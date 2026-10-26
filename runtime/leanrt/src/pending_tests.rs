//! Order tests for the pending stack (`pending`, Reussir's drop stack since
//! entry 23-m), ported from local Reussir patch 13-c's `reussir_rt::drop`
//! tests (02-c at Reussir 7954a367).
//!
//! A scenario is a forest of cells and steps: freeing a cell (its release
//! function) records it, checks that its header is as written (the stack
//! never writes a cell), and does its actions in order:
//! defer a child cell, release a child cell at once (as
//! Reussir's glue frees a record member itself), push a child step
//! ([`defer_step`], [`run_step`]), or call [`drain`]. A step does its
//! actions as leanrt's array frees do: one after another until one pushes
//! work (then it answers "not done") or none is left. Each root is freed as
//! leanrt frees a box's payload: deferred, then drained, so every release
//! runs inside the drain (the stack is empty whenever no drain runs).
//! Random scenarios are run through the stack and through a model with one
//! stack entry per pending cell or step, last pushed first; the orders must
//! agree. The traces (with the [`depth`] and [`releasing`] seen at every
//! event, which show how cells were grouped into runs) are also hashed, so
//! that two implementations can be compared exactly (`digest`, run with
//! `--nocapture`).

use super::*;
use std::cell::{Cell, RefCell};
use std::hash::{DefaultHasher, Hash, Hasher};

thread_local! {
    /// What the end work saw (`releasing`, `depth`) each time it ran on this
    /// thread (`end_work`).
    pub(super) static END_SEEN: RefCell<Vec<(bool, usize)>> = const { RefCell::new(Vec::new()) };
}

fn take_end_seen() -> Vec<(bool, usize)> {
    END_SEEN.with(|s| std::mem::take(&mut *s.borrow_mut()))
}

#[derive(Clone, Copy, Debug)]
enum Action {
    Defer { child: usize },
    Inline { child: usize },
    Step { child: usize },
    RunStep { child: usize },
    Drain,
}

struct Node {
    /// The release function (index in [`releases`]); unused for a step.
    k: usize,
    /// An immediate: a pointer with a nonzero top byte, never dereferenced.
    imm: bool,
    /// The header's second word as initialized (the low half is the tag).
    word: u32,
    actions: Vec<Action>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Ev {
    Release { node: usize, k: usize },
    Step { node: usize, done: usize },
}

struct World {
    nodes: Vec<Node>,
    base: *mut [u64; 2],
    slot: Vec<usize>,
    progress: Vec<usize>,
    released: Vec<bool>,
    trace: Vec<Ev>,
    /// Every event with the depth and activity the stack reported then.
    seen: Vec<(Ev, usize, bool)>,
}

thread_local! {
    static WORLD: RefCell<Option<World>> = const { RefCell::new(None) };
}

fn with_world<R>(f: impl FnOnce(&mut World) -> R) -> R {
    WORLD.with(|w| f(w.borrow_mut().as_mut().expect("no scenario")))
}

unsafe extern "C" fn rel<const K: usize>(p: *mut u8) {
    on_release(p, K)
}

macro_rules! tens {
    ($v:ident; $($h:literal)*) => {
        $($v.extend_from_slice(&[
            rel::<{ $h * 10 }> as Release, rel::<{ $h * 10 + 1 }>,
            rel::<{ $h * 10 + 2 }>, rel::<{ $h * 10 + 3 }>,
            rel::<{ $h * 10 + 4 }>, rel::<{ $h * 10 + 5 }>,
            rel::<{ $h * 10 + 6 }>, rel::<{ $h * 10 + 7 }>,
            rel::<{ $h * 10 + 8 }>, rel::<{ $h * 10 + 9 }>,
        ]);)*
    };
}

/// 300 distinct release functions.
fn releases() -> Vec<Release> {
    let mut v = Vec::new();
    tens!(v; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29);
    v
}

thread_local! {
    static RELEASES_FNS: Vec<Release> = releases();
}

fn release_fn(k: usize) -> Release {
    RELEASES_FNS.with(|r| r[k])
}

fn ptr_of(w: &World, id: usize) -> *mut u8 {
    if w.nodes[id].imm {
        // Never dereferenced: no provenance.
        std::ptr::without_provenance_mut((1usize << 56) | (id << 3))
    } else {
        unsafe { w.base.add(w.slot[id]).cast::<u8>() }
    }
}

fn record(w: &mut World, ev: Ev) {
    w.trace.push(ev);
    w.seen.push((ev, depth(), releasing()));
}

fn on_release(p: *mut u8, k: usize) {
    let id = if (p as usize) >> 56 != 0 {
        ((p as usize) & ((1 << 56) - 1)) >> 3
    } else {
        let words = p.cast::<u32>();
        let (count, word) = unsafe { (words.read(), words.add(1).read()) };
        let id = unsafe { p.cast::<u64>().add(1).read() } as usize;
        let orig = with_world(|w| w.nodes[id].word);
        assert_eq!(count, 1, "count of cell {id} written");
        assert_eq!(word, orig, "second word of cell {id} written");
        id
    };
    assert!(releasing(), "cell {id} released outside a drain");
    let actions = with_world(|w| {
        assert!(!w.released[id], "cell {id} released twice");
        w.released[id] = true;
        record(w, Ev::Release { node: id, k });
        w.nodes[id].actions.clone()
    });
    for a in actions {
        perform(a);
    }
}

fn perform(a: Action) {
    match a {
        Action::Defer { child } => {
            let (p, k) = with_world(|w| (ptr_of(w, child), w.nodes[child].k));
            unsafe { defer_cell(p, release_fn(k)) }
        }
        Action::Inline { child } => {
            let (p, k) = with_world(|w| (ptr_of(w, child), w.nodes[child].k));
            unsafe { release_fn(k)(p) }
        }
        Action::Step { child } => defer_step(child, step_fn),
        Action::RunStep { child } => run_step(child, step_fn),
        Action::Drain => drain(),
    }
}

unsafe extern "C" fn step_fn(id: usize) -> bool {
    let actions = with_world(|w| {
        let done = w.progress[id];
        record(w, Ev::Step { node: id, done });
        w.nodes[id].actions.clone()
    });
    let before = depth();
    loop {
        let done = with_world(|w| w.progress[id]);
        if done == actions.len() {
            return true;
        }
        perform(actions[done]);
        with_world(|w| w.progress[id] = done + 1);
        if done + 1 == actions.len() {
            return true;
        }
        if depth() != before {
            return false;
        }
    }
}

/// The reference: one entry per pending cell or step, last pushed first.
struct Model<'a> {
    nodes: &'a [Node],
    stack: Vec<(bool, usize)>,
    draining: bool,
    progress: Vec<usize>,
    trace: Vec<Ev>,
}

impl Model<'_> {
    fn release(&mut self, id: usize) {
        self.trace.push(Ev::Release { node: id, k: self.nodes[id].k });
        for &a in &self.nodes[id].actions {
            self.perform(a);
        }
    }

    fn perform(&mut self, a: Action) {
        match a {
            Action::Defer { child, .. } => self.stack.push((false, child)),
            Action::Inline { child } => self.release(child),
            Action::Step { child } => self.stack.push((true, child)),
            Action::RunStep { child } => {
                self.stack.push((true, child));
                self.drain();
            }
            Action::Drain => self.drain(),
        }
    }

    fn drain(&mut self) {
        if self.draining {
            return;
        }
        self.draining = true;
        while let Some(&(is_step, id)) = self.stack.last() {
            if !is_step {
                self.stack.pop();
                self.release(id);
            } else {
                let index = self.stack.len() - 1;
                if self.step(id) {
                    self.stack.remove(index);
                }
            }
        }
        self.draining = false;
    }

    fn step(&mut self, id: usize) -> bool {
        self.trace.push(Ev::Step { node: id, done: self.progress[id] });
        let before = self.stack.len();
        let n = self.nodes[id].actions.len();
        loop {
            let done = self.progress[id];
            if done == n {
                return true;
            }
            self.perform(self.nodes[id].actions[done]);
            self.progress[id] = done + 1;
            if done + 1 == n {
                return true;
            }
            if self.stack.len() != before {
                return false;
            }
        }
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

/// A random forest: the roots, then all nodes (index = id).
fn scenario(seed: u64, budget: usize) -> (Vec<usize>, Vec<Node>) {
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let kinds = [1, 3, 40, 300][rng.below(4)];
    let imm_pct = [0, 5, 30][rng.below(3)];
    let mut nodes: Vec<Node> = Vec::new();
    let mut is_step: Vec<bool> = Vec::new();
    let mut new_node = |rng: &mut Rng, nodes: &mut Vec<Node>, step: bool| {
        nodes.push(Node {
            k: if step { 0 } else { rng.below(kinds) },
            imm: !step && rng.chance(imm_pct),
            word: (rng.next() as u32 & 0xffff) | if rng.chance(50) { (rng.next() as u32) << 16 } else { 0 },
            actions: Vec::new(),
        });
        is_step.push(step);
        nodes.len() - 1
    };
    let mut roots = Vec::new();
    let mut queue = std::collections::VecDeque::new();
    while nodes.len() < budget {
        let r = new_node(&mut rng, &mut nodes, false);
        roots.push(r);
        queue.push_back(r);
        while let Some(id) = queue.pop_front() {
            let n = if rng.chance(3) { rng.below(300) } else { rng.below(5) };
            for _ in 0..n {
                if nodes.len() >= budget {
                    break;
                }
                let roll = rng.below(100);
                let action = if roll < 70 {
                    let c = new_node(&mut rng, &mut nodes, false);
                    queue.push_back(c);
                    Action::Defer { child: c }
                } else if roll < 80 {
                    let c = new_node(&mut rng, &mut nodes, false);
                    queue.push_back(c);
                    Action::Inline { child: c }
                } else if roll < 90 {
                    let c = new_node(&mut rng, &mut nodes, true);
                    queue.push_back(c);
                    Action::Step { child: c }
                } else if roll < 95 {
                    let c = new_node(&mut rng, &mut nodes, true);
                    queue.push_back(c);
                    Action::RunStep { child: c }
                } else {
                    Action::Drain
                };
                nodes[id].actions.push(action);
            }
        }
    }
    (roots, nodes)
}

/// Cells at the given slots of `arena`, each with its header (count 1, the
/// node's word) and its id; answers the arena's base.
fn fill(arena: &mut [[u64; 2]], nodes: &[Node], slot: &[usize]) -> *mut [u64; 2] {
    let base = arena.as_mut_ptr();
    for (id, node) in nodes.iter().enumerate() {
        unsafe {
            let cell = base.add(slot[id]);
            let words = cell.cast::<u32>();
            words.write(1);
            words.add(1).write(node.word);
            cell.cast::<u64>().add(1).write(id as u64);
        }
    }
    base
}

fn install(nodes: Vec<Node>, base: *mut [u64; 2], slot: Vec<usize>) {
    let n = nodes.len();
    WORLD.with(|w| {
        *w.borrow_mut() = Some(World {
            nodes,
            base,
            slot,
            progress: vec![0; n],
            released: vec![false; n],
            trace: Vec::new(),
            seen: Vec::new(),
        })
    });
}

/// Runs a scenario through the stack and the model; answers the trace
/// digest (events with depth and activity), the number of events, of steps,
/// and the largest depth seen.
fn run_stats(seed: u64, budget: usize) -> (u64, usize, usize, usize) {
    let (roots, nodes) = scenario(seed, budget);
    let n = nodes.len();
    let mut rng = Rng(seed ^ 0x5555);
    // Cells at random slots of one arena.
    let mut slot: Vec<usize> = (0..2 * n).collect();
    for i in (1..slot.len()).rev() {
        slot.swap(i, rng.below(i + 1));
    }
    slot.truncate(n);
    let mut arena = vec![[0u64; 2]; 2 * n];
    let base = fill(&mut arena, &nodes, &slot);
    let mut model = Model { nodes: &nodes, stack: Vec::new(), draining: false, progress: vec![0; n], trace: Vec::new() };
    for &r in &roots {
        model.stack.push((false, r));
        model.drain();
    }
    let expected = model.trace;
    let ks: Vec<usize> = nodes.iter().map(|node| node.k).collect();
    install(nodes, base, slot);
    assert!(!releasing());
    assert_eq!(depth(), 0);
    for &r in &roots {
        let p = with_world(|w| ptr_of(w, r));
        unsafe { defer_cell(p, release_fn(ks[r])) };
        drain();
        assert!(!releasing());
        assert_eq!(depth(), 0);
    }
    let world = WORLD.with(|w| w.borrow_mut().take().unwrap());
    drop(arena);
    assert_eq!(world.trace.len(), expected.len(), "seed {seed}: event count");
    for (i, (got, want)) in world.trace.iter().zip(&expected).enumerate() {
        assert_eq!(got, want, "seed {seed}: event {i}");
    }
    let mut h = DefaultHasher::new();
    world.seen.hash(&mut h);
    let steps = world.trace.iter().filter(|e| matches!(e, Ev::Step { .. })).count();
    let deepest = world.seen.iter().map(|s| s.1).max().unwrap_or(0);
    (h.finish(), world.trace.len(), steps, deepest)
}

fn seeds() -> (u64, usize) {
    if cfg!(miri) {
        (4, 60)
    } else {
        (400, 3000)
    }
}

#[test]
fn random_drops_match_the_model() {
    let (count, budget) = seeds();
    for seed in 0..count {
        run_stats(seed, budget);
    }
    assert!(take_end_seen().is_empty(), "no release asked for end work");
}

/// Prints the trace digests (compare two implementations' outputs).
#[test]
fn digest() {
    let (count, budget) = seeds();
    let mut all = DefaultHasher::new();
    for seed in 0..count {
        let (d, events, steps, deepest) = run_stats(seed, budget);
        d.hash(&mut all);
        println!("pending-digest seed {seed}: {d:016x} ({events} events, {steps} steps, depth <= {deepest})");
    }
    println!("pending-digest all: {:016x}", all.finish());
}

thread_local! {
    /// The ids that `release_box` saw on this thread.
    static BOXES_SEEN: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    /// The cells `step_defer_boxes` defers, in order.
    static TO_DEFER: RefCell<Vec<*mut u8>> = const { RefCell::new(Vec::new()) };
    /// The depth `step_defer_boxes` saw after its deferrals.
    static DEPTH_AFTER: Cell<usize> = const { Cell::new(0) };
}

/// Reads a boxed cell's id, then frees the box.
unsafe extern "C" fn release_box(p: *mut u8) {
    let id = unsafe { p.cast::<u64>().add(1).read() };
    BOXES_SEEN.with(|s| s.borrow_mut().push(id));
    drop(unsafe { Box::from_raw(p.cast::<[u64; 2]>()) });
}

/// A cell in a box of its own: header (count 1, padding 0), then `id`.
fn boxed_cell(id: u64) -> *mut u8 {
    Box::into_raw(Box::new([1u64, id])).cast::<u8>()
}

/// A step (inside the drain) that defers the cells in `TO_DEFER` and notes
/// the depth after. The release function is made a pointer once, as
/// leanrt's callers read it from a table: two pointers to one function may
/// differ (Miri gives them different addresses), and a cell whose pointer
/// differs starts a run of its own.
unsafe extern "C" fn step_defer_boxes(_: usize) -> bool {
    let release = release_box as Release;
    for p in TO_DEFER.with(|t| std::mem::take(&mut *t.borrow_mut())) {
        unsafe { defer_cell(p, release) };
    }
    DEPTH_AFTER.with(|d| d.set(depth()));
    true
}

/// Three cells in separate allocations, deferred with one release
/// function, form one run, as every program's cells do: the cells vector
/// keeps the earlier two. The drain releases them last first, each after
/// the later ones are freed. Under Miri this checks that the pointers kept
/// in the vector may still access their cells (the other tests take all
/// their cells from one allocation).
#[test]
fn cells_in_separate_boxes() {
    TO_DEFER.with(|t| *t.borrow_mut() = vec![boxed_cell(10), boxed_cell(20), boxed_cell(30)]);
    run_step(0, step_defer_boxes);
    assert_eq!(DEPTH_AFTER.with(|d| d.get()), 2, "the step, and one run");
    assert_eq!(depth(), 0);
    assert_eq!(BOXES_SEEN.with(|s| s.borrow_mut().split_off(0)), vec![30, 20, 10]);
}

thread_local! {
    /// The release function of each cell `step_runs` defers (cell `i` with
    /// `RUN_KS[i]`).
    static RUN_KS: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

/// A step that defers cells 0..n, cell `i` with release function
/// `RUN_KS[i]`, and notes the depth after.
unsafe extern "C" fn step_runs(_: usize) -> bool {
    let n = RUN_KS.with(|r| r.borrow().len());
    for c in 0..n {
        perform(Action::Defer { child: c });
    }
    DEPTH_AFTER.with(|d| d.set(depth()));
    true
}

/// Defers cells with the release functions `ks` in one step; answers the
/// depth after (the step and one entry per run), and checks that they are
/// released last first.
fn runs_of(ks: Vec<usize>) -> usize {
    let n = ks.len();
    let nodes: Vec<Node> = ks.iter().map(|&k| Node { k, imm: false, word: 7, actions: Vec::new() }).collect();
    RUN_KS.with(|r| *r.borrow_mut() = ks);
    let mut arena = vec![[0u64; 2]; n];
    let slot: Vec<usize> = (0..n).collect();
    let base = fill(&mut arena, &nodes, &slot);
    install(nodes, base, slot);
    run_step(0, step_runs);
    assert_eq!(depth(), 0);
    let world = WORLD.with(|w| w.borrow_mut().take().unwrap());
    drop(arena);
    let order: Vec<usize> = world
        .trace
        .iter()
        .map(|e| match *e {
            Ev::Release { node, .. } => node,
            Ev::Step { .. } => unreachable!(),
        })
        .collect();
    let want: Vec<usize> = (0..n).rev().collect();
    assert_eq!(order, want);
    DEPTH_AFTER.with(|d| d.get())
}

/// A run holds cells with one release function: 300 cells with one
/// function are one entry, with three functions in blocks three entries,
/// with two functions in turn one entry each.
#[test]
fn a_run_has_one_release_function() {
    assert_eq!(runs_of(vec![5; 300]), 2);
    assert_eq!(runs_of((0..300).map(|i| i / 100).collect()), 1 + 3);
    assert_eq!(runs_of((0..300).map(|i| i % 2).collect()), 1 + 300);
}

unsafe extern "C" fn release_nothing(_: *mut u8) {}

/// Asks for the end work.
unsafe extern "C" fn release_wanting(_: *mut u8) {
    want_end_work();
}

unsafe extern "C" fn leaf_step(_: usize) -> bool {
    true
}

/// A step that asks for the end work, starts work inside the drain (only
/// pushed) and a nested drain (returns at once).
unsafe extern "C" fn nesting_step(_: usize) -> bool {
    want_end_work();
    run_step(0, leaf_step);
    drain();
    true
}

/// The end work runs once per drain that asked for it, after it is over
/// (not releasing, nothing pending), through the general loop and through
/// the one-cell path; never inside a drain, nor for a drain with nothing to
/// do or one that did not ask (local Reussir patch 40-a's test, 09-a at
/// Reussir 7954a367, for the end work that replaced its hook).
#[test]
fn end_work_runs_after_the_outermost_drain() {
    take_end_seen();
    run_step(0, nesting_step);
    drain();
    let mut cell = [1u64, 0];
    unsafe {
        defer_cell(cell.as_mut_ptr().cast(), release_wanting);
        drain();
        defer_cell(cell.as_mut_ptr().cast(), release_nothing);
        drain();
    }
    run_step(0, leaf_step);
    assert_eq!(take_end_seen(), vec![(false, 0), (false, 0)]);
}

thread_local! {
    /// The cells of `chain` (an arena) and how many `release_chain` freed.
    static CHAIN: RefCell<(*mut [u64; 2], usize, usize)> = const { RefCell::new((std::ptr::null_mut(), 0, 0)) };
}

/// Releases a cell of the chain: defers the next one.
unsafe extern "C" fn release_chain(p: *mut u8) {
    let id = unsafe { p.cast::<u64>().add(1).read() } as usize;
    let next = CHAIN.with(|c| {
        let mut c = c.borrow_mut();
        assert_eq!(id, c.2, "chain order");
        c.2 += 1;
        if id + 1 < c.1 {
            Some(unsafe { c.0.add(id + 1).cast::<u8>() })
        } else {
            None
        }
    });
    if let Some(q) = next {
        unsafe { defer_cell(q, release_chain) };
    }
}

/// Releases a cell of a list freed whole: nothing to do but count.
unsafe extern "C" fn release_head(p: *mut u8) {
    let id = unsafe { p.cast::<u64>().add(1).read() } as usize;
    CHAIN.with(|c| {
        let mut c = c.borrow_mut();
        assert_eq!(id, c.1 - 1 - c.2, "list order");
        c.2 += 1;
    });
}

/// A step that defers every cell of the arena, as Reussir's glue frees the
/// heads of a long list inside a free: one run.
unsafe extern "C" fn step_list(_: usize) -> bool {
    let (base, n) = CHAIN.with(|c| (c.borrow().0, c.borrow().1));
    for i in 0..n {
        unsafe { defer_cell(base.add(i).cast::<u8>(), release_head) };
    }
    assert_eq!(depth(), 2, "the step and one run");
    true
}

/// 10^6 cells: a chain whose releases each defer the next, on a 256 KiB
/// stack (no recursion), and a list freed whole, whose 10^6 cells form one
/// run (one entry; the cells vector holds the other cells; reussir-rt's own
/// tests check that both vectors shrink back after the drain).
#[test]
#[cfg(not(miri))]
fn a_million_cells() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let n = 1_000_000;
            let mut arena = vec![[1u64, 0]; n];
            for (i, c) in arena.iter_mut().enumerate() {
                c[1] = i as u64;
            }
            let base = arena.as_mut_ptr();
            CHAIN.with(|c| *c.borrow_mut() = (base, n, 0));
            unsafe { defer_cell(base.cast::<u8>(), release_chain) };
            drain();
            assert_eq!(CHAIN.with(|c| c.borrow().2), n);
            CHAIN.with(|c| *c.borrow_mut() = (base, n, 0));
            run_step(0, step_list);
            assert_eq!(CHAIN.with(|c| c.borrow().2), n);
            assert!(!releasing());
            assert_eq!(depth(), 0);
            assert!(arena.iter().all(|c| c[0] == 1), "no count written");
        })
        .unwrap()
        .join()
        .unwrap();
}

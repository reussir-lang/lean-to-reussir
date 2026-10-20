//! A map from nonzero addresses to `u32`s: open addressing with linear
//! probing in a power-of-two table at most half full, a zero key marking a
//! free slot, deletion by backward shift (no tombstones). For the task
//! glue's map from a task's cell to its entry (`task`): the runtime keeps
//! nothing in the cell itself.

use std::mem::replace;

pub(crate) struct AddrMap {
    slots: Vec<(usize, u32)>,
    len: usize,
}

impl AddrMap {
    pub(crate) const fn new() -> Self {
        AddrMap { slots: Vec::new(), len: 0 }
    }

    /// Whether the map is empty (one load: the callers skip the probe).
    #[inline(always)]
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The slot where `k`'s probe starts: a multiplication, its high half
    /// folded into the low one (the low bits of an address are zeros).
    #[inline(always)]
    fn start(k: usize, mask: usize) -> usize {
        let h = (k as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        (h ^ (h >> 32)) as usize & mask
    }

    /// The slot holding `k`, if it is in the map.
    #[inline]
    fn index(&self, k: usize) -> Option<usize> {
        if self.len == 0 {
            return None;
        }
        let mask = self.slots.len() - 1;
        let mut i = Self::start(k, mask);
        loop {
            match self.slots[i].0 {
                0 => return None,
                s if s == k => return Some(i),
                _ => i = (i + 1) & mask,
            }
        }
    }

    #[inline]
    pub(crate) fn get(&self, k: usize) -> Option<u32> {
        self.index(k).map(|i| self.slots[i].1)
    }

    /// Map `k` (nonzero) to `v`, replacing what it was mapped to.
    pub(crate) fn insert(&mut self, k: usize, v: u32) {
        debug_assert!(k != 0, "leanrt: a zero address in an AddrMap");
        if 2 * (self.len + 1) > self.slots.len() {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut i = Self::start(k, mask);
        loop {
            let s = self.slots[i].0;
            if s == k {
                self.slots[i].1 = v;
                return;
            }
            if s == 0 {
                self.slots[i] = (k, v);
                self.len += 1;
                return;
            }
            i = (i + 1) & mask;
        }
    }

    /// Remove `k`, if it is in the map. The entries after it in its run move
    /// back where their probe would find them sooner.
    pub(crate) fn remove(&mut self, k: usize) {
        let Some(mut i) = self.index(k) else { return };
        let mask = self.slots.len() - 1;
        self.slots[i] = (0, 0);
        self.len -= 1;
        let mut j = i;
        loop {
            j = (j + 1) & mask;
            let (key, _) = self.slots[j];
            if key == 0 {
                return;
            }
            let home = Self::start(key, mask);
            // The entry at `j` stays if its probe start lies cyclically in
            // (i, j]: a probe for it never passes `i`.
            let stays = if i <= j { i < home && home <= j } else { i < home || home <= j };
            if !stays {
                self.slots[i] = self.slots[j];
                self.slots[j] = (0, 0);
                i = j;
            }
        }
    }

    /// Double the table (at first 64 slots) and put the entries back.
    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        let n = (self.slots.len() * 2).max(64);
        let old = replace(&mut self.slots, vec![(0, 0); n]);
        let mask = n - 1;
        for (k, v) in old.into_iter().filter(|e| e.0 != 0) {
            let mut i = Self::start(k, mask);
            while self.slots[i].0 != 0 {
                i = (i + 1) & mask;
            }
            self.slots[i] = (k, v);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Inserts, replacements and removals against a model, through the
    /// table's growth and with keys whose probes collide.
    #[test]
    fn matches_a_model() {
        let mut m = AddrMap::new();
        let mut model = std::collections::HashMap::new();
        let mut x: u64 = 0x2545_f491_4f6c_dd1d;
        for step in 0..20_000u32 {
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            let r = x.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            // Few distinct keys, so that removals hit and runs form.
            let k = (((r >> 8) % 300) as usize + 1) * 16;
            if r & 3 == 0 {
                m.remove(k);
                model.remove(&k);
            } else {
                m.insert(k, step);
                model.insert(k, step);
            }
            if step % 97 == 0 {
                for kk in (16..=300 * 16).step_by(16) {
                    assert_eq!(m.get(kk), model.get(&kk).copied(), "key {kk} at step {step}");
                }
                assert_eq!(m.len, model.len());
            }
        }
        assert!(!m.is_empty() || model.is_empty());
    }

    /// Runs that wrap from the table's last slot to its first, and removals
    /// whose backward shift moves entries across the wrap or leaves them.
    #[test]
    fn wrapping_runs() {
        // Keys whose probes start at slot `s` of the first, 64-slot table.
        let home = |s: usize| -> Vec<usize> {
            (1..).map(|n| n * 16).filter(|&k| AddrMap::start(k, 63) == s).take(3).collect()
        };
        let (a, b, c) = (home(62), home(63), home(0));
        let all: Vec<usize> = a.iter().chain(&b).chain(&c).copied().collect();
        let scenarios: [(&[usize], usize); 3] = [
            // 62, 63, then 0, 1, 2: removing 63 moves slots 0, 1, 2 back.
            (&[a[0], a[1], b[0], c[0], a[2]], a[1]),
            // Removing 63 leaves slot 0, whose probe starts there.
            (&[a[0], b[0], c[0]], b[0]),
            // Removing 62 leaves 63 and slot 0, whose probe starts at 63.
            (&[a[0], b[0], b[1]], a[0]),
        ];
        for (n, (keys, gone)) in scenarios.iter().enumerate() {
            let mut m = AddrMap::new();
            let mut model = std::collections::HashMap::new();
            let check = |m: &AddrMap, model: &std::collections::HashMap<usize, u32>| {
                for &k in &all {
                    assert_eq!(m.get(k), model.get(&k).copied(), "key {k} in scenario {n}");
                }
            };
            for (v, &k) in keys.iter().enumerate() {
                m.insert(k, v as u32);
                model.insert(k, v as u32);
            }
            assert_eq!(m.slots.len(), 64);
            check(&m, &model);
            m.remove(*gone);
            model.remove(gone);
            check(&m, &model);
            m.insert(*gone, 99);
            model.insert(*gone, 99);
            check(&m, &model);
            for &k in keys.iter() {
                m.remove(k);
                model.remove(&k);
                check(&m, &model);
            }
            assert!(m.is_empty());
        }
    }
}

// Issue 23: the driver of bug23-deep-free.rr (see there).
//   deep N SHAPE   SHAPE 0: left-deep tree, 1: right-deep tree, 2: 64-arm
//                  enum chain, 3: compositions
// Builds one value of N levels (default 1000000) and prints `grew K`: how
// much peak RSS grew, in KiB, during its free, on a 256 KiB stack. One shape
// per process: the peak is a high-water mark, so a later free that needs
// less than an earlier one would show no growth.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
extern void *wl_leaf(void);
extern void *wl_left(void *, uint64_t);
extern void *wl_right(void *, uint64_t);
extern uint64_t wl_tree_consume(void *);
extern void *wl_end(void);
extern void *wl_first(void *, uint64_t);
extern void *wl_last(void *, uint64_t);
extern uint64_t wl_chain_consume(void *);
extern void *wl_id(void);
extern void *wl_comp(void *, void *);
extern uint64_t wl_fn_consume(void *);

static long peak_kib(void) {
  struct rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  return usage.ru_maxrss;
}

static long drop(uint64_t (*consume)(void *), void *value) {
  long before = peak_kib();
  if (consume(value) != 1) abort();
  return peak_kib() - before;
}

int main(int argc, char **argv) {
  struct rlimit limit;
  getrlimit(RLIMIT_STACK, &limit);
  limit.rlim_cur = 256 * 1024;
  setrlimit(RLIMIT_STACK, &limit);
  uint64_t depth = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000;
  int shape = argc > 2 ? atoi(argv[2]) : 0;
  long grown;
  if (shape == 0 || shape == 1) {
    void *tree = wl_leaf();
    for (uint64_t i = 0; i < depth; ++i)
      tree = shape == 0 ? wl_left(tree, i) : wl_right(tree, i);
    grown = drop(wl_tree_consume, tree);
  } else if (shape == 2) {
    void *chain = wl_end();
    for (uint64_t i = 0; i < depth; ++i)
      chain = i % 2 ? wl_first(chain, i) : wl_last(chain, i);
    grown = drop(wl_chain_consume, chain);
  } else {
    void *fn = wl_id();
    for (uint64_t i = 0; i < depth; ++i)
      fn = i % 2 ? wl_comp(fn, wl_id()) : wl_comp(wl_id(), fn);
    grown = drop(wl_fn_consume, fn);
  }
  printf("grew %ld\n", grown);
  return 0;
}

/* Allocation counter for the executables of native Lean and of lean2rr.
 *
 * Both link mimalloc statically: native Lean's runtime (libleanrt) and
 * lean2rr's (Reussir's runtime crate reussir-rt, whose Rust global allocator
 * also goes to mimalloc) call its entry points from other object files.
 * Linked with `-Wl,--wrap=SYMBOL` for each entry point below (the flags are
 * in alloccount.sh), every such call goes through the `__wrap_` function
 * here, which counts it and calls the real one (`__real_`). Calls inside
 * mimalloc itself are not wrapped, so each allocation the program asks for
 * is counted once. At exit (a destructor) the counter prints one line to
 * standard error:
 *
 *     alloccount: allocs A reallocs R bytes B
 *
 * A counts the allocations (a realloc of NULL is one), R the reallocations
 * of an existing block, B the bytes requested by both (the new size of a
 * reallocation): a copy of an array is one allocation of many bytes, so a
 * program that copies an array of n elements n times shows in B, not in A.
 * The counts include what the runtime allocates before `main` (its
 * startup) and after it: compare two runs of one build, not the absolute
 * numbers of the two builds.
 *
 * Limits: when the environment sets ALLOCCOUNT_MAX_ALLOCS (allocations and
 * reallocations together) or ALLOCCOUNT_MAX_BYTES (bytes requested), a run
 * that goes past either stops at once: the counter prints
 *
 *     alloccount: stopped at the limit: allocs A reallocs R bytes B
 *
 * and exits with status 125 (no destructor runs, so no count line). The
 * bytes requested bound the memory a run can hold, so a blowup (an
 * exponential copy of a shared value) stops after a few seconds instead of
 * filling the machine's memory. tests/runtime/alloc-check.sh sets both.
 *
 * Portability: ELF linkers with `--wrap` (GNU ld, gold, lld), and the
 * mimalloc entry points listed here. A program whose allocator is not a
 * statically linked mimalloc would count nothing; tests/runtime/alloc-check.sh
 * fails when a run prints no count line. */
#include <stdatomic.h>
#include <stddef.h>

/* Only the compiler's own headers: Lean's C compiler (leanc) has no C
 * library headers, so the one C library function used is declared here. */
long write(int fd, const void *buf, size_t n);
char *getenv(const char *name);
void _exit(int status);

static _Atomic unsigned long long n_alloc, n_realloc, n_bytes;
/* 0: no limit. Set by the constructor below, before `main`; allocations
 * made before it runs are counted but not checked. */
static unsigned long long max_allocs, max_bytes;
static _Atomic int stopped;

static char *put_str(char *p, const char *s) {
  while (*s) *p++ = *s++;
  return p;
}

static char *put_num(char *p, unsigned long long v) {
  char tmp[24];
  int n = 0;
  do { tmp[n++] = (char)('0' + v % 10); v /= 10; } while (v);
  while (n) *p++ = tmp[--n];
  return p;
}

static void put_counts(const char *prefix) {
  char buf[160], *p = buf;
  p = put_str(p, prefix);
  p = put_num(p, atomic_load(&n_alloc));
  p = put_str(p, " reallocs ");
  p = put_num(p, atomic_load(&n_realloc));
  p = put_str(p, " bytes ");
  p = put_num(p, atomic_load(&n_bytes));
  *p++ = '\n';
  (void)write(2, buf, (size_t)(p - buf));
}

__attribute__((destructor)) static void alloccount_report(void) {
  put_counts("alloccount: allocs ");
}

/* A decimal number from the environment, 0 when unset or not a number. */
static unsigned long long env_num(const char *name) {
  const char *s = getenv(name);
  unsigned long long v = 0;
  if (!s) return 0;
  for (; *s >= '0' && *s <= '9'; s++) v = v * 10 + (unsigned long long)(*s - '0');
  return *s ? 0 : v;
}

__attribute__((constructor)) static void alloccount_limits(void) {
  max_allocs = env_num("ALLOCCOUNT_MAX_ALLOCS");
  max_bytes = env_num("ALLOCCOUNT_MAX_BYTES");
}

static void count(_Atomic unsigned long long *c, size_t bytes) {
  atomic_fetch_add_explicit(c, 1, memory_order_relaxed);
  unsigned long long b = atomic_fetch_add_explicit(&n_bytes, bytes, memory_order_relaxed) + bytes;
  if ((max_allocs && atomic_load_explicit(&n_alloc, memory_order_relaxed) +
                         atomic_load_explicit(&n_realloc, memory_order_relaxed) > max_allocs) ||
      (max_bytes && b > max_bytes)) {
    if (!atomic_exchange(&stopped, 1)) put_counts("alloccount: stopped at the limit: allocs ");
    _exit(125);
  }
}

/* NAME(size): one block of `size` bytes. */
#define W_SIZE(name)              \
  void *__real_##name(size_t);    \
  void *__wrap_##name(size_t s) { \
    count(&n_alloc, s);           \
    return __real_##name(s);      \
  }
W_SIZE(mi_malloc)
W_SIZE(mi_malloc_small)
W_SIZE(mi_zalloc)
W_SIZE(mi_zalloc_small)

/* NAME(count, size): `count` elements of `size` bytes. */
#define W_COUNT(name)                       \
  void *__real_##name(size_t, size_t);      \
  void *__wrap_##name(size_t n, size_t s) { \
    count(&n_alloc, n * s);                 \
    return __real_##name(n, s);             \
  }
W_COUNT(mi_calloc)
W_COUNT(mi_mallocn)

/* NAME(size, alignment). */
#define W_ALIGNED(name)                     \
  void *__real_##name(size_t, size_t);      \
  void *__wrap_##name(size_t s, size_t a) { \
    count(&n_alloc, s);                     \
    return __real_##name(s, a);             \
  }
W_ALIGNED(mi_malloc_aligned)
W_ALIGNED(mi_zalloc_aligned)

void *__real_mi_realloc(void *, size_t);
void *__wrap_mi_realloc(void *p, size_t s) {
  count(p ? &n_realloc : &n_alloc, s);
  return __real_mi_realloc(p, s);
}

void *__real_mi_realloc_aligned(void *, size_t, size_t);
void *__wrap_mi_realloc_aligned(void *p, size_t s, size_t a) {
  count(p ? &n_realloc : &n_alloc, s);
  return __real_mi_realloc_aligned(p, s, a);
}

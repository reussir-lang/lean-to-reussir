/* Allocation tracker for the LAny probe: linked with -Wl,--wrap=SYM for
 * mimalloc's allocation entry points and mi_free (as tests/runtime/alloccount
 * of branch tests-repr, plus the frees). Keeps the set of live blocks (open
 * addressing, linear probing, backward-shift deletion), so a program can ask
 * how many blocks are live (`alloclive_live`), how many allocations and frees
 * happened (`alloclive_allocs`, `alloclive_frees`), and how many frees named
 * a block that was not live (`alloclive_bad_frees`: a double free, or a free
 * of a block allocated before tracking or inside mimalloc). Prints a summary
 * at exit. */
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>

long write(int fd, const void *buf, size_t n);
void *mmap(void *addr, size_t len, int prot, int flags, int fd, long off);

#define BITS 24
#define SIZE ((size_t)1 << BITS)
static uintptr_t *table; /* 0 = empty */
static atomic_flag lock = ATOMIC_FLAG_INIT;
static unsigned long long n_live, n_alloc, n_free, n_bad;

static void lk(void) { while (atomic_flag_test_and_set_explicit(&lock, memory_order_acquire)) {} }
static void ul(void) { atomic_flag_clear_explicit(&lock, memory_order_release); }

static size_t slot(uintptr_t p) { return (size_t)((p >> 3) * 0x9e3779b97f4a7c15ull >> (64 - BITS)); }

static void ensure(void) {
  if (!table) {
    /* PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS (Linux values) */
    table = mmap(0, SIZE * sizeof(uintptr_t), 3, 0x22, -1, 0);
  }
}

static void add(void *q) {
  if (!q) return;
  uintptr_t p = (uintptr_t)q;
  lk(); ensure();
  size_t i = slot(p);
  while (table[i] && table[i] != p) i = (i + 1) & (SIZE - 1);
  if (!table[i]) { table[i] = p; n_live++; }
  n_alloc++;
  ul();
}

static void del(void *q) {
  if (!q) return;
  uintptr_t p = (uintptr_t)q;
  lk(); ensure();
  n_free++;
  size_t i = slot(p);
  while (table[i] && table[i] != p) i = (i + 1) & (SIZE - 1);
  if (!table[i]) { n_bad++; ul(); return; }
  table[i] = 0; n_live--;
  size_t j = i;
  for (;;) {
    j = (j + 1) & (SIZE - 1);
    if (!table[j]) break;
    size_t k = slot(table[j]);
    /* move table[j] to i if k is cyclically outside (i, j] */
    if ((j > i && (k <= i || k > j)) || (j < i && (k <= i && k > j))) {
      table[i] = table[j]; table[j] = 0; i = j;
    }
  }
  ul();
}

unsigned long long alloclive_live(void) { lk(); unsigned long long v = n_live; ul(); return v; }
unsigned long long alloclive_allocs(void) { lk(); unsigned long long v = n_alloc; ul(); return v; }
unsigned long long alloclive_frees(void) { lk(); unsigned long long v = n_free; ul(); return v; }
unsigned long long alloclive_bad_frees(void) { lk(); unsigned long long v = n_bad; ul(); return v; }

static char *put_str(char *p, const char *s) { while (*s) *p++ = *s++; return p; }
static char *put_num(char *p, unsigned long long v) {
  char tmp[24]; int n = 0;
  do { tmp[n++] = (char)('0' + v % 10); v /= 10; } while (v);
  while (n) *p++ = tmp[--n];
  return p;
}
__attribute__((destructor)) static void report(void) {
  char buf[160], *p = buf;
  p = put_str(p, "alloclive: allocs "); p = put_num(p, n_alloc);
  p = put_str(p, " frees "); p = put_num(p, n_free);
  p = put_str(p, " live "); p = put_num(p, n_live);
  p = put_str(p, " bad_frees "); p = put_num(p, n_bad);
  *p++ = '\n';
  (void)write(2, buf, (size_t)(p - buf));
}

#define W_SIZE(name) void *__real_##name(size_t); \
  void *__wrap_##name(size_t s) { void *r = __real_##name(s); add(r); return r; }
W_SIZE(mi_malloc)
W_SIZE(mi_malloc_small)
W_SIZE(mi_zalloc)
W_SIZE(mi_zalloc_small)
#define W_TWO(name) void *__real_##name(size_t, size_t); \
  void *__wrap_##name(size_t a, size_t b) { void *r = __real_##name(a, b); add(r); return r; }
W_TWO(mi_calloc)
W_TWO(mi_mallocn)
W_TWO(mi_malloc_aligned)
W_TWO(mi_zalloc_aligned)

void *__real_mi_realloc(void *, size_t);
void *__wrap_mi_realloc(void *p, size_t s) {
  void *r = __real_mi_realloc(p, s);
  if (r != p) { if (p && r) del(p); add(r); }
  return r;
}
void *__real_mi_realloc_aligned(void *, size_t, size_t);
void *__wrap_mi_realloc_aligned(void *p, size_t s, size_t a) {
  void *r = __real_mi_realloc_aligned(p, s, a);
  if (r != p) { if (p && r) del(p); add(r); }
  return r;
}
void __real_mi_free(void *);
void __wrap_mi_free(void *p) { del(p); __real_mi_free(p); }

/* Snapshot and difference of the live set (debugging). */
static uintptr_t *snap;
size_t mi_usable_size(const void *p);
void alloclive_mark(void) {
  lk(); ensure();
  if (!snap) snap = mmap(0, SIZE * sizeof(uintptr_t), 3, 0x22, -1, 0);
  for (size_t i = 0; i < SIZE; i++) snap[i] = table[i];
  ul();
}
static int in_set(uintptr_t *t, uintptr_t p) {
  size_t i = slot(p);
  while (t[i] && t[i] != p) i = (i + 1) & (SIZE - 1);
  return t[i] == p;
}
void alloclive_diff(void) {
  lk();
  char buf[200];
  for (size_t i = 0; i < SIZE; i++) {
    uintptr_t p = table[i];
    if (p && !in_set(snap, p)) {
      char *q = buf; q = put_str(q, "  new live block "); q = put_num(q, p);
      q = put_str(q, " size "); q = put_num(q, mi_usable_size((void *)p));
      q = put_str(q, " words "); q = put_num(q, ((unsigned long long *)p)[0]);
      q = put_str(q, " "); q = put_num(q, ((unsigned long long *)p)[1]);
      *q++ = '\n'; (void)write(2, buf, (size_t)(q - buf));
    }
  }
  for (size_t i = 0; i < SIZE; i++) {
    uintptr_t p = snap[i];
    if (p && !in_set(table, p)) {
      char *q = buf; q = put_str(q, "  freed old block "); q = put_num(q, p);
      *q++ = '\n'; (void)write(2, buf, (size_t)(q - buf));
    }
  }
  ul();
}

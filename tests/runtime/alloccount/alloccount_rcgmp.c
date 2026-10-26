/* The heap integers of Reussir's integer runtime, counted for the
 * allocation counter (alloccount.c) in lean2rr's builds only.
 *
 * rcgmp makes and frees each heap `Nat` or `Int` through two hooks that
 * reussir-rt defines, `rcgmp_allocate` and `rcgmp_dealloc`. alloccount.sh's
 * AC_RRC links this object with `-Wl,--wrap=` for both, so every call from
 * rcgmp's runtime goes through the `__wrap_` function here, which counts it
 * and calls the hook (`__real_`). The `__real_` declarations are strong, so
 * a link without the hooks fails instead of calling null. The hooks' object
 * is always loaded, because rustc's symbols.o references
 * `__reussir_allocate`, which reussir-rt defines beside them; this object
 * comes after the runtime's rlib on the link line (rustc puts
 * `-C link-arg` objects last) and loads nothing itself. alloccount.c's
 * destructor prints the count, `alloccount: rcgmp live L`, the integers made
 * less those freed. Native builds link neither this object nor the wraps.
 * Only the compiler's own headers, as alloccount.c. */
#include <stdatomic.h>
#include <stddef.h>

_Atomic long long alloccount_rcgmp_live;

void *__real_rcgmp_allocate(size_t, size_t);
void *__wrap_rcgmp_allocate(size_t s, size_t a) {
  atomic_fetch_add_explicit(&alloccount_rcgmp_live, 1, memory_order_relaxed);
  return __real_rcgmp_allocate(s, a);
}

void __real_rcgmp_dealloc(void *, size_t, size_t);
void __wrap_rcgmp_dealloc(void *p, size_t s, size_t a) {
  atomic_fetch_sub_explicit(&alloccount_rcgmp_live, 1, memory_order_relaxed);
  __real_rcgmp_dealloc(p, s, a);
}

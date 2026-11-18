#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
extern bool fresh_immediate(void), fresh_box(void), after_retains(uint64_t);
int main(void) {
  printf("is_unique(E::A) = %d\n", fresh_immediate());
  printf("is_unique(E::B{1}) = %d\n", fresh_box());
  printf("is_unique(E::A) after 1 retain = %d\n", after_retains(1));
  printf("is_unique(E::A) after 2^32-2 retains in total = %d\n", after_retains(4294967293ull));
  printf("is_unique(E::A) after 2^32-1 retains in total = %d\n", after_retains(1));
  printf("is_unique(E::A) after 2^32 retains in total = %d\n", after_retains(1));
  return 0;
}

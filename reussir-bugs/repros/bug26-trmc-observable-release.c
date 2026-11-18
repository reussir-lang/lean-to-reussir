#include <stdio.h>
const void *live_slot;
extern long reussir_main(void);
extern long reussir_control(void);
int main(void) {
  printf("build %ld control %ld\n", reussir_main(), reussir_control());
  return 0;
}

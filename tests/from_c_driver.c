#include <stdio.h>
#include <stdlib.h>

extern int main0(void);
extern unsigned inc(void * /*gc roots*/, unsigned /*int32*/, unsigned /*int32*/, unsigned /*unit*/);
extern unsigned incPure(void * /*gc roots*/, unsigned /*int32*/, unsigned /*int32*/);
extern unsigned incArea(void * /*gc roots*/, unsigned /*unit*/);

int main () {
printf("Starting initialization\n");
  main0(); // Calls "main" from Habit.  Needed to triggar GC initialization.
printf("Finished initialization\n");
  printf("Monadic:%x\n", inc(NULL,0x40,0x30,0));
  printf("Pure:%x\n", incPure(NULL,0x40,0x30));
  printf("Area:%x\n", incArea(NULL,0x20));
  printf("Area:%x\n", incArea(NULL,0x20));
  printf("Area:%x\n", incArea(NULL,0x20));
  printf("Area:%x\n", incArea(NULL,0x20));
  return 0;
}

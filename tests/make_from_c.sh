../alb -f main from_c.hb -o from_c.fidget -O2 \
   --export=inc,inc --export=incPure,incPure --export=incArea,incArea --print-export-signatures && \
../../../compcert1.11-hasp/ccomp -o from_c.out from_c.fidget from_c_driver.c habit_callbacks.c ../../../compcert1.11-hasp/runtime/gc/cheney.o

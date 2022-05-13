#include <stdint.h>

typedef union any {
  int64_t i;
  union any *p;
  union any (*f)(union any, union any);
} any;

any int_to_any(int i){
  any res = {.i = i};
  return res;
}

any funptr_to_any(any (*f)(any, any)){
  any res = {.f = f};
  return res;
}

any ptr_to_any(any *p){
  any res = {.p = p};
  return res;
}

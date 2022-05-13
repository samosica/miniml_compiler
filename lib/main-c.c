#include <stdio.h>
#include "any.h"

extern any _toplevel();

int main() {
  printf("%ld\n", _toplevel().i);
  return 0;
}

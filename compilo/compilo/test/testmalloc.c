#include <stdlib.h>
#include <stdio.h>

long* f(){
  long* i = (long*)malloc(16);
  *i = 4;
  *(i+1) =42;
  return i;
}

int main(){
  long *i= f();
  printf("i:%ld, i+1:%ld", *i, *(i+1));
  free(i);
}

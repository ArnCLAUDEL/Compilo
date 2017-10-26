#include <stdio.h>

void swap(long* a, long* b){
  long t;
  t= *a;
  *a=*b;
  *b=t;
}


int main(){
  long x;
  long y;
  x=54;
  y=2;
  swap(&x,&y);
  printf("(%ld,%ld)", x, y);
  return x;
}
  

#include <stdlib.h>

long* fc(long x){
  long* p;
  p = malloc(8);
  *p=x;
  return p;
}


void d(long* p){
  *p = *p *2;
}

int main(){
  long* p;
  p= fc(3);
  d(p);
  return (*p);
}

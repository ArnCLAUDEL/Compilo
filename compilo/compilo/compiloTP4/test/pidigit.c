#include <stdlib.h>
#include <stdio.h>

long b = 52500; 
long f = 10000;

int main(){
  long* a;
  long c;
  long d;
  long e;
  long g;
  long h;  
  a= malloc(52514*8);
  c= b;
  d= 0;
  h= 0;
  while(b>0){
    d=d%f;
    e=d;
    b=b-1;
    g=b*2;
    while(g>0){
      if(h>0){
	d=d*b+f*a[b];
      }else{
	d=d*b+f*f/5;
      }
      g=g-1;
      a[b]=d%g;
      d=d/g;
      b=b-1;
      g=b*2;
    }
    h=printf("%04ld",e+d/f);
    c= c-14;
    b=c;
  }
}

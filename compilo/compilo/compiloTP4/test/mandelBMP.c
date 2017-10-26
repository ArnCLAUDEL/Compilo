#include "stdio.h"

long f =1000;

long compN(long i, long r){
  long  R, I, b, n;
  I = i;
  R = r;
  n=0;
  b = I * I;
  while (n<256 && R * R + b < 10*f*f){
    I = (2 * R * I)/f + i;
    R = (R * R -b)/f + r;
    b = I * I;
    n=n+1;
  }
  return n;
}

void printInt(long i){
  putchar( i       % 256 );
  putchar((i / 256)% 256 );
  putchar((i / 256*256) % 256 );  
  putchar( i / 256*256*256 );
}


void printShort(long i){
  putchar( i %256);
  putchar( i/256 ); 
}

int main()
{
  long x,y,c;
  long i,r,n;
  long s;
  c=1;
  x=0;
  y=0;
  //c = 40; 
  //x = -7500;
  //y =  -2000;
  s=100;
  putchar('B');  putchar('M');
  printInt(54 + 3*3*3*s*s );
  printShort(0);
  printShort(0); 
  printInt(54);

  printInt(40);
  printInt( 3*s );
  printInt( 3*s );

  printShort(1);
  printShort(24);
  printInt(0);
  printInt(0);
  printInt(0);
  printInt(0);
  printInt(0);
  printInt(0);
  
  for (i = y -3*(f/c)/2; i < y+ (3*f/c)/2; i = i+ (f/s)/c){
    for (r = x -2*f/c;  r < x+ f/c ; r = r+ (f/s)/c){
      long n;
      n = 100 * compN(i,r);
      putchar ( n % 256);
      putchar ( 10* ((n / 256) /256));
      putchar ( (10* (n / 256))% 256 );
    }
    //puts ("");
  }
}

#include "stdio.h"

long f =1000;

long compN(long i, long r){
  long  R, I, b, n;
  I = i;
  R = r;
  n=0;
  b = I * I;
  while (n<=26 && R * R + b < 10*f*f){
    I = (2 * R * I)/f + i;
    R = (R * R -b)/f + r;
    b = I * I;
    n=n+1;
  }
  return n;
}

int main()
{
  long x,y,c;
  long i,r,n;
  c=1;
  x=0;
  y=0;
  //c = 40; 
  //x = -7500;
  //y =  -2000;
  while(1){
    long ch;
    for (i = y -f/c; i < y+ f/c; i = i+(6*f/100)/c){
      for (r = x -2*f/c;  r < x+ f/c ; r = r+(3*f/100)/c){
	putchar (compN(i,r) + 31);
      }
      puts ("");
    }
    ch = getchar();
    if(ch=='q'){
      x = x - (f/10)/c;
    }
    if(ch=='d'){
      x = x + (f/10)/c;
    }
    if(ch=='z'){
      y = y - (f/10)/c;
    }
    if(ch=='s'){
      y = y + (f/10)/c;
    }
    if(ch=='a'){
      c = (c*11)/10+1;
    }
    if(ch=='e'){
      c = (c*9-1)/10;
    }
    
  }
}

#include <stdio.h>

long clear_line(){
  printf("\033[A\033[2K");
  return 0;
}

long print(long c,long max){
  long x;
  printf("#");
  for(x=0;x<c;x=x+1){
    printf(" ");
  }
  printf("X");
  for(x=c+1;x<max;x=x+1){
    printf(" ");
  }
  printf("#\n");
  return 0;
}

int main(){
  long p;
  long m;
  long c;
  p=25;
  m=50;
  c=0;
  print(p,m);
  while(c != 'z'){
    c=getchar();
    if(c == '\n'){
      clear_line();
    } else {
      if(c=='a' && p>0){
	p=p-1;
      } else if(c=='e' && p<m-1) {
	p=p+1;
      }
    }
    clear_line();
    print(p,m);
  }
}

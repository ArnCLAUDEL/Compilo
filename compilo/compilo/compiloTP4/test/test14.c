
long f1(){
  long x;
  x=0;
  return (x=1)+x;
}

long f2(){
  long x;
  x=0;
  return x+(x=1);
}


int main(){
  long x;
  long y;
  printf("f1()=%i; f2()=%i",f1(),f2());
}

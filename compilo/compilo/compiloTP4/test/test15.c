long x;

long f(){
  x=1;
  return 1;
}

int main(){
  x=0;
  if (x<2 || f()){
    printf("test\n");
  }
  printf("x=%i\n",x);
}

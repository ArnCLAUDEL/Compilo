long x;

long f(long y){
  x=x+y;
  return x;
}

int main(){
  x=42;
  f(2);
  return f(1);
}

long f(long x,long y){
  return x+y+1;
}

int main(){
  return f(f(42,32),f(2,3));
}

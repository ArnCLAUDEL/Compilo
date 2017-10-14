long f(long x,long y){
  return x+y+1;
}

int main(){
  return f(f(0,1),f(2,3));
}

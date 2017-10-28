long fact(long x){
  if(x<2){
    return 1;
  }else{
    return x*fact(x-1);
  }
}

int main(){
  long x;
  x=2;
  x=fact((2*x)-1);
  return x;
}

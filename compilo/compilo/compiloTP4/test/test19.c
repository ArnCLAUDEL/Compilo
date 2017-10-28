long x;

long fact(){
  if(x){
    long y;
    y=x;
    x=x-1;
    return (y*fact());
  }else{
    return 1;
  }
}

int main(){
  x=4;
  return fact();
}

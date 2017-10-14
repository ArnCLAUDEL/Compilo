long fact(long x){
  if(x){
    return (fact(x-1)*x);
  }else{
    return 1;
  }
}

int main(){
  return fact(4);
}

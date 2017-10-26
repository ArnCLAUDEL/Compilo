int main(){
  long x, y;
  x=2;
  {
    long x;
    x=3;
    y=x;
  }
  return y;
}

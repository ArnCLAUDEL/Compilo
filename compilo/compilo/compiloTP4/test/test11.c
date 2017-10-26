int main(){
  long* test;
  test = malloc(16);
  test[0]=0;
  test[1]=1;
  return test[1];
}

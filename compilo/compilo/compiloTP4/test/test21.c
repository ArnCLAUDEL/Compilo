int main(){
  void* i = malloc(0);
  printf("%i\n",i);

  *(int*)i = 5;
  printf("%i\n",*((int*)i));
  
  free(i);
  printf("%i\n",i);

}

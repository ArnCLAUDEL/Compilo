#include <stdlib.h>
#include <stdio.h>

long** init(){
  long** l = (long**)malloc(8);
  *l=0;
  return l;
}

void add(long** list, long v){
  long* nl = (long*)malloc(16);
  *nl=v;
  *(nl+1)=(long) *list;
  *list= nl;
}

void printlist(long** list){
  long* l2 = *list;
  while( l2 != 0) {
    printf("%ld, ", *l2);
    //printf("i+1:%ld, ", (long)l2->next);
    l2= (long*)*(l2+1);
  }
}


int main(){
  long i;
  long** list;
  list= init();
  for(i =10005;i> 10000; i--){add(list,i);};
  printlist(list);
}

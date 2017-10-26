#include <stdlib.h>
#include <stdio.h>

long** init(){
  long** l;
  l = malloc(8);
  *l=0;
  return l;
}

void add(long** list, long v){
  long* nl;
  nl= malloc(16);
  nl[0]=v;
  nl[1]= *list;
  *list= nl;
}

void printlist(long** list){
  long* l2;
  l2 = *list;
  while( l2 != 0) {
    printf("%ld, ", l2[0]);
    l2= l2[1];
  }
}


int main(){
  long i;
  long** list;
  list= init();
  add(list, 3);
  add(list, 8);
  add(list, 42);
  add(list, 6544);
  for(i =12;i< 100; i=i+1){
    add(list,i);
  }
  printlist(list);
}

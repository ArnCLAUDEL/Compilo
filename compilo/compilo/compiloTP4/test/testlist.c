#include <stdlib.h>
#include <stdio.h>


typedef struct node{
  long val;
  struct node* next;
} node;

struct node** init(){
  struct node** l = (struct node**)malloc(8);
  *l=0;
  return l;
}

void add(struct node** list, long v){
  struct node* nl = (struct node*)malloc(sizeof(struct node));
  nl->val=v;
  nl->next=*list;
  *list= nl;
}

void printlist(struct node** list){
  struct node* l2 = *list;
  while( l2 != 0) {
    printf("%ld, ", l2->val);
    //printf("i+1:%ld, ", (long)l2->next);
    l2=l2->next;
  }
}


int main(){
  struct node** list= init();
  add(list, 3);
  add(list, 8);
  add(list, 42);
  add(list, 6544);
  printlist(list);
}

#include <stdio.h>
#include <stdlib.h>

long partition (long* arr, long low, long high)
{
  long pivot;
  long i;
  long j;
  long tmp;

  pivot = arr[high];
  i = low-1;

  for(j = low; j < high; j=j+1){
    if (arr[j] <= pivot){
      i=i+1; 
      tmp= arr[i];
      arr[i]=arr[j];
      arr[j]=tmp;
    }
  }
  tmp= arr[i+1];
  arr[i+1]=arr[high];
  arr[high]=tmp;
  return (i + 1);
}


void quickSort(long* arr, long low, long high)
{
  if (low < high)
    {
      long pi;
      pi = partition(arr, low, high);

      quickSort(arr, low, pi - 1);
      quickSort(arr, pi + 1, high);
    }
}

void printtable(long* t, long size){
  long i;
  for(i=0;i<size;i=i+1){
    printf("%ld, ", t[i]);
  }
}

int main(){
  long* t;
  t = malloc(8*8);
  t[0] =5;
  t[1] = 3;
  t[2] = 58;
  t[3] = 1;
  t[4] = 7;
  t[5] = 4;
  t[6] = 100;
  t[7] = 2;
  printtable(t,8);
  printf("\n");
  quickSort(t,0,7);
  printtable(t,8);
  return t[0];
}

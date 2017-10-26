long factaux(long acc,long v){
  if(v==1){
    return acc;
  }else{ 
    return factaux(
      acc*v,
      v-1);
  }
}

long factaux2(long acc,long v){
 start:
  if(v==1){
    return acc;
  } else { 
    acc = acc*v;
    v=v-1;
    goto start;
  }
}

long fact(long x){
	return factaux2(1,x); 
} 


int main(){
  return fact(4);
}

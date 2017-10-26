
int fact(int x){
	if((x<2)){
		return 1;
	}else{
		return (x*fact((x-1)));
	}
}

int main(){
	return fact(3);
}

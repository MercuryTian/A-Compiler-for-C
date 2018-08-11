const int a=+1, b=2, c=1;
const char ch1='Y',ch2='N';

int i,j,tmp,fibo,number;
int array[10];
char word[10];

int getmax(int a, int b){
	if(a<=b)				
		printf(b);				

	else{
		printf(a);				
	}
	
}

void print(){
	printf("This is a string");
}

int compute(){
	int n;
	scanf(tmp);
	n=a+b*c-(tmp+3)*2;
	printf(n);
}

char test1(char ch){
	char x;
	x=ch+1;
	return (x);
}

void test2(int num, char ch){
	printf(ch);
	if(num==ch){
		printf(word);
	}
	if(num!=ch)
		printf(ch1);
}

void test3(){
	scanf(i);
	scanf(j);
	if(i<j)
		printf("i<j");
	if(i==j)
		printf("i=j");
	if(i>j)
		printf("i>j");
	if(a<=c)
		printf("a<=c");
	if(b>=c)
		printf("b>=c");
}

void test4(){
	const int _var_X=123,_var_Y=456;
	printf(_var_X+_var_Y);
	printf("\n");
	printf(_var_X-_var_Y);
	printf("\n");
	printf(_var_X*_var_Y);
	printf("\n");
	printf(_var_X/_var_Y);
}

void test5(){
	printf("+-*/ !%#$&,().-/0123456789:;<>=?@ABCDEFGHIJKLMNOPQRSRUVWXYZabcdEFGHIJKLMNOPQRSTUVWXYZ");
}

int fibonacci (int n){   
    if(n==1) return (1);    
    if(n!=2) return (+fibonacci(n+-1)+fibonacci(n-2)+0); 
    return (1);
}

void main()
{
	const int _var_N=+101;
	const int _var_M=-101;

	int choice;
	scanf(choice);
	if(choice<10){
		switch(choice){
			case 0: getmax(a,b);
			case 1: print();
			case 2: compute();
			case 5: test3();
			case 6: test4();
			case 7: test5();
			case 8: 
			{
                tmp = _var_M + _var_N;
                printf(tmp);
			}
			case 9:
			{
				scanf(number);
				fibo = fibonacci(number);
				printf(fibo);
			}
			default: printf("overflow");
		}
	}
}





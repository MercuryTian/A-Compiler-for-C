void test(){
	printf("+-*/ !%#$&,().-/0123456789:;<>=?@ABCDEFGHIJKLMNOPQRSRUVWXYZabcdEFGHIJKLMNOPQRSTUVWXYZ");
}

void main()
{
	int choice;
	scanf(choice);
	if(choice<9){
		switch(choice){
			case 7: test();
			default: printf("overflow");
		}
	}
}

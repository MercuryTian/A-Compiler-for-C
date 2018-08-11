void test(){
    const int _var_X=123,_var_Y=456;
    printf(_var_X+_var_Y);
    printf("\n");
    printf(_var_X-_var_Y);
    printf("\n");
    printf(_var_X*_var_Y);
}

void main()
{
    int choice;
    scanf(choice);
    if(choice<9){
        switch(choice){
            case 6: test();
            default: printf("overflow");
        }
    }
}

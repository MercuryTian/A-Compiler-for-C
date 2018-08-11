void test(){
    scanf(i);
    scanf(j);
    if(i<j)
        printf("i<j");
    if(i==j)
        printf("i=j");
    if(i>j)
        printf("i>j");
}

void main()
{
    int choice;
    scanf(choice);
    if(choice<9){
        switch(choice){
            case 5: test()
            default: printf("overflow");
        }
    }
}

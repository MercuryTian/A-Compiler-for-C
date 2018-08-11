//
//  main.cpp
//  lexical analyzer
//
//  Created by Mercury Tien.
//  Copyright (c) 2016 Macbook. All rights reserved.
//

#include <stdio.h>
#include <ctype.h>
#include <cstring>
#include <iostream>
#include <string>
#include <fstream>
#include <queue>
#include <vector>
#include <map>
#include <algorithm>
#include "tool.h"

using namespace std;

char token[1024];            //存放单词的字符串，记录单词值
char word[1024];             //读进来的字符串，待处理
char ch=' ';                //存放当前读进的字符
string symbol;              //枚举型全局变量，存放当前识别单词的类型
int num;                    //整型全局变量，存放当前读入的整型数值
int p;                      //读token的指针
int ll;                     //读文件的行数
queue<string> q_token;       //存放语法分析时预读的单词或单词串
queue<string> q_symbol;
string rcd;                 //用于记录无返回值函数定义和主函数区分时第二个单词(一个是标识符，一个是main)
ifstream file;
bool ifOp;                  //优化开关

/* support to log in table */
bool isGlobal = false;
string functName;           //函数名
int num_tab;                //组装的整数
int off_tab = 0;                //偏移量，字符和整数都按照word+4来处理
int addr_tab = 0;

/* support to construct quaternary */
string fac, termstr, expression, label;
int fac_no, term_no, expr_no, lab_no, str_no;
int integer_no;
string write_type = "";
string glo_lab, glo_expr, glo_str;
/* generate quaternary */
string factor_auto(){
    fac = ".factor" + numTOstrs(fac_no);
    fac_no++;
    return fac;
}
string term_auto(){
    termstr = ".term" + numTOstrs(term_no);
    term_no++;
    return termstr;
}
string expr_auto(){
    expression = ".expr" + numTOstrs(expr_no);
    expr_no++;
    return expression;
}
string label_auto(){
    label  = ".label" + numTOstrs(lab_no);
    lab_no++;
    return label;
}
string str_auto(){
    glo_str = ".str" + numTOstrs(str_no);
    str_no++;
    return glo_str;
}
/* get src */
string get_factor(){
    return fac;
}
string get_term(){
    return termstr;
}
string get_expression(){
    return  expression;
}
string get_label(){
    return label;
}
string get_str(){
    return glo_str;
}

/* type */
enum type_table{
    VOID,
    INT,
    CHAR,
    PAR_INT,
    PAR_CHAR,
    ERR
};

/* symbol item 符号表项 */
struct item_table{
    string name;
    type_table type;
    int size;
    string value;           //for constant
    string functBelong;     //belong to which function, if is a local variable
    int position;
    int address;            //reserved address
    int offset;
    bool isArray;
    bool isGlobal;
    bool isConst;
    bool isFunct;
    int parNum;
};
item_table tmp_tab;
vector <item_table> symTab;

/* insert into symbol table */
void insertTable(){
    symTab.push_back(tmp_tab);
}

/* search global variable */
item_table* searchGlo_var(string name){
    vector<item_table>:: iterator i;
    for(i=symTab.begin(); i!=symTab.end(); i++){
        if(name == i->name && i->functBelong=="")
            return &*i;     //如果找到了，重复定义，返回这个item_table
    }
    return nullptr;         //如果没找到，返回空指针
}

/* search variable in function */
item_table* searchFunct_var(string functName, string varName){
    vector<item_table>:: iterator i;
    for(i=symTab.begin(); i!=symTab.end(); i++){
        if(functName == i->functBelong && varName == i->name){
            return &*i;     //如果找到了，重复定义，返回这个item_table
        }
    }
    return nullptr;         //如果没找到，返回空指针
}

/* reserve aimcode */
vector<string>aim_line;
int findMaxoff(string Functname){
    int off = 0, size= 4;
    vector<item_table>:: iterator i;
    for(i=symTab.begin(); i!=symTab.end(); i++){
        if(i->functBelong == Functname){
            if(off<i->offset){
                off = i->offset;
                if(i->isArray)
                    size = i->size;
                else
                    size = 4;
            }
        }
    }
    return off+size;    //分配的空间大小
}
/* clear tmp_tab */
void clearTmp(){
    tmp_tab.name = "";
    tmp_tab.type = ERR;
    tmp_tab.size = 0;
    tmp_tab.value = "";
    tmp_tab.functBelong = "";
    tmp_tab.position = -1;
    tmp_tab.address = -1;
    tmp_tab.offset = -1;
    tmp_tab.isArray = false;
    tmp_tab.isGlobal = false;
    tmp_tab.isConst = false;
    tmp_tab.isFunct = false;
    tmp_tab.parNum = 0;
}
int parNum = 0;

/* quaternary */
struct quater{
    string op;
    string src1;
    string src2;
    string obj;
};
vector<quater> quaternary;

/* insert quaternary */
void insertQuater(string op, string src1, string src2, string obj){
    quater tmp;
    tmp.op = op;
    tmp.src1 = src1;
    tmp.src2 = src2;
    tmp.obj = obj;
    quaternary.push_back(tmp);
}

/*OPTIMIZATION: iterate quaters */
void iterateQuater(){
    vector<quater>:: iterator i;
    for(i=quaternary.begin(); i!=quaternary.end(); i++){
        if(i->op == "assign" && i->obj.c_str()[0] == '.'){
            if((i+1)->op == "assign" && (i+1)!=quaternary.end() && (i+1)->src1==i->obj){
                //下一个四元式仍是assign，且赋值临时变量和上一行的被赋值临时变量相等，且没有读到四元式末尾
                if((i+2)->op == "assign" && (i+2)!=quaternary.end() && (i+2)->src1==(i+1)->obj
                   && (i+1)->obj.c_str()[0]=='.'){ //到第三行，条件同上
                    i->obj = (i+2)->obj;
                    i = quaternary.erase(i+1);
                    i = quaternary.erase(i);
                }
                else{ //只有两行的情况
                    i->obj = (i+1)->obj;
                    i = quaternary.erase(i+1);
                }
                i--;
            }
        }
    }
}

/*error*/
void error(int i){
    if(i == 1)              //找不到整数
        printf("Can't find integer.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 2)         //未声明的标识符
        printf("Undeclared identifier.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 3)         //此处应为标识符
        printf("Identifier expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 4)         //此处应为字符
        printf("Char expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 5)         //此处应为类型标识符
        printf("Type identifier expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 6)         //此处应为[
        printf("[ expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 7)         //此处应为]
        printf("] expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 8)         //数组应定义大小
        printf("Array must have size.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 9)         //此处应为表达式
        printf("Expression expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 10)        //此处应为(
        printf("( expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 11)        //此处应为)
        printf(") expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 12)        //此处应为因子
        printf("Factor expected.     *CONTENT: %s      *POSITION: %d\n", word,ll);
    else if(i == 13)        //此处应为项
        printf("Term expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 14)        //此处应为if
        printf("If expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 15)        //此处应为while
        printf("While expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 16)        //此处应为=
        printf("= expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 17)        //此处应为scanf
        printf("Scanf expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 18)        //此处应为printf
        printf("Printf expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 19)        //此处应为:
        printf(": expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 20)        //此处应为常量
        printf("Constant expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 21)        //此处应为case
        printf("Case expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 22)        //此处应为default
        printf("Default expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 23)        //此处应为switch
        printf("Switch expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 24)        //此处应为{
        printf("{ expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 25)        //此处应为}
        printf("} expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 26)        //此处应为return
        printf("Return expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 27)        //此处应为语句
        printf("Statement expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 28)        //此处应为;
        printf("; expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 29)        //此处应为void
        printf("Void expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 30)        //此处应为main
        printf("Main expected.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 31)        //不合法的整数
        printf("Illegal integer.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 32)        //不合法的字符
        printf("Illegal character.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 33)        //读到文件行末尾
        printf("End of a line.     *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 34)        //重复定义
        printf("Dupilicate definition.      *CONTENT: %s      *POSITION: %d\n", word, ll);
    else if(i == 35)        //未定义
        printf("Can't find definition.    *CONTENT: %s      *POSITION: %d\n",  word, ll);
    else if(i == 36)        //重复定义
        printf("Repeated definition.    *CONTENT: %s      *POSITION: %d\n",  word, ll);
    else if(i == 37)        //函数名不能被赋值
        printf("Function cannot be assigned.    *CONTENT: %s      *POSITION: %d\n",  word, ll);
    else if(i == 38)        //参数个数不匹配
        printf("The number of parameters does not match.    *CONTENT: %s    *POSITION: %d\n", word, ll);
    else if(i == 39)        //scanf内容无效
        printf("Scanf: Input invalid.   *CONTENT: %s    *POSIION: %d\n",word, ll);
    else if(i == 40)        //void函数return了一个值
        printf("Void function mustn't return a value.   *CONTENT: %s    *POSITION: %d\n", word, ll);
    else
        printf("UNKNOWN.     *CONTENT: %s      *POSITION: %d\n", word, ll);
//        system("pause");
}

/*pop queue*/
void clearQueue(){
    q_token.pop();
    q_symbol.pop();
    if(q_token.size() > 0){
        symbol = q_symbol.front();
        string tmp = q_token.front();
        strcpy(token,tmp.c_str());
    }
}

/*clear token array*/
void clearToken(){
    int i;
    for(i=0; token[i]!='\0'; i++){
        token[i]='\0';
    }
    ch = ' ';
}

/*judge if is space*/
bool isSpace(){
    if(ch == ' ')
        return true;
    else
        return false;
}

/*judge if is return*/
bool isNewline(){
    if(ch == '\n')
        return true;
    else
        return false;
}
/*judge if is tab*/
bool isTab(){
    if(ch == '\t')
        return true;
    else
        return false;
}

/*judge if is letter*/
bool isLetter(){
    if(isalpha(ch) || ch=='_')
        return true;
    else
        return false;
}

/*judge if is digit*/
bool isDigit(){
    if(isdigit(ch))
        return true;
    else
        return false;
}

/*judge if is colon*/
bool isColon(){
    if(ch == ':')
        return true;
    else
        return false;
}

/*judge if is comma*/
bool isComma(){
    if(ch == ',')
        return true;
    else
        return false;
}

/*judge if is semi*/
bool isSemi(){
    if(ch == ';')
        return true;
    else
        return false;
}

/*judge if is . */
bool isPeriod(){
    if(ch == '.')
        return true;
    else
        return false;
}

/*judge if is = */
bool isEqu(){
    if(ch == '=')
        return true;
    else
        return false;
}

/*judge if is + */
bool isPlus(){
    if(ch == '+')
        return true;
    else
        return false;
}

/*judge if is - */
bool isMinus(){
    if(ch == '-')
        return true;
    else
        return false;
}

/*judge if is / */
bool isDivi(){
    if(ch == '/')
        return true;
    else
        return false;
}

/*judge if is * */
bool isStar(){
    if(ch == '*')
        return true;
    else
        return false;
}

/*judge if is < */
bool isLess(){
    if(ch == '<')
        return true;
    else
        return false;
}

/*judge if is > */
bool isMore(){
    if(ch == '>')
        return true;
    else
        return false;
}

/*judge if is ! */
bool isSigh(){
    if(ch == '!')
        return true;
    else
        return false;
}

/*judge if is ( */
bool isLpar(){
    if(ch == '(')
        return true;
    else
        return false;
}

/*judge if is ) */
bool isRpar(){
    if(ch == ')')
        return true;
    else
        return false;
}

/*judge if is [ */
bool isLbrack(){
    if(ch == '[')
        return true;
    else
        return false;
}

/*judge if is ] */
bool isRbrack(){
    if(ch == ']')
        return true;
    else
        return false;
}

/*judge if is { */
bool isLbrace(){
    if(ch == '{')
        return true;
    else
        return false;
}

/*judge if is } */
bool isRbrace(){
    if(ch == '}')
        return true;
    else
        return false;
}

/*judge if is ' */
bool isSingle(){
    if(ch == '\'')                              //单引号要用转义字符
        return true;
    else
        return false;
}

/*judge if is " */
bool isDouble(){
    if(ch == '\"')                              //双引号要用转义字符
        return true;
    else
        return false;
}

/*link ch and token*/
void catToken(){
    char tmp[2];
    tmp[1] = '\0';
    tmp[0] = ch;
    strcat(token, tmp);
}

/*retreat a char 读字符指针后退一个*/
int retract(){
    return p--;
}

/*check reserved word*/
string reserver(){
    //对于字母，如果不是保留字，就是标识符
    if(!strcmp(token,"if") && !strcmp(token,"else") && !strcmp(token,"switch") && !strcmp(token,"case")
       && !strcmp(token,"default") && !strcmp(token,"int") && !strcmp(token,"char") && !strcmp(token,"void")
       && !strcmp(token,"main") && !strcmp(token,"while") && !strcmp(token,"return") && !strcmp(token,"scanf")
       && !strcmp(token,"printf") && !strcmp(token,"const"))
        return "IDENT";                         //void main 放到语法分析程序中考虑
    else if(token == string("if")){
        return "IF";
    }
    else if(token == string("else")){
        return "ELSE";
    }
    else if(token == string("while")){
        return "WHILE";
    }
    else if(token == string("switch")){
        return "SWITCH";
    }
    else if(token == string("case")){
        return "CASE";
    }
    else if(token == string("default")){
        return "DEFAULT";
    }
    else if(token == string("int")){
        return "INT";
    }
    else if(token == string("char")){
        return "CHAR";
    }
    else if(token == string("void")){
        return "VOID";
    }
    else if(token == string("main")){
        return "MAIN";
    }
    else if(token == string("return")){
        return "RETURN";
    }
    else if(token == string("scanf")){
        return "SCANF";
    }
    else if(token == string("printf")){
        return "PRINTF";
    }
    else if(token == string("const")){
        return "CONST";
    }
    else
        return "IDENT";
}

/*transfer token to integer*/
int tranNum(char token[]){
    int i=0, num=0, n;
    while(token[i] != '\0')
        i++;
    n = i;
    
    for(i=0; i<n; i++){
        num = num*10 + token[i] - '0';
    }
    return num;
}

/*transfer ch to digit*/
int tranDigit(char ch){
    return ch- '0';
}

/*Lexical-Analyzer*/
/* 1: 读到单词，正常继续
 * 0: 没读到单词，一行结束
 * -1: 没读到单词，但是发现错误
 */
int getsym()
{
    clearToken();
    while(isSpace() || isNewline() || isTab())  //这里有问题，多个空格应该当做一个空格处理，字符串内的空格不过滤??
    {
        ch = word[p++];
        if(strlen(word) < p)                    //没有读到单词，一行结束
            return 0;
    }
    
    if(isLetter()){                             //如果读到的是字母
        while(isLetter() || isDigit()){         //＜标识符＞::= ＜字母＞｛＜字母＞｜＜数字＞｝
            catToken();                         //将字符拼接成字符串
            ch = word[p++];                     //getchar();
        }
        retract();                              //回退一个字符
        
        string resultValue = reserver();        //resultValue是查找保留字的返回值
        
        if(resultValue == string("IDENT"))
            symbol = string("IDENT");           //token中的字符串为标识符
        else
            symbol = resultValue;               //记录类别编码
    }
    
    /*＜数字＞::= ０｜＜非零数字＞
     ＜非零数字＞  ::= １｜．．．｜９
     ＜无符号整数＞  ::= ＜非零数字＞｛＜数字＞｝
     */
    else if(isDigit()){                         //如果读到的是数字，要先判断是否是0
        if(tranDigit(ch) == 0){
            ch = word[p++];                     //预读一个字符
            if(isDigit()){                      //如果下一个还是数字，报错
                error(31);
                return -1;
            }
            else{                               //只有一个0，结束，返回类别编码和单词值
                symbol = string("SIGNED");      //0属于<整数>
                num = 0;
                token[0] = '0';
            }
            retract();                          //回退一个字符
        }
        else{                                   //如果读到的是非零数
            while(isDigit()){
                catToken();
                ch = word[p++];                 //getchar();
            }
            retract();
            num = tranNum(token);
            symbol = string("UNSIGNED");        //此时识别的是<无符号整数>
        }
    }
    
    else if(isColon()){                         //如果是冒号
        symbol = string("COLON");
        token[0] = ':';
        token[1] = '\0';
    }
    
    else if(isPlus()){                          //如果是加号
        symbol = string("ADDSY");
        token[0] = '+';
        token[1] = '\0';
    }
    
    else if(isMinus()){                         //如果是减号
        symbol = string("MINUSSY");
        token[0] = '-';
        token[1] = '\0';
    }
    
    else if(isStar()){                          //如果是乘号
        symbol = string("MULSY");
        token[0] = '*';
        token[1] = '\0';
    }
    
    else if(isDivi()){                          //如果是除号
        symbol = string("DIVSY");
        token[0] = '/';
        token[1] = '\0';
    }
    
    else if(isLess()){                          //如果是小于号
        ch = word[p++];
        if(isEqu()){                            //如果预读的字符是等号
            symbol = string("LESSEQSY");
            token[0] = '<';
            token[1] = '=';
            token[2] = '\0';
        }
        else{
            retract();
            symbol = string("LESSSY");
            token[0] = '<';
            token[1] = '\0';
        }
    }
    
    else if(isMore()){                          //如果是大于号
        ch = word[p++];
        if(isEqu()){                            //如果预读的字符是等号
            symbol = string("MOREEQSY");
            token[0] = '>';
            token[1] = '=';
            token[2] = '\0';
        }
        else{
            retract();
            symbol = string("MORESY");
            token[0] = '>';
            token[1] = '\0';
        }
    }
    
    else if(isSigh()){                          //如果是叹号
        ch = word[p++];
        if(isEqu()){
            symbol = string("NEQSY");
            token[0] = '!';
            token[1] = '=';
            token[2] = '\0';
        }
        else{
            retract();                          //叹号不能单独使用
            error(32);
            return -1;
        }
    }
    
    else if(isEqu()){                           //如果是等号
        ch = word[p++];
        if(isEqu()){
            symbol = string("EQUSY");           //那么是赋值符
            token[0] = '=';
            token[1] = '=';
            token[2] = '\0';
        }
        else{
            retract();
            symbol = string("ASSIGN");
            token[0] = '=';
            token[1] = '\0';
        }
    }
    
    else if(isLpar()){                          //如果是左括号
        symbol = string("LPARENT");
        token[0] = '(';
        token[1] = '\0';
    }
    
    else if(isRpar()){                          //如果是右括号
        symbol = string("RPARENT");
        token[0] = ')';
        token[1] = '\0';
    }
    
    else if(isLbrack()){                        //如果是[
        symbol = string("LBRACK");
        token[0] = '[';
        token[1] = '\0';
    }
    
    else if(isRbrack()){                        //如果是]
        symbol = string("RBRACK");
        token[0] = ']';
        token[1] = '\0';
    }
    
    else if(isLbrace()){                        //如果是{
        symbol = string("LBRACE");
        token[0] = '{';
        token[1] = '\0';
    }
    
    else if(isRbrace()){                        //如果是}
        symbol = string("RBRACE");
        token[0] = '}';
        token[1] = '\0';
    }
    
    else if(isComma()){                         //如果是逗号
        symbol = string("COMMA");
        token[0] = ',';
        token[1] = '\0';
    }
    
    else if(isPeriod()){                        //如果是句号
        symbol = string("PERIOD");
        token[0] = '.';
        token[1] = '\0';
    }
    
    else if(isSemi()){
        symbol = string("SEMI");                //如果是分号
        token[0] = ';';
        token[1] = '\0';
    }
    
    else if(isSingle()){                        //如果是单引号，开始处理字符SYM
        ch = word[p++];
        if(isLetter()||isDigit()||isPlus()||isDivi()||isStar()||isMinus()){
            token[0] = ch;
            ch = word[p++];
            if(isSingle()){
                token[1] = '\0';
                symbol = string("SYM");
            }
            else{
                retract();
                error(32);
                return -1;
            }
        }
        else{
            retract();
            error(32);
            return -1;
        }
    }
    
    else if(isDouble()){                        //如果是双引号，开始处理字符串CHARS
        ch = word[p++];
        while(!isDouble()){
            if(strlen(word)<p){
                error(33);
                return -1;                      //return -1表示错误
            }
            else{
                if(ch==32 || ch==33 || (ch>=35 && ch<=126)){
                    catToken();
                    ch = word[p++];
                }
                else{
                    retract();
                    error(32);
                    return -1;
                }
            }
        }
        symbol = string("CHARS");
    }
    
    
    else error(32);
    
    return 1;
}

/* 特殊情况多预读的getsym */
/* -1: 错误
 * 1: 读到单词，正常继续
 * 0: 没读到单词，一行结束
 * 2: 文件结束
 */
int getsym_q(){
    int r;
    while ((r=getsym()) == 0) {
        if(!file.eof()){
            file.getline(word, 1024);
//            word[strlen(word)-1] = '\0';    //处理\r
            ll++;
            p = 0;
        }
        else{
            return 2;
        }
    }
    if(r != 1)
        return -1;
    
    q_symbol.push(symbol);
    string tmp = string(token);
    //若标识符有大写字母，转换成小写字母
    if(symbol == "IDENT"){
        string low;
        low.resize(tmp.size());
        transform(tmp.begin(), tmp.end(), low.begin(), ::tolower);
        tmp = low;
    }
    strcpy(token,tmp.c_str());
    q_token.push(token);
    strcpy(token,q_token.front().c_str());
    symbol = q_symbol.front();
    
    return r;   //正常继续,return 1
}

/* <整数> */
void integer(){
    if(symbol == "ADDSY"){
        clearQueue();
        getsym_q();
        if(symbol == "UNSIGNED"){
            //组装整数
            num_tab = num;
            tmp_tab.value = num_tab;
            integer_no = num_tab;
            //pre-read
            clearQueue();
            getsym_q();
        }
        else error(1);
    }
    else if(symbol == "MINUSSY"){
        clearQueue();
        getsym_q();
        if(symbol == "UNSIGNED"){
            clearQueue();
            getsym_q();
            //组装整数
            num_tab = 0 - num;
            tmp_tab.value = num_tab;
            integer_no = num_tab;
        }
        else error(1);
    }
    else if(num == 0){
        clearQueue();
        getsym_q();
        num_tab = 0;
        integer_no = num_tab;
        return ;
    }
    else if(symbol == "UNSIGNED"){
        clearQueue();
        getsym_q();
        num_tab = num;
        integer_no = num_tab;
    }
    else error(1);
}

/* <常量定义> */
void constDef(){
    //＜常量说明＞::= const＜常量定义＞;{const＜常量定义＞;}
    //＜常量定义＞::=int＜标识符＞＝＜整数＞{,＜标识符＞＝＜整数＞}|char＜标识符＞＝＜字符＞{,＜标识符＞＝＜字符＞}
    string tmp_value, tmp_name;
    if(symbol == "INT"){
        tmp_tab.type = INT;
        tmp_tab.position = ll;
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol == "IDENT"){
            tmp_tab.name = string(token);
            tmp_name = string(token);
            //pre-read
            clearQueue();
            getsym_q();
            if(symbol == "ASSIGN"){
                //pre-read
                clearQueue();
                getsym_q();
                integer();
                tmp_value = numTOstrs(num_tab);
                insertQuater("const", "int", tmp_value, tmp_name);
                //log in table
                if(isGlobal){
                    if(searchGlo_var(tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.value = numTOstrs(num_tab);
                        tmp_tab.address =addr_tab;
                        tmp_tab.isGlobal = true;
                        tmp_tab.isConst = true;
                        insertTable();
                        clearTmp();
                        addr_tab += 4;
                    }
                }
                else{   //if is not a global constant, must be a local constant
                    if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.value = numTOstrs(num_tab);
                        tmp_tab.functBelong = functName;
                        tmp_tab.offset = off_tab;
                        tmp_tab.isGlobal = false;
                        tmp_tab.isConst = true;
                        insertTable();
                        clearTmp();
                        off_tab += 4;
                    }
                }
                string temp_type;
            }
            else error(2);
        }
        else error(3);
        
        while(symbol == "COMMA"){
            //pre-read
            clearQueue();
            getsym_q();
            if(symbol == "IDENT"){
                tmp_name = string(token);
                tmp_tab.name = string(token);
                //pre-read
                clearQueue();
                getsym_q();
                if(symbol == "ASSIGN"){
                    //pre-read
                    clearQueue();
                    getsym_q();
                    integer();
                    tmp_value = numTOstrs(num_tab);
                    insertQuater("const", "int", tmp_value, tmp_name);
                    //log in table
                    if(isGlobal){
                        if(searchGlo_var(tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = INT;
                            tmp_tab.value = numTOstrs(num_tab);
                            tmp_tab.address =addr_tab;
                            tmp_tab.position = ll;
                            tmp_tab.isGlobal = true;
                            tmp_tab.isConst = true;
                            insertTable();
                            clearTmp();
                            addr_tab += 4;
                        }
                    }
                    else{   //if is not a global constant, must be a local constant
                        if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = INT;
                            tmp_tab.value = numTOstrs(num_tab);
                            tmp_tab.functBelong = functName;
                            tmp_tab.offset = off_tab;
                            tmp_tab.position = ll;
                            tmp_tab.isGlobal = false;
                            tmp_tab.isConst = true;
                            insertTable();
                            clearTmp();
                            off_tab += 4;
                        }
                    }
                    string temp_type;
                }
                else error(2);
            }
            else error(3);
        }
        // cout<<symbol<<"*SYNTAX: This is a definition of constant."<<endl;
    }
    
    else if(symbol == "CHAR"){
        tmp_tab.type = CHAR;
        tmp_tab.position = ll;
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol == "IDENT"){
            tmp_name = string(token);
            tmp_tab.name = string(token);
            //pre-read
            clearQueue();
            getsym_q();
            if(symbol == "ASSIGN"){
                //pre-read;
                clearQueue();
                getsym_q();
                tmp_value = string(token);
                insertQuater("const", "char", tmp_value, tmp_name);
                if(symbol == "SYM"){
                    //log in table
                    if(isGlobal){
                        if(searchGlo_var(tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.value = string(token);
                            tmp_tab.address = addr_tab;
                            tmp_tab.position = ll;
                            tmp_tab.isGlobal = true;
                            tmp_tab.isConst = true;
                            insertTable();
                            clearTmp();
                            addr_tab += 4;
                        }
                    }
                    else{
                        if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.value = string(token);
                            tmp_tab.offset = off_tab;
                            tmp_tab.functBelong = functName;
                            tmp_tab.position = ll;
                            tmp_tab.isGlobal = false;
                            tmp_tab.isConst = true;
                            insertTable();
                            clearTmp();
                            off_tab += 4;
                        }
                    }
                    string temp_type;
                    //pre-read
                    clearQueue();
                    getsym_q();
                }
                else
                    error(4);
            }
            else error(2);
        }
        else error(3);
        
        while(symbol == "COMMA"){
            //pre-read
            clearQueue();
            getsym_q();
            if(symbol == "IDENT"){
                tmp_name = string(token);
                tmp_tab.name = string(token);
                //pre-read
                clearQueue();
                getsym_q();
                if(symbol == "ASSIGN"){
                    clearQueue();
                    getsym_q();
                    tmp_value = string(token);
                    insertQuater("const", "char", tmp_value, tmp_name);
                    if(symbol == "SYM"){
                        //log in table
                        if(isGlobal){
                            if(searchGlo_var(tmp_tab.name) != nullptr)
                                error(34);
                            else{
                                tmp_tab.type = CHAR;
                                tmp_tab.value = string(token);
                                tmp_tab.address = addr_tab;
                                tmp_tab.position = ll;
                                tmp_tab.isGlobal = true;
                                tmp_tab.isConst = true;
                                insertTable();
                                clearTmp();
                                addr_tab += 4;
                            }
                        }
                        else{
                            if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                                error(34);
                            else{
                                tmp_tab.type = CHAR;
                                tmp_tab.value = string(token);
                                tmp_tab.offset = off_tab;
                                tmp_tab.position = ll;
                                tmp_tab.functBelong = functName;
                                tmp_tab.isGlobal = false;
                                tmp_tab.isConst = true;
                                insertTable();
                                clearTmp();
                                off_tab += 4;
                            }
                        }
                        string temp_type;
                        //pre-read
                        clearQueue();
                        getsym_q();
                    }
                    else
                        error(4);
                }
                else error(2);
            }
            else error(3);
        }
        // cout<<symbol<<"*SYNTAX: This is a definition of constant."<<endl;
    }
    
    else error(5);
}

/* <变量定义> */
//已经预读了3个单词，所以每次调用这个函数之前，还要先预读两次
void varDef(){
    //＜变量定义＞::=＜类型标识符＞(＜标识符＞|＜标识符＞‘[’＜无符号整数＞‘]’){,＜标识符＞|＜标识符＞‘[’＜无符号整数＞‘]’ }
    string tmp_type, tmp_name;
    if(symbol=="INT" || symbol=="CHAR"){
        tmp_tab.position = ll;
        //table support
        type_table temp_sym;
        if(symbol == "INT")
            temp_sym = INT;
        else
            temp_sym = CHAR;
        
        clearQueue();
        symbol = q_symbol.front();
        string tmp = q_token.front();
        strcpy(token,tmp.c_str());
        
        if(symbol != "IDENT")
            error(3);
        else{
            //build quater
            tmp_name = string(token);
            tmp_tab.name = string(token);
            //pre-read
            clearQueue();
            symbol = q_symbol.front();
            string tmp = q_token.front();
            strcpy(token,tmp.c_str());
    
            //int/char类型数组
            if(symbol == "LBRACK"){
                clearQueue();
                getsym_q();
                if(symbol == "UNSIGNED"){
                    tmp_tab.size = num;
                    clearQueue();
                    getsym_q();
                    
                    //build quater-array
                    if(temp_sym == INT)
                        insertQuater("array", "int", numTOstrs(tmp_tab.size * 4), tmp_name);
                    else
                        insertQuater("array", "char", numTOstrs(tmp_tab.size * 4), tmp_name);
                    
                    if(symbol != "RBRACK")
                        error(7);
                    else{
                        //log in table
                        if(isGlobal){
                            if(searchGlo_var(tmp_tab.name) != nullptr)
                                error(34);
                            else{
                                tmp_tab.type = temp_sym;
                                tmp_tab.address = addr_tab;
                                tmp_tab.position = ll;
                                tmp_tab.isArray = true;
                                tmp_tab.isGlobal = true;
                                tmp_tab.isConst = false;
                                addr_tab += 4 * tmp_tab.size;
                                insertTable();
                                clearTmp();
                            }
                        }
                        else{
                            if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                                error(34);
                            else{
                                tmp_tab.type = temp_sym;
                                tmp_tab.offset = off_tab;
                                tmp_tab.functBelong = functName;
                                tmp_tab.position = ll;
                                tmp_tab.isArray = true;
                                tmp_tab.isGlobal = false;
                                tmp_tab.isConst = false;
                                off_tab += 4 * tmp_tab.size;
                                insertTable();
                                clearTmp();
                            }
                        }
                        //pre-read
                        clearQueue();
                        getsym_q();
                    }
                }
                else error(8);
            }
            
            else if(symbol == "SEMI"){
                //build quater
                if(temp_sym == INT)
                    insertQuater("int", "", "", tmp_name);
                else
                    insertQuater("char", "", "", tmp_name);
                //int/char类型变量, log in table
                if(isGlobal){
                    if(searchGlo_var(tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.type = temp_sym;
                        tmp_tab.address = addr_tab;
                        tmp_tab.position = ll;
                        tmp_tab.isArray = false;
                        tmp_tab.isGlobal = true;
                        tmp_tab.isConst = false;
                        insertTable();
                        clearTmp();
                        addr_tab += 4;
                    }
                }
                else{
                    if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.type = temp_sym;
                        tmp_tab.offset = off_tab;
                        tmp_tab.functBelong = functName;
                        tmp_tab.position = ll;
                        tmp_tab.isArray = false;
                        tmp_tab.isGlobal = false;
                        tmp_tab.isConst = false;
                        insertTable();
                        clearTmp();
                        off_tab += 4;
                    }
                }
            }
            
            else{
                //build quater
                if(temp_sym == INT)
                    insertQuater("int", "", "", tmp_name);
                else
                    insertQuater("char", "", "", tmp_name);

                //int/char类型变量, log in table
                if(isGlobal){
                    if(searchGlo_var(tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.type = temp_sym;
                        tmp_tab.address = addr_tab;
                        tmp_tab.position = ll;
                        tmp_tab.isArray = false;
                        tmp_tab.isGlobal = true;
                        tmp_tab.isConst = false;
                        insertTable();
                        clearTmp();
                        addr_tab += 4;
                    }
                }
                else{
                    if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                        error(34);
                    else{
                        tmp_tab.type = temp_sym;
                        tmp_tab.offset = off_tab;
                        tmp_tab.functBelong = functName;
                        tmp_tab.position = ll;
                        tmp_tab.isArray = false;
                        tmp_tab.isGlobal = false;
                        tmp_tab.isConst = false;
                        insertTable();
                        clearTmp();
                        off_tab += 4;
                    }
                }
            }
            
            string temp_type;
        }
        
        while(symbol == "COMMA"){
            clearQueue();
            getsym_q();
            if(symbol != "IDENT")
                error(3);
            else{
                tmp_tab.name = string(token);
                tmp_name = string(token);
                //pre-read
                clearQueue();
                getsym_q();
                //int/char类型数组
                if(symbol == "LBRACK"){
                    clearQueue();
                    getsym_q();
                    if(symbol == "UNSIGNED"){
                        tmp_tab.size = num;
                        //pre-read
                        clearQueue();
                        getsym_q();
                        if(symbol != "RBRACK")
                            error(7);
                        else{
                            //build quater
                            if(temp_sym == INT)
                                insertQuater("array", "int", numTOstrs(tmp_tab.size * 4), tmp_name);
                            else
                                insertQuater("array", "char", numTOstrs(tmp_tab.size * 4), tmp_name);
                            //log in table
                            if(isGlobal){
                                if(searchGlo_var(tmp_tab.name) != nullptr)
                                    error(34);
                                else{
                                    tmp_tab.address = addr_tab;
                                    tmp_tab.position = ll;
                                    tmp_tab.isArray = true;
                                    tmp_tab.isGlobal = true;
                                    tmp_tab.isConst = false;
                                    addr_tab += 4 * tmp_tab.size;
                                    insertTable();
                                    clearTmp();
                                }
                            }
                            else{
                                if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                                    error(34);
                                else{
                                    tmp_tab.offset = off_tab;
                                    tmp_tab.functBelong = functName;
                                    tmp_tab.position = ll;
                                    tmp_tab.isArray = true;
                                    tmp_tab.isGlobal = false;
                                    tmp_tab.isConst = false;
                                    off_tab += 4 * tmp_tab.size;
                                    insertTable();
                                    clearTmp();
                                }
                            }
                            //pre-read
                            clearQueue();
                            getsym_q();
                        }
                    }
                    else error(8);
                }
                //int/char类型变量
                else if(symbol == "SEMI"){
                    //build quater
                    if(temp_sym == INT)
                        insertQuater("int", "", "", tmp_name);
                    else
                        insertQuater("char", "", "", tmp_name);
                    //int类型变量, log in table
                    if(isGlobal){
                        if(searchGlo_var(tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = temp_sym;
                            tmp_tab.address = addr_tab;
                            tmp_tab.position = ll;
                            tmp_tab.isArray = false;
                            tmp_tab.isGlobal = true;
                            tmp_tab.isConst = false;
                            insertTable();
                            clearTmp();
                            addr_tab += 4;
                        }
                    }
                    else{
                        if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = temp_sym;
                            tmp_tab.offset = off_tab;
                            tmp_tab.functBelong = functName;
                            tmp_tab.position = ll;
                            tmp_tab.isArray = false;
                            tmp_tab.isGlobal = false;
                            tmp_tab.isConst = false;
                            insertTable();
                            clearTmp();
                            off_tab += 4;
                        }
                    }
                }
                
                else{
                    //build quater
                    if(temp_sym == INT)
                        insertQuater("int", "", "", tmp_tab.name);
                    else
                        insertQuater("char", "", "", tmp_tab.name);
                    //int/char类型变量, log in table
                    if(isGlobal){
                        if(searchGlo_var(tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = temp_sym;
                            tmp_tab.address = addr_tab;
                            tmp_tab.position = ll;
                            tmp_tab.isArray = false;
                            tmp_tab.isGlobal = true;
                            tmp_tab.isConst = false;
                            insertTable();
                            clearTmp();
                            addr_tab += 4;
                        }
                    }
                    else{
                        if(searchFunct_var(functName, tmp_tab.name) != nullptr)
                            error(34);
                        else{
                            tmp_tab.type = temp_sym;
                            tmp_tab.offset = off_tab;
                            tmp_tab.functBelong = functName;
                            tmp_tab.position = ll;
                            tmp_tab.isArray = false;
                            tmp_tab.isGlobal = false;
                            tmp_tab.isConst = false;
                            insertTable();
                            clearTmp();
                            off_tab += 4;
                        }
                    }
                }
            }
        }
        // cout<<symbol<<"*SYNTAX: This is a definition of variable."<<endl;
    }
    else error(5);
}

/* <参数> */
void parameter(){
    //＜参数＞::=＜参数表＞
    //＜参数表＞::=＜类型标识符＞＜标识符＞{,＜类型标识符＞＜标识符＞}|＜空＞
    if(symbol == "INT" || symbol == "CHAR"){
        if(symbol == "INT")
            tmp_tab.type = PAR_INT;
        else
            tmp_tab.type = PAR_CHAR;
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol != "IDENT")
            error(3);
        else{
            tmp_tab.name = string(token);
            clearQueue();
            getsym_q();
            //log in table
            tmp_tab.position = ll;
            tmp_tab.functBelong = functName;
            tmp_tab.offset = off_tab;
            tmp_tab.isGlobal = false;
            tmp_tab.isConst = false;
            tmp_tab.isFunct = false;
            insertTable();
            parNum ++;
            clearTmp();
            off_tab += 4;
        }
        
        while(symbol == "COMMA"){
            clearQueue();
            getsym_q();
            if(symbol == "INT" || symbol == "CHAR"){
                if(symbol == "INT")
                    tmp_tab.type = PAR_INT;
                else
                    tmp_tab.type = PAR_CHAR;
                clearQueue();
                getsym_q();
                if(symbol != "IDENT")
                    error(3);
                else {
                    tmp_tab.name = string(token);
                    clearQueue();
                    getsym_q();
                    //log in table
                    tmp_tab.position = ll;
                    tmp_tab.functBelong = functName;
                    tmp_tab.offset = off_tab;
                    tmp_tab.isGlobal = false;
                    tmp_tab.isConst = false;
                    tmp_tab.isFunct = false;
                    insertTable();
                    parNum ++;
                    clearTmp();
                    off_tab += 4;
                }
            }
        }
        // cout<<symbol<<"*SYNTAX: This is a list of parameter."<<endl;
    }
    else    //读到的单词是空
        return;
    
}

/* <值参数表> */
void expr();
void paralist(){
    //＜值参数表＞::=＜表达式＞{,＜表达式＞}｜＜空＞
    string src1;
    
    if(symbol == "RPARENT"){
        return ;
    }
    if(symbol == "ADDSY" || symbol == "MINUSSY"
       || symbol == "IDENT" || symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"
       || symbol == "INT" || symbol == "CHAR" || symbol == "LPARENT"){
        src1 = expr_auto();
        expr();
        insertQuater("push", src1, "", ""); //值参数表进栈
    }
    else
        error(9);
    while(symbol == "COMMA"){
        clearQueue();
        getsym_q();
        src1 = expr_auto();
        expr();
        insertQuater("push", src1, "", "");
    }
    // cout<<symbol<<"*SYNTAX: This is a list of parameter."<<endl;
}

/* <有/无返回值函数调用语句> 不进行区分在语法分析中 */
//已经预读一个了，除因子之外，若其他函数调用，需要先预读一个
void functCall(){
    //＜有返回值函数调用语句＞ ::= ＜标识符＞‘(’＜值参数表＞‘)’
    if(symbol == "IDENT"){
        //pre-read
        clearQueue();
        symbol = q_symbol.front();

        if(symbol == "LPARENT"){
            clearQueue();
            getsym_q();
            paralist();
            if(symbol == "RPARENT"){
                clearQueue();
                getsym_q();
                // cout<<symbol<<"*SYNTAX: This is a call of function."<<endl;
            }
            else error(11);
        }
        else error(10);
    }
    else error(3);
}

/* <因子> */
void expr();
void functCall_y();
void factor(){
    //＜因子＞::=＜标识符＞｜＜标识符＞‘[’＜表达式＞‘]’｜＜整数＞|＜字符＞｜＜有返回值函数调用语句＞|‘(’＜表达式＞‘)’
    string tmp_factor = get_factor();
    string src1, src2;
    
    if(symbol == "IDENT"){
        src2 = string(token);
        write_type = src2;
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol == "LBRACK"){
            //pre-read
            clearQueue();
            getsym_q();
            //build quater
            src1 = expr_auto();
            expr();
            if(symbol == "RBRACK"){
                //将数组中的值取出来
                insertQuater("=[]", src1, tmp_factor, src2);
                clearQueue();
                getsym_q();
                write_type = src2;//打印数组的值，而不是ASCII
            }
            else error(7);
        }
        else if(symbol == "LPARENT"){   //已经预读一个
            if(searchGlo_var(src2)!= nullptr){
                if(searchGlo_var(src2)->isFunct && searchGlo_var(src2)->type != VOID){
                    clearQueue();
                    getsym_q();
                    paralist();
                    insertQuater("callre", tmp_factor, "", src2);
                    
                }
                else
                    error(35);
            }
            else
                //没有找到定义，报错
                error(35);
            clearQueue();
            getsym_q();
        }
        else{
            insertQuater("assign", src2, "", tmp_factor);
        }
        // cout<<symbol<<"*SYNTAX: This is a factor."<<endl;
    }
    
    else if(symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "ADDSY" || symbol == "MINUSSY"){
        integer();
        src1 = numTOstrs(integer_no);
        insertQuater("assign", src1, "", tmp_factor);
        // cout<<symbol<<"*SYNTAX: This is a factor."<<endl;
    }
    
    else if(symbol == "SYM"){
        src1 = string(token);
        int ch = src1.c_str()[0];
        insertQuater("assign", numTOstrs(ch), "", tmp_factor);
        clearQueue();
        getsym_q();
        // cout<<symbol<<"*SYNTAX: This is a factor."<<endl;
    }
    
    else if(symbol == "LPARENT"){
        //pre-read
        clearQueue();
        getsym_q();
        //build quater
        src1 = expr_auto();
        expr();
        insertQuater("assign", src1, "", tmp_factor);
        
        if(symbol == "RPARENT"){
            clearQueue();
            getsym_q();
        }
        // cout<<symbol<<"*SYNTAX: This is a factor."<<endl;
    }

    else error(12);
}

/* <项> */
void term(){
    string src1, src2;
    //＜项＞::=＜因子＞{＜乘法运算符＞＜因子＞}
    string tmp_term = get_term();
    bool hasmul = false;
    if(symbol == "IDENT" || symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"
       || symbol == "INT" || symbol == "CHAR" || symbol == "LPARENT" || symbol == "ADDSY" || symbol == "MINUSSY"){
        src1 = factor_auto();
        factor();
    }
    else error(12);
    while(symbol == "MULSY" || symbol == "DIVSY"){
        hasmul = true;
        //record op
        string temp_sym;
        temp_sym = symbol;
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol == "IDENT" || symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"
           || symbol == "INT" || symbol == "CHAR" || symbol == "LPARENT" || symbol == "ADDSY" || symbol == "MINUSSY"){
            src2 = factor_auto();
            factor();
            if(temp_sym == "MULSY")
                insertQuater("mul", src1, src2, tmp_term);
            else
                insertQuater("div", src1, src2, tmp_term);
            src1 = tmp_term;
        }
        else error(12);
    }
    if (!hasmul) {
        insertQuater("assign", src1, "", tmp_term);
    }
    // cout<<symbol<<"*SYNTAX: This is a term."<<endl;

}

/* <表达式> */
void expr(){
    //＜表达式＞::=［＋｜－］＜项＞{＜加法运算符＞＜项＞}
    string tmp_expr = get_expression(); //先取出表达式的值
    string src1, src2, tmp_sym;
    if(symbol == "ADDSY" || symbol == "MINUSSY"){
        tmp_sym = symbol;
        clearQueue();
        getsym_q();
        src1 = term_auto();
        term();

        if(tmp_sym == "MINUSSY")
            insertQuater("sub", "0", src1, src1);
    }
    else if(symbol == "IDENT" || symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"
            || symbol == "INT" || symbol == "CHAR" || symbol == "LPARENT"){  //直接进入<项>
        src1 = term_auto();
        term();
        
    }
    else
        error(13);
    while(symbol == "ADDSY" || symbol == "MINUSSY"){
        tmp_sym = symbol;
        clearQueue();
        getsym_q();
        src2 = term_auto();
        term();
        if(tmp_sym == "ADDSY")
            insertQuater("add", src1, src2, src1);
        else
            insertQuater("sub", src1, src2, src1);
    }
    insertQuater("assign", src1, "", tmp_expr);
    // cout<<symbol<<"*SYNTAX: This is an expression."<<endl;
}

/* <条件> */
void condition(){
    string tmp_expr1, tmp_expr2;
    string tmp_op;
    //＜条件＞::=＜表达式＞＜关系运算符＞＜表达式＞｜＜表达式＞  表达式为0条件为假，否则为真
    if(symbol == "ADDSY" || symbol == "MINUSSY" || symbol == "IDENT" || symbol == "SIGNED"
       || symbol == "UNSIGNED" || symbol == "SYM" || symbol == "INT" || symbol == "CHAR"
       || symbol == "LPARENT"){
        tmp_expr1 = expr_auto();
        expr();
        if(symbol == "LESSSY" || symbol == "LESSEQSY" || symbol == "MORESY"
           || symbol == "MOREEQSY" || symbol == "NEQSY" || symbol == "EQUSY"){
            //build quater 操作符与symbol要取反
            tmp_op = symbol;
            //pre-read
            clearQueue();
            getsym_q();
            tmp_expr2 = expr_auto();
            expr();
            // cout<<symbol<<"*SYNTAX: This is a condition."<<endl;
        }
        else{//括号里只有一个表达式的情况，要和0作比较
            tmp_op = "NEQSY";
            tmp_expr2 = expr_auto();
            insertQuater("assign", "0", "", tmp_expr2);
            // cout<<symbol<<"*SYNTAX: This is a condition."<<endl;
        }
    }
    //build quater
    if(tmp_op == "LESSSY")
        insertQuater("bet", tmp_expr1, tmp_expr2, get_label());
    else if(tmp_op == "LESSEQSY")
        insertQuater("bt", tmp_expr1, tmp_expr2, get_label());
    else if(tmp_op == "MORESY")
        insertQuater("let", tmp_expr1, tmp_expr2, get_label());
    else if(tmp_op == "MOREEQSY")
        insertQuater("lt", tmp_expr1, tmp_expr2, get_label());
    else if(tmp_op == "NEQSY")
        insertQuater("beq", tmp_expr1, tmp_expr2, get_label());
    else if(tmp_op == "EQUSY")
        insertQuater("bne", tmp_expr1, tmp_expr2, get_label());
    else
        error(35);
}


/* <条件语句> */
void statement();
void state_condition(){
    //＜条件语句＞::=if ‘(’＜条件＞‘)’＜语句＞［else＜语句＞］
    string lab1, lab2;
    if(symbol == "IF"){
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            //pre-read
            clearQueue();
            getsym_q();
            lab1 = label_auto();
            condition();
            
            if(symbol == "RPARENT"){
                clearQueue();
                getsym_q();
                statement();
                if(symbol == "ELSE"){
                    lab2 = label_auto();
                    insertQuater("j", lab2, "", "");
                    insertQuater("set", lab1, "", "");
                    clearQueue();
                    getsym_q();
                    statement();
                    insertQuater("set", lab2, "", "");
                    // cout<<symbol<<"*SYNTAX: This is a conditional statement."<<endl;
                    //                    printf("*SYNTAX: This is a conditional statement.\n");
                }
                else{
                    insertQuater("set", lab1, "", "");
                }
            }
            else error(11);
        }
        else error(10);
    }
    else error(14);
}

/* <循环语句> */
void loop(){
    //＜循环语句＞::=while ‘(’＜条件＞‘)’＜语句＞
    string lab1, lab2; //入口：lab1, 出口：lab2
    if(symbol == "WHILE"){
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            clearQueue();
            getsym_q();
            lab2 = label_auto();
            insertQuater("set", lab2, "", "");
            lab1 = label_auto();
            condition();
            if(symbol == "RPARENT"){
                clearQueue();
                getsym_q();
                statement();
                insertQuater("j", lab2, "", "");
                insertQuater("set", lab1, "", "");
                // cout<<symbol<<"*SYNTAX: This is a loop."<<endl;
            }
            else error(11);
        }
        else error(10);
    }
    else error(15);
}

/* <赋值语句> */
//已经预读一个了，除去语句外，若其他函数调用，需要先预读一个
void assign(){
    //＜赋值语句＞::=＜标识符＞＝＜表达式＞|＜标识符＞‘[’＜表达式＞‘]’=＜表达式＞
    string tmp_expr, obj, src1;
    if(symbol == "IDENT"){
        obj = string(token);
        clearQueue();
        if(symbol == "ASSIGN"){
            clearQueue();
            getsym_q();
            tmp_expr = expr_auto();
            expr();
            insertQuater("assign", tmp_expr, "", obj);
            // cout<<symbol<<"*SYNTAX: This is a assign statement"<<endl;
        }
        else if(symbol == "LBRACK"){
            clearQueue();
            getsym_q();
            src1 = expr_auto();
            expr();
            if(symbol == "RBRACK"){
                clearQueue();
                getsym_q();
                if(symbol == "ASSIGN"){
                    clearQueue();
                    getsym_q();
                    tmp_expr = expr_auto();
                    expr();
                    insertQuater("[]=", src1, tmp_expr, obj);
                    // cout<<symbol<<"*SYNTAX: This is an assign statement."<<endl;
                }
                else error(16);
            }
            else error(7);
        }
        else error(6);
    }
}

/* <读语句> */
void read(){
    //＜读语句＞::=scanf ‘(’＜标识符＞{,＜标识符＞}‘)’
    if(symbol == "SCANF"){
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            clearQueue();
            getsym_q();
            if(symbol == "IDENT"){
                //判断scanf的内容是否有效，先找局部再找全局
                if(searchFunct_var(functName, token) != nullptr){
                    if(searchFunct_var(functName, token)->isArray)
                        error(39);
                    else if(searchFunct_var(functName, token)->isFunct)
                        error(39);
                }
                else if(searchGlo_var(token) != nullptr){
                    if(searchGlo_var(token)->isArray)
                        error(39);
                    else if(searchGlo_var(token)->isFunct)
                        error(39);
                }
                //插入四元式
                insertQuater("read", string(token), "", "");
                clearQueue();
                getsym_q();
                while(symbol == "COMMA"){
                    clearQueue();
                    getsym_q();
                    if(symbol == "IDENT"){
                        insertQuater("read", string(token), "", "");
                        clearQueue();
                        getsym_q();
                    }
                    else error(3);
                }
                if(symbol == "RPARENT"){
                    clearQueue();
                    getsym_q();
                    // cout<<symbol<<"*SYNTAX: This is a reading sentence."<<endl;
                }
                else error(11);
            }
            else error(3);
        }
        else error(10);
    }
    else error(17);
}

/* <写语句> */
void write(){
    //＜写语句＞::=printf ‘(’ ＜字符串＞,＜表达式＞ ‘)’| printf ‘(’＜字符串＞ ‘)’| printf ‘(’＜表达式＞‘)’
    string tmp_expr;
    if(symbol == "PRINTF"){
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            clearQueue();
            getsym_q();
            if(symbol == "CHARS"){
                string str = string(token);
                insertQuater("write", str, str_auto(), "");
                //pre-read
                clearQueue();
                getsym_q();
                if(symbol == "COMMA"){
                    //pre-read
                    clearQueue();
                    getsym_q();
                    //build quater
                    tmp_expr = expr_auto();
                    expr();
                    if(write_type != ""){
                        if((searchFunct_var(functName, write_type)!=nullptr && (searchFunct_var(functName, write_type)->type == PAR_CHAR || searchFunct_var(functName, write_type)->type == CHAR)) || (searchGlo_var(write_type)!=nullptr && (searchGlo_var(write_type)->type == CHAR))){
                            insertQuater("write", tmp_expr, "char", "");
                        }
                        else
                            insertQuater("write", tmp_expr, "int", "");
                    }
                    else{
                        insertQuater("write", tmp_expr, "int", "");
                    }
                    if(symbol == "RPARENT"){
                        clearQueue();
                        getsym_q();
                        // cout<<symbol<<"*SYNTAX: This is a writing sentence."<<endl;
                    }
                    else error(11);
                }
                else if(symbol == "RPARENT"){
                    clearQueue();
                    getsym_q();
                    // cout<<symbol<<"*SYNTAX: This is a writing sentence."<<endl;
                }
                else error(11);
            }
            else if(symbol == "ADDSY" || symbol == "MINUSSY"
                    || symbol == "IDENT" || symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"
                    || symbol == "INT" || symbol == "CHAR" || symbol == "LPARENT"){
                tmp_expr = expr_auto();
                expr();
                if(write_type != ""){
                    if((searchFunct_var(functName, write_type)!=nullptr && (searchFunct_var(functName, write_type)->type == PAR_CHAR || searchFunct_var(functName, write_type)->type == CHAR)) || (searchGlo_var(write_type)!=nullptr && (searchGlo_var(write_type)->type == CHAR))){
                        insertQuater("write", tmp_expr, "char", "");
                    }
                    else
                        insertQuater("write", tmp_expr, "int", "");
                }
                else{
                    insertQuater("write", tmp_expr, "int", "");
                }

                
                if(symbol == "RPARENT"){
                    clearQueue();
                    getsym_q();
                    // cout<<symbol<<"*SYNTAX: This is a writing sentence."<<endl;
                }
                else error(11);
            }
        }
        else error(10);
    }
    else error(18);
}

/* <情况子语句> */
void childcase(){
    //＜情况子语句＞::=case＜常量＞：＜语句＞
    int tmp_case;
    if(symbol == "CASE"){
        clearQueue();
        getsym_q();
        if(symbol == "SIGNED" || symbol == "UNSIGNED" || symbol == "SYM"){
            if(symbol == "SIGNED"){
                tmp_case = strTOnum(string(token));
                string lab1 = term_auto();
                insertQuater("assign", numTOstrs(tmp_case), "", lab1);
                insertQuater("bne", glo_expr, lab1, get_label());
            }
            else if(symbol == "UNSIGNED"){
                tmp_case = strTOnum(string(token));
                string lab1 = term_auto();
                insertQuater("assign", numTOstrs(tmp_case), "", lab1);
                insertQuater("bne", glo_expr, lab1, get_label());
            }
            else{
                tmp_case = token[0];
                string lab1 = term_auto();
                insertQuater("assign", numTOstrs(tmp_case), "", lab1);
                insertQuater("bne", glo_expr, lab1, get_label());
            }
            clearQueue();
            getsym_q();
            if(symbol == "COLON"){
                clearQueue();
                getsym_q();
                statement();
                insertQuater("j", glo_lab, "", "");
                // cout<<symbol<<"*SYNTAX: This is a child case statement."<<endl;
            }
            else error(19);
        }
        else error(20);
    }
    else error(21);
}

/* <情况表> */
void caselist(){
    //＜情况表＞::=＜情况子语句＞{＜情况子语句＞}
    string tmp_lab = label_auto();  //用来记录下一个label
    while(symbol == "CASE"){
        insertQuater("set", tmp_lab, "", "");
        tmp_lab = label_auto();
        childcase();
    }
    insertQuater("set", tmp_lab, "", "");
    // cout<<symbol<<"*SYNTAX: This is a case list."<<endl;
}

/* <缺省> */
void defaultstate(){
    //＜缺省＞::= default : ＜语句＞
    if(symbol ==  "DEFAULT"){
        clearQueue();
        getsym_q();
        if(symbol == "COLON"){
            clearQueue();
            getsym_q();
            statement();
            // cout<<symbol<<"*SYNTAX: This is default."<<endl;
            //            printf("*SYNTAX: This is default.\n");
        }
        else error(19);
    }
    else error(22);
}

/* <情况语句> */
void casestate(){
    //＜情况语句＞::=switch ‘(’＜表达式＞‘)’ ‘{’＜情况表＞［＜缺省＞］‘}’
    if(symbol == "SWITCH"){
        glo_lab = label_auto();
        //pre-read
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            clearQueue();
            getsym_q();
            glo_expr = expr_auto();
            expr();
            if(symbol == "RPARENT"){
                clearQueue();
                getsym_q();
                if(symbol == "LBRACE"){
                    clearQueue();
                    getsym_q();
                    caselist();
                    if(symbol == "DEFAULT"){
                        defaultstate();
                        if(symbol == "RBRACE"){
                            clearQueue();
                            getsym_q();
                            // cout<<symbol<<"*SYNTAX: This is a case sentence."<<endl;
                        }
                        else error(25);
                    }
                    else if(symbol == "RBRACE"){
                        clearQueue();
                        getsym_q();
                        // cout<<symbol<<"*SYNTAX: This is a case sentence."<<endl;
                    }
                    else error(25);
                    
                    insertQuater("set", glo_lab, "", "");
                }
                else error(24);
            }
            else error(11);
        }
        else error(10);
    }
    else error(23);
}

/* <返回语句> */
void returnstate(){
    //return[‘(’＜表达式＞‘)’]
    string tmp_expr;
    if(symbol == "RETURN"){
        clearQueue();
        getsym_q();
        if(symbol == "LPARENT"){
            if(searchGlo_var(functName)->type == VOID)
                error(40);
            clearQueue();
            getsym_q();
            tmp_expr = expr_auto();
            expr();
            insertQuater("return", tmp_expr, "", "");
            if(symbol == "RPARENT"){
                clearQueue();
                getsym_q();
                // cout<<symbol<<"*SYNTAX: This is a return sentence."<<endl;
            }
            else error(11);
        }
        else{
            insertQuater("return", "", "", "");
            return;
        }
    }
    else error(26);
}

/* <语句> */
void statelist();
void statement(){
    /*
     ＜语句＞::=＜条件语句＞｜＜循环语句＞|'{'＜语句列＞'}'｜＜有返回值函数调用语句＞;
     |＜无返回值函数调用语句＞;｜＜赋值语句＞;｜＜读语句＞;｜＜写语句＞;｜＜空＞;|＜情况语句＞｜＜返回语句＞;
     */
    if(symbol == "IF"){                         // <条件语句>
        state_condition();
    }
    else if(symbol == "WHILE"){                      //＜循环语句＞
        loop();
    }
    else if(symbol == "LBRACE"){                     //'{'＜语句列＞'}'
        clearQueue();
        getsym_q();
        statelist();
        if(symbol == "RBRACE"){
            clearQueue();
            getsym_q();
            return ;
        }
        else error(25);
    }
    else if(symbol == "IDENT"){
        string tmp_name = string(token);
        getsym_q();
        rcd = q_symbol.back();
        if(rcd == "ASSIGN" || rcd == "LBRACK"){   //＜赋值语句＞;
            assign();
            if(symbol == "SEMI"){
                clearQueue();
                getsym_q();
            }
            else error(28);
        }
        else if(rcd == "LPARENT"){           //＜有/无返回值函数调用语句＞;
            clearQueue();
            clearQueue();
            getsym_q();
            if(symbol != "RPARENT"){
                paralist();
            }
            clearQueue();
            getsym_q();
            if(searchGlo_var(tmp_name)!=nullptr){
                if(searchGlo_var(tmp_name)->type == VOID){
                    insertQuater("call", tmp_name, "", "");
                }
                else{
                    insertQuater("call", tmp_name, "", "");
                }
            }
            else
                error(35);
           
            if(symbol == "SEMI"){
                clearQueue();
                getsym_q();
            }
            else error(28);
        }
        else error(10);
    }
    else if(symbol == "SCANF"){                      //＜读语句＞;
        read();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
        }
        else error(28);
    }
    else if(symbol == "PRINTF"){                     // <写语句>;
        write();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
        }
        else error(28);
    }
    else if(symbol == "SEMI"){                       //＜空＞;
        clearQueue();
        getsym_q();
    }
    else if(symbol == "SWITCH"){                     //＜情况语句＞
        casestate();
    }
    else if(symbol == "RETURN"){                    //＜返回语句＞;
        returnstate();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
        }
        else error(28);
    }
    
    else error(27);
    
    // cout<<symbol<<"*SYNTAX: This is a statement."<<endl;
}

/* <语句列> */
void statelist(){
    //＜语句列＞::=｛＜语句＞｝
    while(symbol != "RBRACE"){
        statement();
    }
    // cout<<symbol<<"*SYNTAX: This is a statement column."<<endl;
}

/* <复合语句> */
void compound(){
    //＜复合语句＞::=[＜常量说明＞][＜变量说明＞]＜语句列＞
    //＜语句列＞::=｛＜语句＞｝
    while(symbol == "CONST"){
        clearQueue();
        getsym_q();
        constDef();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
        }
        else error(28);
    }
    while(symbol=="INT" || symbol=="CHAR"){
        getsym_q();
        rcd = q_symbol.back();
        getsym_q();
        varDef();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
        }
        else error(28);
    }
    //语句列
    statelist();
    // cout<<symbol<<"*SYNTAX: This is a compound statement."<<endl;
}

/* <有返回值函数定义> */
//已经预读了3个单词，所以每次调用这个函数之前，还要先预读两次
void functDef_y(){
    //＜有返回值函数定义＞::= ＜声明头部＞'('＜参数＞')''{'＜复合语句＞'}'
    //＜声明头部＞::=int＜标识符＞|char＜标识符＞
    type_table tmp_sym;
    if(symbol == "INT" || symbol == "CHAR"){
        tmp_tab.position = ll;
        if(symbol == "INT")
            tmp_sym = INT;
        else
            tmp_sym = CHAR;
        clearQueue();
        symbol = q_symbol.front();
        string tmp = q_token.front();
        strcpy(token,tmp.c_str());

        if(symbol == "IDENT"){  //record function name
            functName = string(token);
            insertQuater("begin", string(token), "", "");
            //pre-read
            clearQueue();
            symbol = q_symbol.front();
            string tmp = q_token.front();
            strcpy(token,tmp.c_str());
            
            if(symbol != "LPARENT")
                error(10);
            else{
                isGlobal = false;
                clearQueue();
                getsym_q();
                off_tab = 0;
                parameter();
                if(symbol == "RPARENT"){
                    //log in table: a function with return value
                    tmp_tab.type = tmp_sym;
                    tmp_tab.name = functName;
                    tmp_tab.isFunct = true;
                    tmp_tab.parNum = parNum;
                    parNum = 0;
                    insertTable();
                    clearTmp();
                    //pre-read
                    clearQueue();
                    getsym_q();
                    if(symbol == "LBRACE"){
                        clearQueue();
                        getsym_q();
                        compound();
                        if(symbol != "RBRACE")
                            error(25);
                        else{
                            //pre-read
                            clearQueue();
                            getsym_q();
                            insertQuater("end", functName, "", "");
                            // cout<<symbol<<"*SYNTAX: This is a definition of a function with return value."<<endl;
                        }
                    }
                    else error(24);
                }
                else error(11);
            }
        }
        else error(3);
    }
    else
        error(5);
    
}

/* <无返回值函数定义> */
//已经预读3个单词了，除程序以外，其他函数调用，需先预读两个单词
void functDef_n(){
    //＜无返回值函数定义＞::=void＜标识符＞'('＜参数＞')''{'＜复合语句＞'}'
    if(symbol == "VOID"){
        tmp_tab.type = VOID;
        clearQueue();
        symbol = q_symbol.front();
        string tmp = q_token.front();
        strcpy(token,tmp.c_str());
        
        if(symbol == "IDENT"){
            functName = string(token);
            insertQuater("begin", string(token), "", "");
            //pre-read
            clearQueue();
            symbol = q_symbol.front();
            rcd = q_symbol.back();
            string tmp = q_token.front();
            strcpy(token,tmp.c_str());
            
            if(symbol == "LPARENT"){
                clearQueue();
                getsym_q();
                isGlobal = false;
                off_tab = 0;
                parameter();
                if(symbol == "RPARENT"){
                    //log in table
                    tmp_tab.type = VOID;
                    tmp_tab.name = functName;
                    tmp_tab.isFunct = true;
                    tmp_tab.parNum = parNum;
                    parNum= 0;
                    insertTable();
                    clearTmp();
                    //pre-read
                    clearQueue();
                    getsym_q();
                    if(symbol == "LBRACE"){
                        clearQueue();
                        getsym_q();
                        compound();
                        if(symbol == "RBRACE"){
                            //pre-read
                            clearQueue();
                            getsym_q();
                            insertQuater("end", functName, "", "");
                            // cout<<symbol<<"*SYNTAX: This is a definition of function without return value."<<endl;
                        }
                        else error(25);
                    }
                    else error(24);
                }
                else error(11);
            }
            else error(10);
        }
        else return;    //还有可能是主函数
    }
    else error(29);
}

/* <主函数> */
//已经预读3个单词了，除程序外，其他函数调用时，需先预读2个单词
void funct_main(){
    //＜主函数＞::=void main'('')''{'＜复合语句＞'}'
    if(symbol == "VOID"){
        tmp_tab.type = VOID;
        clearQueue();
        if(symbol == "MAIN"){
            //quater
            functName = string(token);
            insertQuater("begin", "tzx", "", "");
            insertQuater("set", "main", "", "");
            isGlobal = false;
            off_tab = 0;
            //pre-read
            clearQueue();
            symbol = q_symbol.front();
            string tmp = q_token.front();
            strcpy(token,tmp.c_str());
            
            if(symbol == "LPARENT"){
                clearQueue();
                getsym_q();
                if(symbol == "RPARENT"){
                    clearQueue();
                    getsym_q();
                    if(symbol == "LBRACE"){
                        clearQueue();
                        getsym_q();
                        compound();
                        if(symbol == "RBRACE"){
                            //log in table
                            tmp_tab.name = functName;
                            tmp_tab.isFunct = true;
                            insertTable();
                            clearTmp();
                            //pre-read
                            clearQueue();
                            getsym_q();
                            // cout<<symbol<<"*SYNTAX: This is a main function."<<endl;
                        }
                        else error(25);
                    }
                    else error(24);
                }
                else error(11);
            }
            else error(10);
        }
        else return;    //还有可能是无返回值函数定义
    }
    else error(29);
    
}

/* <程序>的分析子程序 */
void program(){
    //＜程序＞::=[＜常量说明＞][＜变量说明＞]{＜有返回值函数定义＞|＜无返回值函数定义＞}＜主函数＞
    //＜常量说明＞::=const＜常量定义＞;{ const＜常量定义＞;}
    insertQuater("global", "", "", "");
    while(symbol == "CONST"){
        isGlobal = true;
        //pre-read
        clearQueue();
        getsym_q();
        constDef();
        if(symbol == "SEMI"){
            clearQueue();
            getsym_q();
            // cout<<symbol<<"*SYNTAX: This is a constant declaration."<<endl;
        }
        else error(28);
    }
    //＜变量说明＞::=＜变量定义＞;{＜变量定义＞;}
    //＜变量定义＞::=＜类型标识符＞(＜标识符＞|＜标识符＞‘[’＜无符号整数＞‘]’){,＜标识符＞|＜标识符＞‘[’＜无符号整数＞‘]’ }
    // <变量说明>和<有返回值函数定义>开头是一样的，需要预读多个单词才能判断
    if (symbol == "VOID") { //无返回值函数或主函数
        getsym_q();
        rcd = q_symbol.back();
        getsym_q();
    }
    while(symbol=="INT" || symbol=="CHAR"){
        isGlobal = true;
        getsym_q(); //IDENT
        rcd = q_symbol.back();
        getsym_q();
        if(q_symbol.back() != "LPARENT"){  //说明是变量定义,已经预读了3个单词
            varDef();
            if(symbol != "SEMI")
                error(28);
            else{
                clearQueue();
                getsym_q();
                if(symbol == "VOID"){   //针对前面有int，后面才是void，不会进入前面的If了，所以要在这里预读两个
                    getsym_q();
                    rcd = q_symbol.back();
                    getsym_q();
                    break;
                }
                // cout<<symbol<<"*SYNTAX: This is a variable declaration."<<endl;
            }
        }
        else{
            break;
        }
    }
    //{＜有返回值函数定义＞|＜无返回值函数定义＞}
    //＜有返回值函数定义＞::=＜声明头部＞'('＜参数＞')''{'＜复合语句＞'}'
    //＜无返回值函数定义＞::=void＜标识符＞'('＜参数＞')''{'＜复合语句＞'}
    //＜主函数＞::=void main'('')''{'＜复合语句＞'}'
    insertQuater("text", "", "", "");
    while(symbol=="INT" || symbol=="CHAR" || symbol=="VOID"){
        if(symbol=="INT" || symbol=="CHAR"){
            functDef_y();   //在上一个while中已经预读了3个，直接调用即可,＜有返回值函数定义＞
            getsym_q();
            rcd = q_symbol.back();
            getsym_q();
        }
        else if(symbol == "VOID"){  // <无返回值函数定义>
            if(rcd == "IDENT"){
                functDef_n();
                getsym_q();
                rcd = q_symbol.back();
                getsym_q();
            }
            else break;
        }
        else break;  //主函数
    }
    //＜主函数＞
    if(symbol == "VOID"){
        if(rcd == "MAIN"){
            funct_main();
        }
        else error(30);
    }
    else error(29);
}

/*syntax analysis*/
void syntax()
{
    while (getsym_q() != 1) {}
    
    program();
    
}

/* scan global */
void scanGlobal()
{
    vector <quater>:: iterator i;
    string tmp;
    for(i=quaternary.begin(); i!=quaternary.end(); i++){
        if(i->op == "global"){
            aim_line.push_back(".data");
            continue;
        }
        //global constant
        else if(i->op == "const"){
            if(i->src1 == "int"){
                tmp = i->obj + ": .word " + i->src2;
                aim_line.push_back(tmp);
            }
            else{   //src1==char
                tmp = i->obj + ": .word " + "\'" + i->src2 + "\'";
                aim_line.push_back(tmp);
            }
        }
        //global variable
        else if(i->op=="int"){
            tmp = i->obj + ": .word " + "0";
            aim_line.push_back(tmp);
        }
        else if(i->op == "char"){
            tmp = i->obj + ": .word " + "0";
            aim_line.push_back(tmp);
        }
        else if(i->op == "text")
            return;
        else if(i->op == "array"){
            tmp = i->obj + ": .space " + i->src2;
            aim_line.push_back(tmp);
        }
    }
}

/* scan string */
void scan_str()
{
    vector <quater>:: iterator i;
    //string tmp;
    for(i=quaternary.begin(); i!=quaternary.end(); i++){
        if(i->op=="write"){
            string str=i->src2.substr(0,4);
            if (str==".str") {
                aim_line.push_back(i->src2 + ": .asciiz \"" + i->src1 + "\"");
            }
        }
    }
}

/* produce aimcode */
void aimcode()
{
    if(ifOp)
        iterateQuater();
    map <string,int> tmp_table;//临时符号表
    vector<string> tmp_par;//临时参数表
    string funct_name;
    int funct_off = 0;
    vector <quater> :: iterator i;
    for(i=quaternary.begin(); i!=quaternary.end(); i++){
        if(i->op == "global"){
            scanGlobal();
            scan_str();
            while (i->op!="text") {
                i++;
            }
            i--;
        }
        else if(i->op == "text"){
            aim_line.push_back(".text");
            aim_line.push_back("lui $s7 0x1001"); //加载立即数到高位,$s7保存.data的基地址
            aim_line.push_back("j main");
        }
        else if(i->op == "begin"){
            funct_off = findMaxoff(i->src1);
            aim_line.push_back(i->src1 + ": ");
            if(i->src1 == "tzx"){
                funct_name = "main";
                funct_off = findMaxoff("main");
                tmp_table.clear();
                continue;
            }
            funct_name = i->src1;
            tmp_table.clear();
        }
        else if(i->op == "end"){
            if(funct_name == "main")
                continue;
            aim_line.push_back("jr $ra");
            funct_off = 0;
        }
        else if(i->op == "assign"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if (i->src1.c_str()[0] == '-' || isdigit(i->src1.c_str()[0])) {
                    aim_line.push_back("li $s1 " + i->src1);
                }
                else{
                    if(searchFunct_var(funct_name, i->src1) != nullptr){
                        item_table* t = searchFunct_var(funct_name, i->src1);
                        off1 = t->offset;
                        aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                    }
                    else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(i->src1);
                        off1 = t->address;
                        aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
            }
            else{   //临时变量，查临时符号表
                int off1 = tmp_table[i->src1];
                aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            //第二个变量
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    if(t->isConst)
                        error(36);
                    else if(t->isFunct)
                        error(37);
                    off2 = t->offset;
                    aim_line.push_back("sw $s1 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->obj)){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    if(t->isConst)
                        error(36);
                    else if(t->isFunct)
                        error(37);
                    off2 = t->address;
                    aim_line.push_back("sw $s1 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->obj);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->obj] = funct_off;
                    aim_line.push_back("sw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->obj];
                    aim_line.push_back("sw $s1 -" + numTOstrs(off2) + "($sp)");
                }
            }
        }
        //local const
        else if(i->op == "const"){
            int off1;
            if(searchFunct_var(funct_name, i->obj) != nullptr){
                item_table* t = searchFunct_var(funct_name, i->obj);
                off1 = t->offset;
                if(i->src1 == "int"){
                    aim_line.push_back("li $s1 " + i->src2);
                }
                else{
                    int ch = i->src2.c_str()[0];
                    aim_line.push_back("li $s1 " + numTOstrs(ch));
                }
                aim_line.push_back("sw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            else if(searchGlo_var(i->obj) != nullptr)
                continue;
            else
                error(2);
        }
        //b-type
        else if(i->op == "lt"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
            }
            //blt
            aim_line.push_back("blt $s1 $s2 " + i->obj);
        }
        else if(i->op == "let"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }

            }
            //ble
            aim_line.push_back("ble $s1 $s2 " + i->obj);
        }
        else if(i->op == "bt"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                
            }
            //bgt
            aim_line.push_back("bgt $s1 $s2 " + i->obj);
        }
        else if(i->op == "bet"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                
            }
            //bge
            aim_line.push_back("bge $s1 $s2 " + i->obj);
        }
        else if(i->op == "beq"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                
            }
            //beq
            aim_line.push_back("beq $s1 $s2 " + i->obj);
        }
        else if(i->op == "bne"){
            int off1, off2;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off1 = tmp_table[i->src1];
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){//变量
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src2];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                
            }
            //bne
            aim_line.push_back("bne $s1 $s2 " + i->obj);
        }
        //arithmetic
        else if(i->op == "add"){
            int off1, off2, off3;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off1 = tmp_table[i->src1];
                aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src2) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off2 = tmp_table[i->src2];
                aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
            }
            //add
            aim_line.push_back("add $s3 $s1 $s2");
            //第三个变量
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off3 = t->offset;
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->obj)){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off3 = t->address;
                    aim_line.push_back("sw $s3 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->obj);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->obj] = funct_off;
                    aim_line.push_back("sw $s3 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->obj];
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
            }

        }
        else if(i->op == "sub"){
            int off1, off2, off3;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                
                else if(strTOnum(i->src1) == 0){
                    aim_line.push_back("li $s1 0");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off1 = tmp_table[i->src1];
                aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src2) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off2 = tmp_table[i->src2];
                aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
            }
            //sub
            aim_line.push_back("sub $s3 $s1 $s2");
            //第三个变量
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off3 = t->offset;
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->obj)){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off3 = t->address;
                    aim_line.push_back("sw $s3 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->obj);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->obj] = funct_off;
                    aim_line.push_back("sw $s3 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->obj];
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
            }

        }
        else if(i->op == "mul"){
            int off1, off2, off3;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off1 = tmp_table[i->src1];
                aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src2) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off2 = tmp_table[i->src2];
                aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
            }
            //mul
            aim_line.push_back("mul $s3 $s1 $s2");
            //第三个变量
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off3 = t->offset;
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->obj)){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off3 = t->address;
                    aim_line.push_back("sw $s3 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->obj);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->obj] = funct_off;
                    aim_line.push_back("sw $s3 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->obj];
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
            }

        }
        else if(i->op == "div"){
            int off1, off2, off3;
            //第一个变量
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off1 = t->offset;
                    aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off1 = t->address;
                    aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off1 = tmp_table[i->src1];
                aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
            }
            //第二个变量
            if(i->src2.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src2) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src2);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                int off2 = tmp_table[i->src2];
                aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
            }
            //div
            aim_line.push_back("div $s3 $s1 $s2");
            //第三个变量
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off3 = t->offset;
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->obj)){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off3 = t->address;
                    aim_line.push_back("sw $s3 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->obj);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->obj] = funct_off;
                    aim_line.push_back("sw $s3 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->obj];
                    aim_line.push_back("sw $s3 -" + numTOstrs(off3) + "($sp)");
                }
            }

        }
        //j
        else if(i->op == "j"){
            aim_line.push_back("j " + i->src1);
        }
        //set label
        else if(i->op == "set"){
            aim_line.push_back(i->src1+":");
        }
        //assign array: []=, =[]
        else if(i->op == "[]="){//[]=,rs,rt,rd -> rd[rs] = rt
            int off1, off2, off3;//存寄存器在内存里的偏移量
            int size;
            bool from_local = false;
            //找rd
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr && searchFunct_var(funct_name, i->obj)->isArray){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off1 = t->offset;
                    from_local = true;
                    aim_line.push_back("addi $s1 $sp -" + numTOstrs(off1));
                }
                else if(searchGlo_var(i->obj)!= nullptr  && searchGlo_var(i->obj)->isArray){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off1 = t->address;
                    from_local = false;
                    aim_line.push_back("addi $s1 $s7 " + numTOstrs(off1));
                }
                else
                    error(2);   //未定义
            }
            else
                error(2);
            //判断rs
            if(i->src1.c_str()[0] == '-' || isdigit(i->src1.c_str()[0])){//数字
                size = 4*strTOnum(i->src1);
                aim_line.push_back("li $s2 " + numTOstrs(size));
            }
            else if(i->src1.c_str()[0] == '.'){//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    aim_line.push_back("mul $s2 $s2 4");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src1];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                    aim_line.push_back("mul $s2 $s2 4");
                }
            }
            else{//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                    aim_line.push_back("mul $s2 $s2 4");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                    aim_line.push_back("mul $s2 $s2 4");
                }
                else
                    error(2);   //未定义
            }
            //找rt
            if(i->src2.c_str()[0] != '.'){
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off3 = t->offset;
                    aim_line.push_back("lw $s3 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off3 = t->address;
                    aim_line.push_back("lw $s3 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("lw $s3 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->src2];
                    aim_line.push_back("lw $s3 -" + numTOstrs(off3) + "($sp)");
                }
            }
            //sw
            if(from_local)
                aim_line.push_back("sub $s1 $s1 $s2");
            else
                aim_line.push_back("add $s1 $s1 $s2");
            aim_line.push_back("sw $s3 0($s1)");
        }
        //=[]  =[],rs,rt,rd -> rt = rd[rs]
        else if(i->op == "=[]"){
            int off1, off2, off3;
            int size;
            bool from_local;
            //找rd
            if(i->obj.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->obj) != nullptr && searchFunct_var(funct_name, i->obj)->isArray){
                    item_table* t = searchFunct_var(funct_name, i->obj);
                    off1 = t->offset;
                    from_local = true;
                    aim_line.push_back("addi $s1 $sp -" + numTOstrs(off1));
                }
                else if(searchGlo_var(i->obj)!=nullptr && searchGlo_var(i->obj)->isArray){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->obj);
                    off1 = t->address;
                    from_local = false;
                    aim_line.push_back("addi $s1 $s7 " + numTOstrs(off1));
                }
                else
                    error(2);   //未定义
            }
            else
                error(2);
            //判断rs
            if(i->src1.c_str()[0] == '-' || isdigit(i->src1.c_str()[0])){//数字
                size = 4*strTOnum(i->src1);
                aim_line.push_back("li $s2 " + numTOstrs(size));
            }
            else if(i->src1.c_str()[0] == '.'){//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("lw $s2 -" + numTOstrs(funct_off) + "($sp)");
                    aim_line.push_back("mul $s2 $s2 4");
                    funct_off += 4;
                }
                else{
                    off2 = tmp_table[i->src1];
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                    aim_line.push_back("mul $s2 $s2 4");
                }
            }
            else{//变量
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off2 = t->offset;
                    aim_line.push_back("lw $s2 -" + numTOstrs(off2) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off2 = t->address;
                    aim_line.push_back("lw $s2 " + numTOstrs(off2) + "($s7)");
                    aim_line.push_back("mul $s2 $s2 4");
                }
                else
                    error(2);   //未定义
            }
            //找rt
            if(i->src2.c_str()[0] != '.'){
                if(searchFunct_var(funct_name, i->src2) != nullptr){//找局部
                    item_table* t = searchFunct_var(funct_name, i->src2);
                    off3 = t->offset;
                    aim_line.push_back("addi $s3 $sp -" + numTOstrs(off3));
                }
                else if(searchGlo_var(i->src2) != nullptr){//找全局
                    item_table* t = searchGlo_var(i->src2);
                    off3 = t->address;
                    aim_line.push_back("add $s3 $s7 " + numTOstrs(off3));
                }
                else
                    error(2);
            }
            else{//临时变量
                map<string,int>:: iterator k = tmp_table.find(i->src2);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src2] = funct_off;
                    aim_line.push_back("addi $s3 $sp -" + numTOstrs(funct_off));
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->src2];
                    aim_line.push_back("addi $s3 $sp -" + numTOstrs(off3));
                }
            }
            //sw
            if(from_local)
                aim_line.push_back("sub $s1 $s1 $s2");
            else
                aim_line.push_back("add $s1 $s1 $s2");
            aim_line.push_back("lw $s1 0($s1)");//取值
            aim_line.push_back("sw $s1 0($s3)");
        }
        //push
        else if(i->op == "push"){
            tmp_par.push_back(i->src1);//参数名压入参数表
        }
        //call function
        else if(i->op == "call"){
            vector<string>:: iterator j;
            int off1, off2;
            int par_num = 0;
            for(j=tmp_par.begin(); j!=tmp_par.end(); j++){
                if(j->c_str()[0] != '.'){//变量
                    if(searchFunct_var(funct_name, *j) != nullptr){
                        item_table* t = searchFunct_var(funct_name, *j);
                        off1 = t->offset;
                        aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                    }
                    else if(searchGlo_var(*j)){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(*j);
                        off1 = t->address;
                        aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
                else{//临时变量作参数
                    map<string,int>:: iterator k = tmp_table.find(*j);
                    if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                        tmp_table[*j] = funct_off;
                        aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                        funct_off += 4;
                    }
                    else{
                        off2 = tmp_table[*j];
                        aim_line.push_back("lw $s1 -" + numTOstrs(off2) + "($sp)");
                    }
                }
                //$s2到了参数开始的地方
                aim_line.push_back("addi $s2 $sp -" + numTOstrs(funct_off+4+par_num*4));
                aim_line.push_back("sw $s1 0($s2)");
                par_num++;
            }
            if(par_num != searchGlo_var(i->src1)->parNum){
                error(38);
                continue;
            }
            aim_line.push_back("addi $sp $sp -" + numTOstrs(funct_off));
            aim_line.push_back("sw $ra 0($sp)");
            aim_line.push_back("addi $sp $sp -4");
            
            aim_line.push_back("jal " + i->src1);
            //函数调用完成，要跳转回来了
            aim_line.push_back("addi $sp $sp 4");
            aim_line.push_back("lw $ra 0($sp)");
            aim_line.push_back("addi $sp $sp " + numTOstrs(funct_off));
            tmp_par.clear();
        }
        else if(i->op == "callre"){
            vector<string>:: iterator j;
            int off1, off2, off3;
            int par_num = 0;
            for(j=tmp_par.begin(); j!=tmp_par.end(); j++){
                if(j->c_str()[0] != '.'){//变量
                    if(searchFunct_var(funct_name, *j) != nullptr){
                        item_table* t = searchFunct_var(funct_name, *j);
                        off1 = t->offset;
                        aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                    }
                    else if(searchGlo_var(*j) != nullptr){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(*j);
                        off1 = t->address;
                        aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
                else{//临时变量作参数
                    map<string,int>:: iterator k = tmp_table.find(*j);
                    if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                        tmp_table[*j] = funct_off;
                        aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                        funct_off += 4;
                    }
                    else{
                        off2 = tmp_table[*j];
                        aim_line.push_back("lw $s1 -" + numTOstrs(off2) + "($sp)");
                    }
                }
                //$s2到了参数开始的地方
                aim_line.push_back("addi $s2 $sp -" + numTOstrs(funct_off+4+par_num*4));
                aim_line.push_back("sw $s1 0($s2)");
                par_num++;
            }
            if(par_num != searchGlo_var(i->obj)->parNum){
                error(38);
                continue;
            }
            aim_line.push_back("addi $sp $sp -" + numTOstrs(funct_off));
            aim_line.push_back("sw $ra 0($sp)");
            aim_line.push_back("addi $sp $sp -4");
            
            aim_line.push_back("jal " + i->obj);
            //函数调用完成，要跳转回来了
            aim_line.push_back("addi $sp $sp 4");
            aim_line.push_back("lw $ra 0($sp)");
            aim_line.push_back("addi $sp $sp " + numTOstrs(funct_off));
            //判断函数的返回值
            if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                if(searchFunct_var(funct_name, i->src1) != nullptr){
                    item_table* t = searchFunct_var(funct_name, i->src1);
                    off3 = t->offset;
                    aim_line.push_back("sw $v0 -" + numTOstrs(off3) + "($sp)");
                }
                else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                    item_table* t = searchGlo_var(i->src1);
                    off3 = t->address;
                    aim_line.push_back("sw $v0 " + numTOstrs(off3) + "($s7)");
                }
                else
                    error(2);   //未定义
            }
            else{   //临时变量，查临时符号表
                map<string,int>:: iterator k = tmp_table.find(i->src1);
                if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                    tmp_table[i->src1] = funct_off;
                    aim_line.push_back("sw $v0 -" + numTOstrs(funct_off) + "($sp)");
                    funct_off += 4;
                }
                else{
                    off3 = tmp_table[i->src1];
                    aim_line.push_back("sw $v0 -" + numTOstrs(off3) + "($sp)");
                }
            }
            tmp_par.clear();

        }
        //return
        else if(i->op == "return"){
            int off1;
            if(funct_name == "main")
                continue;
            //先判断有没有return的东西
            if(i->src1 == ""){
                aim_line.push_back("jr $ra");
            }
            else{
                if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                    if(searchFunct_var(funct_name, i->src1) != nullptr){
                        item_table* t = searchFunct_var(funct_name, i->src1);
                        off1 = t->offset;
                        aim_line.push_back("lw $v0 -" + numTOstrs(off1) + "($sp)");
                    }
                    else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(i->src1);
                        off1 = t->address;
                        aim_line.push_back("lw $v0 " + numTOstrs(off1) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
                else{   //临时变量，查临时符号表
                    map<string,int>:: iterator k = tmp_table.find(i->src1);
                    if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                        tmp_table[i->src1] = funct_off;
                        aim_line.push_back("lw $v0 -" + numTOstrs(funct_off) + "($sp)");
                        funct_off += 4;
                    }
                    else{
                        off1 = tmp_table[i->src1];
                        aim_line.push_back("lw $v0 -" + numTOstrs(off1) + "($sp)");
                    }
                }
                aim_line.push_back("jr $ra");
            }
        }
        //read
        else if(i->op == "read"){
            if(searchFunct_var(funct_name, i->src1) != nullptr){//找局部
                if(searchFunct_var(funct_name, i->src1)->type == INT || searchFunct_var(funct_name, i->src1)->type == PAR_INT){
                    aim_line.push_back("li $v0 5");
                    aim_line.push_back("syscall");
                    aim_line.push_back("sw $v0 -" + numTOstrs(searchFunct_var(funct_name, i->src1)->offset) + "($sp)");
                }
                else if(searchFunct_var(funct_name, i->src1)->type == CHAR || searchFunct_var(funct_name, i->src1)->type == PAR_CHAR){
                    aim_line.push_back("li $v0 12");
                    aim_line.push_back("syscall");
                    aim_line.push_back("sw $v0 -" + numTOstrs(searchFunct_var(funct_name, i->src1)->offset) + "($sp)");
                }
                else
                    error(38);
            }
            else if(searchGlo_var(i->src1) != nullptr){//找全局
                if(searchGlo_var(i->src1)->type == INT){
                    aim_line.push_back("li $v0 5");
                    aim_line.push_back("syscall");
                    aim_line.push_back("sw $v0 " + numTOstrs(searchGlo_var(i->src1)->address) + "($s7)"); //DEBUG: 全局地址增加不是减，起始寄存器是$s7
                }
                else if(searchGlo_var(i->src1)->type == CHAR){
                    aim_line.push_back("li $v0 12");
                    aim_line.push_back("syscall");
                    aim_line.push_back("sw $v0 " + numTOstrs(searchGlo_var(i->src1)->address) + "($s7)");
                }
                else
                    error(38);
            }
            else
                error(2);
        }
        //write
        else if(i->op == "write"){
            int off1, off2;
            if(i->src2 == "int"){
                if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                    if(searchFunct_var(funct_name, i->src1) != nullptr){
                        item_table* t = searchFunct_var(funct_name, i->src1);
                        off1 = t->offset;
                        aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                    }
                    else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(i->src1);
                        off1 = t->address;
                        aim_line.push_back("lw $s1 " + numTOstrs(off1) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
                else{   //临时变量，查临时符号表
                    map<string,int>:: iterator k = tmp_table.find(i->src1);
                    if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                        tmp_table[i->src1] = funct_off;
                        aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                        funct_off += 4;
                    }
                    else{
                        off1 = tmp_table[i->src1];
                        aim_line.push_back("lw $s1 -" + numTOstrs(off1) + "($sp)");
                    }
                }
                    aim_line.push_back("li $v0 1");
                    aim_line.push_back("move $a0 $s1");
                    aim_line.push_back("syscall");
            }
            else if(i->src2 == "char"){
                if(i->src1.c_str()[0] != '.'){  //说明是一个变量，查函数的符号表，如果没找到，再找全局的符号表
                    if(searchFunct_var(funct_name, i->src1) != nullptr){
                        item_table* t = searchFunct_var(funct_name, i->src1);
                        off2 = t->offset;
                        aim_line.push_back("lw $s1 -" + numTOstrs(off2) + "($sp)");
                    }
                    else if(searchGlo_var(i->src1) != nullptr){    //如果是全局的，从$s7开始偏移
                        item_table* t = searchGlo_var(i->src1);
                        off2 = t->address;
                        aim_line.push_back("lw $s1 " + numTOstrs(off2) + "($s7)");
                    }
                    else
                        error(2);   //未定义
                }
                else{   //临时变量，查临时符号表
                    map<string,int>:: iterator k = tmp_table.find(i->src1);
                    if(k == tmp_table.end()){   //没找到，第二个变量是新定义的
                        tmp_table[i->src1] = funct_off;
                        aim_line.push_back("lw $s1 -" + numTOstrs(funct_off) + "($sp)");
                        funct_off += 4;
                    }
                    else{
                        off2 = tmp_table[i->src1];
                        aim_line.push_back("lw $s1 -" + numTOstrs(off2) + "($sp)");
                    }
                }
                aim_line.push_back("li $v0 11");
                aim_line.push_back("move $a0 $s1");
                aim_line.push_back("syscall");
            }
            else if(i->src2.c_str()[0] == '.'){
                aim_line.push_back("la $a0 " + i->src2);
                aim_line.push_back("li $v0 4");
                aim_line.push_back("syscall");
            }
            else
                error(2);
        }
    }
}


/* main */

int main()
{
    //read file
    string cpath;
    cout << "Please input the file path: " << endl;
    cin >> cpath;
    file.open(cpath);
    ofstream tabfile;
    ofstream quaterfile;
    ofstream aimcodefile;
    if(!file){
        cout<<"Open Error!"<<endl;
    }
    else if(file.eof()){
        cout<<"End of File!"<<endl;
    }
    else{
        cout<<"Please set the optimization on-off. On:1. Off:other key."<<endl;
        cin>>ifOp;
        syntax();
        aimcode();
    }
    
    
    //打印符号表
    tabfile.open("tabfile.txt");
    vector<item_table>:: iterator i;
    for(i=symTab.begin(); i!=symTab.end(); i++){
        tabfile<<"name: "<<i->name<<'\t'<<"type: "<<i->type<<'\t'<<"size: "<<i->size<<'\t'<<"value: "<<i->value<<'\t'<<"functBelong: "<<i->functBelong<<'\t'<<"position: "<<i->position<<'\t'<<"address: "<<i->address<<'\t'<<"offset: "<<i->offset<<endl;
    }
    
    //打印四元式
    quaterfile.open("quaterfile.txt");
    vector<quater>:: iterator j;
    for(j=quaternary.begin(); j!=quaternary.end(); j++){
        quaterfile<<j->op<<'\t'<<'\t'<<j->src1<<'\t'<<'\t'<<j->src2<<'\t'<<'\t'<<j->obj<<endl;
    }
    
    //打印目标代码
    aimcodefile.open("aimcode.txt");
    vector<string>:: iterator k;
    for(k=aim_line.begin(); k!=aim_line.end(); k++){
        aimcodefile<<*k<<endl;
    }
    
    file.close();
    tabfile.close();
    quaterfile.close();
    return 0;
}

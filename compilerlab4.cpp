#include <set>
#include <regex>
#include <stack>
#include <string>
#include <iostream>
using namespace std;

// lexical analysis
bool lexical_debug=false;
bool parse_debug=false;
bool out2file=false;
vector<regex> regex_array;
string s;
int priority(string s);
struct token{
    int type;
    int prio;
    string content;
    token(int t, string s):type(t), content(s){prio=priority(s);}
};
vector<token> token_stream;
// assembly language
struct frame{  //a frame of the particular function
    int shift;  //variable address shift according to ebp
    string ret_type;
    map<string, int> address;  //variable address
    frame(){shift=0;}  //shift is initialized to 0
    string get_address(string var){
        int ret=address[var];
        return ret>0?"+"+to_string(ret):to_string(ret);
    }
};
set<string> func;
int if_cnt = 0, while_cnt = 0;  //used for label jumping
stack<string> while_label;

void init(){
    //keywords
    regex_array.push_back(regex("int|void|return|if|else|while|continue|break"));
    //identifiers
    regex_array.push_back(regex("[[:alpha:]_][[:alnum:]_]*"));
    //numbers
    regex_array.push_back(regex("[[:digit:]]+"));
    //operators <=, >= and == should be combined seperately
    regex_array.push_back(regex(R"(=|\+|-|\*|\/|%|<|<=|>|>=|==|!=|&|\||\^|\(|\)|&&|\|\||!|~)"));
    //seperators
    regex_array.push_back(regex(R"(;|\{|\}|,)"));
}

void lexical_analysis(){  //output lexical tokens
    while (cin>>s){
        while (s != ""){
            string res="";
            smatch match;
            int array_len = regex_array.size(), t;
            for (int i=0; i<array_len; ++i){
                if (regex_search(s, match, regex_array[i])){
                    if (match.position(0) != 0) continue;
                    res = match[0];
                    t = i;
                    break;
                }
            }
            if (res=="") throw "lexical analysis error";
            s = s.substr(res.length());
            if (!token_stream.empty()){
                string back = token_stream.back().content;
                if (back=="<"||back==">"||back=="=")
                    if (res=="="){
                        token_stream.pop_back();
                        res = back+res;
                    }
                if (back=="&"&&res=="&"||back=="|"&&res=="|"){
                    token_stream.pop_back();
                    res = back+res;
                }
            }
            token_stream.push_back(token(t, res));
        }
    }
    if (lexical_debug==true){
        for (auto x:token_stream)
            cout<<"debug:"<<x.type<<" "<<x.content<<endl;
    }
}

int priority(string s){  //determine the priority of operators
    if (s==";"||s==",") return -1;
    if (s==")") return 0;
    if (s=="||") return 1;
    if (s=="&&") return 2;
    if (s=="|") return 3;
    if (s=="^") return 4;
    if (s=="&") return 5;
    if (s=="=="||s=="!=") return 6;
    if (s=="<"||s=="<="||s==">"||s==">=") return 7;
    if (s=="+"||s=="-") return 8;
    if (s=="*"||s=="/"||s=="%") return 9;
    if (s=="!"||s=="~") return 10;  //unary operator
    if (s=="(") return 11;
    return -1;
}

string parse_exp(frame *cur_frame, int &p);
//call a function, where p points to the name of function previously, and the character after ")" afterwards
string call_func(frame *cur_frame, int &p){
    string result;
    string func_name=token_stream[p].content;
    if (func_name=="println_int") func_name="printf";
    p+=2;  //p is on the token after "("
    string arg_code;
    int arg_num=0;
    while (token_stream[p-1].content!=")"){
        arg_code=parse_exp(cur_frame, p)+arg_code;  //push the argument reversely
        arg_num++;
    }
    if (func_name=="printf"){
        arg_code+="push offset format_str\n";
        arg_num++;
    }
    result+=arg_code;
    result+="call "+func_name+"\n";
    result+="add esp, "+to_string(arg_num*4)+"\n";
    return result;
}

//synchronize the memory stack and the abstract stack
//in the end, remain a temporary value in memory stack, 
//  p points to the token after "(" previously, and
//  p points to the token after ")"(control statement or function call), "," or ";"(assignment or return)
string parse_exp(frame *cur_frame, int &p){  
    string result;
    stack<token> oprt, opnd;
    int parenthesis=0;
    while (true){
        auto &t=token_stream[p];
        //cout<<t.content<<endl;
        if (t.type==3&&token_stream[p-1].type>=3){  //unary operator
            if (token_stream[p-1].content!=")"){  //no ) will appear before an unary operator
                if (t.content=="-") t.prio=10;  //unary -
            }
        }
        if (t.type==3||t.type==4){  //operator or seperator
            while (oprt.size()&&(oprt.top().prio>=t.prio)){
                if (oprt.top().content=="("){  //deal with (
                    if (t.content==")") oprt.pop();
                    break;
                }
                if (oprt.top().prio==10){  //unary operator
                    result+="pop eax\n";
                    opnd.pop();
                    string t=oprt.top().content;
                    if (t=="-") result+="neg eax\n";
                    if (t=="!") result+="cmp eax, 0\nsete cl\nmovzx eax, cl\n";
                    if (t=="~") result+="not eax\n";
                } else {  //binary operator
                    result+="pop ebx\npop eax\n";
                    opnd.pop(); opnd.pop();
                    string t=oprt.top().content;
                    //cout<<t<<endl;
                    if (t=="+") result+="add eax, ebx\n";
                    if (t=="-") result+="sub eax, ebx\n";
                    if (t=="*") result+="imul eax, ebx\n";
                    if (t=="/") result+="cdq\nidiv ebx\n";
                    if (t=="%"){
                        result+="cdq\nidiv ebx\n";
                        result+="mov eax, edx\n";  //quotient in eax, remainder in edx
                    }

                    if (t=="<"||t=="<="||t==">"||t==">="||t=="=="|t=="!=")  //compare
                        result+="cmp eax, ebx\n";
                    if (t=="<") result+="setl cl\n";
                    if (t=="<=") result+="setle cl\n";
                    if (t==">") result+="setg cl\n";
                    if (t==">=") result+="setge cl\n";
                    if (t=="==") result+="sete cl\n";
                    if (t=="!=") result+="setne cl\n";
                    if (t=="<"||t=="<="||t==">"||t==">="||t=="=="|t=="!=")  //compare
                        result+="movzx eax, cl\n";

                    if (t=="&&"||t=="||"){
                        result+="cmp eax, 0\nsetne cl\nmovzx eax, cl\n";
                        result+="cmp ebx, 0\nsetne cl\nmovzx ebx, cl\n";
                    }
                    
                    if (t=="|"||t=="||") result+="or eax, ebx\n";
                    if (t=="&"||t=="&&") result+="and eax, ebx\n";
                    if (t=="^") result+="xor eax, ebx\n";
                }

                oprt.pop();
                result+="push eax\n";
                opnd.push(token(-1, ""));  //placeholder
            }
            if (token_stream[p].content!=")") oprt.push(token_stream[p]);
            if (t.content=="(") parenthesis++;
            if (t.content==")") parenthesis--;
            p++;
        } else {
            if (t.type==2){  //numbers
                result+="mov eax, "+t.content+"\n";
                opnd.push(token_stream[p++]);
            }
            else if (func.find(t.content)!=func.end()){  //function calls
                result+=call_func(cur_frame, p);
                opnd.push(token(-1, ""));  //placeholder
            } else {  //variables
                result+="mov eax, DWORD PTR [ebp"+cur_frame->get_address(t.content)+"]\n";
                opnd.push(token_stream[p++]);
            }
            result+="push eax\n";
        }
        //end of expression
        if (token_stream[p-1].type==4) break;
        if (parenthesis<0) break;  //the end of a control statement or function call
    }
    return result;
}

//find all the functions in the program
string find_function(){
    string result;
    int p=0;
    while (p<token_stream.size()-1){
        if (token_stream[p].type==1&&token_stream[p+1].content=="("){
            string func_name=token_stream[p].content;
            func.insert(func_name);
            if (func_name!="println_int")
                result+=".global "+token_stream[p].content+"\n";
        }
        p++;
    }
    result+=".data\nformat_str:\n.asciz \"%d\\n\"\n.extern printf\n.text\n";  //special function "println_int"
    return result;
}

//deal with the sentence like "a=1;" or "a=1," where p points to "a" previously and the character behind "," or ";" afterwards
string assignment(frame *cur_frame, int &p){
    string result;
    string var_name=token_stream[p].content;
    p+=2;
    result+=parse_exp(cur_frame, p);
    result+="pop eax\n";
    result+="mov DWORD PTR [ebp"+cur_frame->get_address(var_name)+"], eax\n";
    return result;
}

//deal with a code block, where p points to "{" previously, and the character after "}" afterwards
string parse_block(frame *father_frame, int &p){
    p++;
    frame *cur_frame = new frame();
    *cur_frame = *father_frame;  //temporal frame for inner code block
    string result="";
    while (token_stream[p].content!="}"){
        if (token_stream[p].type==0){  //indicate variable definition, returning from a function, or control statements
            if (token_stream[p].content=="int"){  //variable definition
                p++;
                while (token_stream[p-1].content!=";"){  //dealing with multiple variables
                    result+="push 0\n";  //make esp-=4 manually
                    cur_frame->shift-=4;
                    cur_frame->address[token_stream[p].content]=cur_frame->shift;
                    if (token_stream[p+1].content=="=")  //assignment with definition
                        result+=assignment(cur_frame, p);
                    else p+=2;  //handle ";"
                }
            }
            if (token_stream[p].content=="return"){  //return an expression
                p++;
                result+=parse_exp(cur_frame, p);
                result+="pop eax\n";
                result+="leave\nret\n";
            }
            if (token_stream[p].content=="if"){
                p+=2;
                string id=to_string(if_cnt++);
                result+=".if_"+id+"_begin:\n";  // label of the begin of "if" block
                result+=parse_exp(cur_frame, p);
                result+="pop eax\ncmp eax, 0\n";
                result+="je .if_"+id+"_end\n";
                result+=parse_block(cur_frame, p);
                result+="jmp .else_"+id+"_end\n";
                result+=".if_"+id+"_end:\n";  // label of the end of "if" block
                if (token_stream[p].content=="else"){
                    p++;
                    result+=parse_block(cur_frame, p);
                }
                result+=".else_"+id+"_end:\n";  // label of the end of "else" block
            }
            if (token_stream[p].content=="while"){
                p+=2;
                string id=to_string(while_cnt++);
                result+=".while_"+id+"_begin:\n";  // label of the begin of "while" block
                result+=parse_exp(cur_frame, p);
                result+="pop eax\ncmp eax, 0\n";
                result+="je .while_"+id+"_end\n";
                while_label.push(id);
                result+=parse_block(cur_frame, p);
                result+="jmp .while_"+id+"_begin\n";
                result+=".while_"+id+"_end:\n";  // label of the end of "while" block
                while_label.pop();
            }
            if (token_stream[p].content=="continue"){
                string id=while_label.top();
                result+="jmp .while_"+id+"_begin\n";
                p+=2;
            }
            if (token_stream[p].content=="break"){
                string id=while_label.top();
                result+="jmp .while_"+id+"_end\n";
                p+=2;
            }
        }
        if (token_stream[p].type==1){  //indicate assigning a variable or calling a function
            if (func.find(token_stream[p].content)==func.end()){  //assignment
                result+=assignment(cur_frame, p);
            } else {  //function call
                result+=call_func(cur_frame, p);
                p++;  //handle ";"
            }
        }
    }
    p++;
    delete cur_frame;
    return result;
}

//deal with a function, where p points to the return type previously, and the character after "}" afterwards
string parse_function(int &p){
    string result="";
    string func_name=token_stream[p+1].content;
    frame *cur_frame=new frame();
    cur_frame->ret_type=token_stream[p].content;
    result+=func_name+":\n";
    result+="push ebp\nmov ebp, esp\n";
    p+=2;  //p points to "("
    int up_shift=8;
    while (token_stream[p].content!=")"){  //deal with the address of parameters(in the previous frame)
        if (token_stream[p+1].content==")"){  //zero parameter
            p++;
            break;
        }
        cur_frame->address[token_stream[p+2].content]=up_shift;
        up_shift+=4;
        p+=3;
    }
    p++;  //points to the character "{"
    //deal with the body of this function
    result+=parse_block(cur_frame, p);
    if (cur_frame->ret_type=="void") result+="leave\nret\n";  //may be redundant for complex functions
    if (parse_debug) cout<<result<<endl;
    delete cur_frame;
    return result;
}

//continuing parsing functions
//for example, if the function is "void func(){}", then p points to "void" previously, and the character after "}" afterwards;
string parse(){
    string result=".intel_syntax noprefix\n";
    result+=find_function();
    int p=0;
    while (p<token_stream.size()){
        result+="\n"+parse_function(p);
    }
    return result;
}

int main(int argc, char *argv[]){
    if (argc!=2){  //read input file
        return 0;
    }
    freopen(argv[1], "r", stdin);
    if (lexical_debug==true){
        freopen((string(argv[1])+".token").c_str(), "w", stdout);
    }
    init();
    string result;
    try{
        lexical_analysis();
        fclose(stdin);
        result=parse();
        if (out2file){
            string filename=string(argv[1]);
            filename = filename.substr(0, filename.find_last_of("."));
            freopen((filename+".s").c_str(), "w", stdout);
            cout<<result;
            fclose(stdout);
        }
        else cout<<result<<endl;
    }
    catch(const char* msg){
        cerr<<msg<<endl;
    }
    return 0;
}
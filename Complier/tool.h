//
//  tool.h
//  compiler design
//
//  Created by Macbook on 30/11/2016.
//  Copyright © 2016 Macbook. All rights reserved.
//

#ifndef tool_h
#define tool_h
#include <sstream>

using namespace std;


inline int strTOnum(std::string str)
{
    int i;
    std::stringstream ss;
    ss << str;
    ss >> i;
    return i;
}

inline std::string numTOstrs(int num)
{
    std::string i;
    std::stringstream ss;
    ss << num;
    ss >> i;
    return i;
}

#endif /* tool_h */

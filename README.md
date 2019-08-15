# A-Compiler-for-C

This is a simple compiler for C, which can convert C codes to MIPS assembling codes.

- Target strcuture: `MIPS`

- Use `Mars 4.5`  for excuting MIPS code
- `aimcode.txt`  is an example of aimcode that generates by compiler.

### Structures

- The codes of compiler are contained by `main.cpp` and `tool.h`. 
- `main.cpp` includes **lexical analysis**, **grammar analysis**, **symbol table**, **intermediate code generation**, **aimcode generation** and **optimization for intermediate code**.
- `tool.h` includes tool functions that used in `main.cpp`




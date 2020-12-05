void main() {
  int i;
  for(i = 0; i < 1000000; i++){
    asm(
      // 4 two cycle stalls for q1, 1 one cycle stalls q1 
      // 1 two cycle stalls for q2, 2 one cycle stalls q2
      "addi $4, $0, 1  \n \t "
      "addi $5, $0, 1  \n \t " 
      "add $3, $4, $0  \n \t " // 1 cycle q1 
      "add $5, $4, $3  \n \t " // 2 cycle q1, 1 cycle q2
      "add $6, $4, $3  \n \t " // no q1 stall b/c eaten up by prev. instr.
      "addi $6, $0, 1  \n \t "
      "add $4, $6, $0  \n \t " // 2 cycle q1, 1 cycle q2
      "addi $6, $0, 1  \n \t "
      "lw $7, 0($3)    \n \t "
      "sub $5, $7, $3  \n \t " // 2 cycle q1, 2 cycle q2
      "lw $7, 0($3)    \n \t "
      "sw $7, 0($1)    \n \t " // 2 cycle q1, 0 q2
      "add $6, $0, 6  \n \t "
      );
  }  
}

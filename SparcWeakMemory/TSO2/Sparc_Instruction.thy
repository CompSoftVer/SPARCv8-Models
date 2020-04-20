 \<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
  \<close>

text {* SPARC instruction model *}
theory Sparc_Instruction
  imports Main State 
begin
  
text{*
This theory provides a formal model for assembly instruction to be executed in the model.

Unlike the formal model of SPARCv8 ISA (small-step semantics), here we work on a 
higher level and provide big-step semantics.

We don't consider ASI here. We only support instructions that access ASI = 10, 11. *}

primrec get_operand_w5::"inst_operand \<Rightarrow> word5"
where "get_operand_w5 (W5 r) = r"

primrec get_operand_w30::"inst_operand \<Rightarrow> word30"
where "get_operand_w30 (W30 r) = r"

primrec get_operand_w22::"inst_operand \<Rightarrow> word22"
where "get_operand_w22 (W22 r) = r"

primrec get_operand_cond::"inst_operand \<Rightarrow> word4"
where "get_operand_cond (Cond r) = r"

primrec get_operand_flag::"inst_operand \<Rightarrow> word1"
where "get_operand_flag (Flag r) = r"

primrec get_operand_simm13::"inst_operand \<Rightarrow> word13"
where "get_operand_simm13 (Simm13 r) = r"

primrec get_operand_opf::"inst_operand \<Rightarrow> word9"
where "get_operand_opf (Opf r) = r"

primrec get_operand_imm7:: "inst_operand \<Rightarrow> word7"
where "get_operand_imm7 (Imm7 r) = r"
    
primrec get_operand_asi:: "inst_operand \<Rightarrow> word8"
where "get_operand_asi (Asi r) = r"    

definition get_op::"word32 \<Rightarrow> int"
where "get_op w \<equiv> uint (w >> 30)"

definition get_op2::"word32 \<Rightarrow> int"
where "get_op2 w \<equiv> 
  let mask_op2 = 0b00000001110000000000000000000000 in
  uint ((bitAND mask_op2 w) >> 22)"

definition get_op3::"word32 \<Rightarrow> int"
where "get_op3 w \<equiv> 
  let mask_op3 = 0b00000001111110000000000000000000 in 
  uint ((bitAND mask_op3 w) >> 19)"

definition get_disp30::"word32 \<Rightarrow> int"
where "get_disp30 w \<equiv> 
  let mask_disp30 = 0b00111111111111111111111111111111 in
  uint (bitAND mask_disp30 w)"

definition get_a::"word32 \<Rightarrow> int"
where "get_a w \<equiv>
  let mask_a = 0b00100000000000000000000000000000 in
  uint ((bitAND mask_a w) >> 29)"

definition get_cond::"word32 \<Rightarrow> int"
where "get_cond w \<equiv>
  let mask_cond = 0b00011110000000000000000000000000 in
  uint ((bitAND mask_cond w) >> 25)"

definition get_disp_imm22::"word32 \<Rightarrow> int"
where "get_disp_imm22 w \<equiv>
  let mask_disp_imm22 = 0b00000000001111111111111111111111 in
  uint (bitAND mask_disp_imm22 w)"

definition get_rd::"word32 \<Rightarrow> int"
where "get_rd w \<equiv>
  let mask_rd = 0b00111110000000000000000000000000 in
  uint ((bitAND mask_rd w) >> 25)"

definition get_rs1::"word32 \<Rightarrow> int"
where "get_rs1 w \<equiv>
  let mask_rs1 = 0b00000000000001111100000000000000 in
  uint ((bitAND mask_rs1 w) >> 14)"

definition get_i::"word32 \<Rightarrow> int"
where "get_i w \<equiv>
  let mask_i = 0b00000000000000000010000000000000 in
  uint ((bitAND mask_i w) >> 13)"

definition get_opf::"word32 \<Rightarrow> int"
where "get_opf w \<equiv> 
  let mask_opf = 0b00000000000000000011111111100000 in
  uint ((bitAND mask_opf w) >> 5)"

definition get_rs2::"word32 \<Rightarrow> int"
where "get_rs2 w \<equiv>
  let mask_rs2 = 0b00000000000000000000000000011111 in
  uint (bitAND mask_rs2 w)"

definition get_simm13::"word32 \<Rightarrow> int"
where "get_simm13 w \<equiv>
  let mask_simm13 = 0b00000000000000000001111111111111 in
  uint (bitAND mask_simm13 w)"

definition get_asi::"word32 \<Rightarrow> int"
where "get_asi w \<equiv>
  let mask_asi = 0b00000000000000000001111111100000 in
  uint ((bitAND mask_asi w) >> 5)"

definition get_trap_cond:: "word32 \<Rightarrow> int"
where "get_trap_cond w \<equiv>
  let mask_cond = 0b00011110000000000000000000000000 in
  uint ((bitAND mask_cond w) >> 25)"

definition get_trap_imm7:: "word32 \<Rightarrow> int"
where "get_trap_imm7 w \<equiv>
  let mask_imm7 = 0b00000000000000000000000001111111 in
  uint (bitAND mask_imm7 w)"

text {* Parse type 1 instructions (CALL), with a single operand disp30+"00". 
We currently don't support CALL, but we add this function for 
future extensibility. *}  
  
definition parse_instr_f1::"word32 \<Rightarrow> instruction option" where 
"parse_instr_f1 w \<equiv> Some (call_type CALL,[W30 (word_of_int (get_disp30 w))])"   

text {* Parse type 2 instructions (SETHI, NOP, and branching instructions). *}

definition parse_instr_f2::"word32 \<Rightarrow> instruction option" where
"parse_instr_f2 w \<equiv>
  let op2 = get_op2 w in
  if op2 = uint(0b100::word3) then \<comment>\<open> SETHI or NOP \<close>
    let rd = get_rd w in
    let imm22 = get_disp_imm22 w in
    if rd = 0 \<and> imm22 = 0 then \<comment>\<open> NOP \<close>
      Some (nop_type NOP,[])
    else \<comment>\<open> SETHI, with operands [imm22,rd] \<close>
      Some (sethi_type SETHI,[(W22 (word_of_int imm22)), (W5 (word_of_int rd))])
  else if op2 = uint(0b010::word3) then \<comment>\<open> Bicc, with operands [a,disp22]  \<close>
    let cond = get_cond w in
    let flaga = Flag (word_of_int (get_a w)) in
    let disp22 = W22 (word_of_int (get_disp_imm22 w)) in
    if cond = uint(0b0001::word4) then \<comment>\<open> BE \<close>
      Some (bicc_type BE,[flaga,disp22])
    else if cond = uint(0b1001::word4) then \<comment>\<open> BNE \<close>
      Some (bicc_type BNE,[flaga,disp22])
    else if cond = uint(0b1100::word4) then \<comment>\<open> BGU  \<close>
      Some (bicc_type BGU,[flaga,disp22])
    else if cond = uint(0b0010::word4) then  \<comment>\<open> BLE  \<close>
      Some (bicc_type BLE,[flaga,disp22])
    else if cond = uint(0b0011::word4) then  \<comment>\<open> BL  \<close>
      Some (bicc_type BL,[flaga,disp22])
    else if cond = uint(0b1011::word4) then  \<comment>\<open> BGE  \<close>
      Some (bicc_type BGE,[flaga,disp22])
    else if cond = uint(0b0110::word4) then  \<comment>\<open> BNEG  \<close>
      Some (bicc_type BNEG,[flaga,disp22])
    else if cond = uint(0b1010::word4) then  \<comment>\<open> BG  \<close>
      Some (bicc_type BG,[flaga,disp22])
    else if cond = uint(0b0101::word4) then  \<comment>\<open> BCS  \<close>
      Some (bicc_type BCS,[flaga,disp22])
    else if cond = uint(0b0100::word4) then  \<comment>\<open> BLEU  \<close>
      Some (bicc_type BLEU,[flaga,disp22])
    else if cond = uint(0b1101::word4) then  \<comment>\<open> BCC  \<close>
      Some (bicc_type BCC,[flaga,disp22])
    else if cond = uint(0b1000::word4) then  \<comment>\<open> BA  \<close>
      Some (bicc_type BA,[flaga,disp22])
    else if cond = uint(0b0000::word4) then  \<comment>\<open> BN  \<close>
      Some (bicc_type BN,[flaga,disp22])
    else if cond = uint(0b1110::word4) then  \<comment>\<open> BPOS  \<close>
      Some (bicc_type BPOS,[flaga,disp22])
    else if cond = uint(0b1111::word4) then  \<comment>\<open> BVC  \<close>
      Some (bicc_type BVC,[flaga,disp22])
    else if cond = uint(0b0111::word4) then  \<comment>\<open> BVS  \<close>
      Some (bicc_type BVS,[flaga,disp22])
    else None
  else None
"

text {* Parse type 3 instructions.
We don't consider floating-point operations, so we don't 
consider the third type of format 3. 
We currently don't support JMPL, RETT, SAVE, RESTORE, but we add them in this
function for future extensibility. *}
  
definition parse_instr_f3::"word32 \<Rightarrow> instruction option"
where "parse_instr_f3 w \<equiv>
  let this_op = get_op w in
  let rd = get_rd w in
  let op3 = get_op3 w in
  let rs1 = get_rs1 w in
  let flagi = get_i w in
  let asi = get_asi w in
  let rs2 = get_rs2 w in
  let simm13 = get_simm13 w in
  if this_op = uint(0b11::word2) then  \<comment>\<open> Load and Store  \<close>
   \<comment>\<open> We only consider LD, ST, and CAS here.  \<close>
   \<comment>\<open> If an instruction accesses alternative space but flagi = 1, 
     may need to throw a trap.  \<close>
    if op3 = uint(0b000000::word6) then  \<comment>\<open> LD  \<close>
      if flagi = 1 then  \<comment>\<open> Operant list is [i,rs1,simm13,rd]  \<close>
         Some (load_store_type LD,[(Flag (word_of_int flagi)),
                      (W5 (word_of_int rs1)),
                      (Simm13 (word_of_int simm13)),
                      (W5 (word_of_int rd))])
      else  \<comment>\<open> Operant list is [i,rs1,rs2,rd]  \<close>
         Some (load_store_type LD,[(Flag (word_of_int flagi)),
                      (W5 (word_of_int rs1)),
                      (W5 (word_of_int rs2)),
                      (W5 (word_of_int rd))])    
    else if op3 = uint(0b000100::word6) then  \<comment>\<open> ST  \<close>
      if flagi = 1 then  \<comment>\<open> Operant list is [i,rs1,simm13,rd]  \<close>
         Some (load_store_type ST,[(Flag (word_of_int flagi)),
                      (W5 (word_of_int rs1)),
                      (Simm13 (word_of_int simm13)),
                      (W5 (word_of_int rd))])
      else  \<comment>\<open> Operant list is [i,rs1,rs2,rd]  \<close>
         Some (load_store_type ST,[(Flag (word_of_int flagi)),
                      (W5 (word_of_int rs1)),
                      (W5 (word_of_int rs2)),
                      (W5 (word_of_int rd))])    
    else if op3 = uint(0b001111::word6) then  \<comment>\<open> SWAP  \<close>
      if flagi = 1 then  \<comment>\<open> Operant list is [i,rs1,simm13,rd]  \<close>
         Some (load_store_type SWAP,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> Operant list is [i,rs1,rs2,rd]  \<close>
         Some (load_store_type SWAP,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])    
    else if op3 = uint(0b111100::word6) then  \<comment>\<open> CASA  \<close>
       Some (load_store_type CASA,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (Asi (word_of_int asi)),
                       (W5 (word_of_int rd))])
    else None
  else if this_op = uint(0b10::word2) then  \<comment>\<open> Others  \<close>
    if op3 = uint(0b111000::word6) then  \<comment>\<open> JMPL  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (ctrl_type JMPL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (ctrl_type JMPL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b111001::word6) then  \<comment>\<open> RETT  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2]  \<close>
         Some (ctrl_type RETT,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2))])
      else  \<comment>\<open> return [i,rs1,simm13] \<close>
         Some (ctrl_type RETT,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13))])    
     \<comment>\<open> FLUSH instruction  \<close>
    else if op3 = uint(0b111011::word6) then  \<comment>\<open> FLUSH  \<close>
      if flagi = 0 then  \<comment>\<open> return [1,rs1,rs2]  \<close>
         Some (load_store_type FLUSH,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (W5 (word_of_int rs2))])
      else  \<comment>\<open> return [i,rs1,simm13]  \<close>
         Some (load_store_type FLUSH,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (Simm13 (word_of_int simm13))])
     \<comment>\<open> The following are arithmetic instructions.  \<close>
    else if op3 = uint(0b000001::word6) then  \<comment>\<open> AND  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ANDs,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ANDs,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b010001::word6) then  \<comment>\<open> ANDcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ANDcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (W5 (word_of_int rs2)),
                         (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ANDcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (Simm13 (word_of_int simm13)),
                         (W5 (word_of_int rd))])
    else if op3 = uint(0b000101::word6) then  \<comment>\<open> ANDN  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ANDN,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ANDN,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b010101::word6) then  \<comment>\<open> ANDNcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ANDNcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (W5 (word_of_int rs2)),
                          (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ANDNcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (Simm13 (word_of_int simm13)),
                          (W5 (word_of_int rd))])
    else if op3 = uint(0b000010::word6) then  \<comment>\<open> OR  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ORs,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ORs,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b010010::word6) then  \<comment>\<open> ORcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ORcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ORcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b000110::word6) then  \<comment>\<open> ORN  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ORN,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ORN,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b010110::word6) then  \<comment>\<open> ORNcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type ORNcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type ORNcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b000011::word6) then  \<comment>\<open> XORs  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type XORs,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type XORs,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b010011::word6) then  \<comment>\<open> XORcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type XORcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type XORcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b000111::word6) then  \<comment>\<open> XNOR  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type XNOR,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type XNOR,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b010111::word6) then  \<comment>\<open> XNORcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (logic_type XNORcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (logic_type XNORcc,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b100101::word6) then  \<comment>\<open> SLL  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (shift_type SLL,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,shcnt,rd] \<close>
        let shcnt = rs2 in
         Some (shift_type SLL,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int shcnt)),
                       (W5 (word_of_int rd))])
    else if op3 = uint (0b100110::word6) then  \<comment>\<open> SRL  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (shift_type SRL,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,shcnt,rd] \<close>
        let shcnt = rs2 in
         Some (shift_type SRL,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int shcnt)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b100111::word6) then  \<comment>\<open> SRA  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (shift_type SRA,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,shcnt,rd] \<close>
        let shcnt = rs2 in
         Some (shift_type SRA,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int shcnt)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b000000::word6) then  \<comment>\<open> ADD  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type ADD,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type ADD,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b010000::word6) then  \<comment>\<open> ADDcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type ADDcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (W5 (word_of_int rs2)),
                         (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type ADDcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (Simm13 (word_of_int simm13)),
                         (W5 (word_of_int rd))])
    else if op3 = uint(0b001000::word6) then  \<comment>\<open> ADDX  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type ADDX,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type ADDX,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011000::word6) then  \<comment>\<open> ADDXcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type ADDXcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type ADDXcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])    
    else if op3 = uint(0b000100::word6) then  \<comment>\<open> SUB  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SUB,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (W5 (word_of_int rs2)),
                       (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SUB,[(Flag (word_of_int flagi)),
                       (W5 (word_of_int rs1)),
                       (Simm13 (word_of_int simm13)),
                       (W5 (word_of_int rd))])
    else if op3 = uint(0b010100::word6) then  \<comment>\<open> SUBcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SUBcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (W5 (word_of_int rs2)),
                         (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SUBcc,[(Flag (word_of_int flagi)),
                         (W5 (word_of_int rs1)),
                         (Simm13 (word_of_int simm13)),
                         (W5 (word_of_int rd))])
    else if op3 = uint(0b001100::word6) then  \<comment>\<open> SUBX  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SUBX,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SUBX,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011100::word6) then  \<comment>\<open> SUBXcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SUBXcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SUBXcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])    
    else if op3 = uint(0b100100::word6) then  \<comment>\<open> MULScc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type MULScc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type MULScc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b001010::word6) then  \<comment>\<open> UMUL  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type UMUL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type UMUL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011010::word6) then  \<comment>\<open> UMULcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type UMULcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type UMULcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b001011::word6) then  \<comment>\<open> SMUL  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SMUL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SMUL,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011011::word6) then  \<comment>\<open> SMULcc \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SMULcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (W5 (word_of_int rs2)),
                          (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SMULcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (Simm13 (word_of_int simm13)),
                          (W5 (word_of_int rd))])
    else if op3 = uint(0b001110::word6) then  \<comment>\<open> UDIV  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type UDIV,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type UDIV,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011110::word6) then  \<comment>\<open> UDIVcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type UDIVcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (W5 (word_of_int rs2)),
                          (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type UDIVcc,[(Flag (word_of_int flagi)),
                          (W5 (word_of_int rs1)),
                          (Simm13 (word_of_int simm13)),
                          (W5 (word_of_int rd))])
    else if op3 = uint(0b001111::word6) then  \<comment>\<open> SDIV  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SDIV,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SDIV,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b011111::word6) then  \<comment>\<open> SDIVcc  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (arith_type SDIVcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (arith_type SDIVcc,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b111100::word6) then  \<comment>\<open> SAVE  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (ctrl_type SAVE,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (W5 (word_of_int rs2)),
                        (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (ctrl_type SAVE,[(Flag (word_of_int flagi)),
                        (W5 (word_of_int rs1)),
                        (Simm13 (word_of_int simm13)),
                        (W5 (word_of_int rd))])
    else if op3 = uint(0b111101::word6) then  \<comment>\<open> RESTORE  \<close>
      if flagi = 0 then  \<comment>\<open> return [i,rs1,rs2,rd]  \<close>
         Some (ctrl_type RESTORE,[(Flag (word_of_int flagi)),
                           (W5 (word_of_int rs1)),
                           (W5 (word_of_int rs2)),
                           (W5 (word_of_int rd))])
      else  \<comment>\<open> return [i,rs1,simm13,rd] \<close>
         Some (ctrl_type RESTORE,[(Flag (word_of_int flagi)),
                           (W5 (word_of_int rs1)),
                           (Simm13 (word_of_int simm13)),
                           (W5 (word_of_int rd))])         
    else None
  else None"

text {* Decode the word32 value of an instruction into 
        the name of the instruction and its operands. *}
definition decode_instruction::"word32 \<Rightarrow> instruction option" where 
"decode_instruction w \<equiv> 
  let this_op = get_op w in 
  if this_op = uint(0b01::word2) then  \<comment>\<open> Instruction format 1  \<close>
    parse_instr_f1 w
  else if this_op = uint(0b00::word2) then  \<comment>\<open> Instruction format 2  \<close>
    parse_instr_f2 w
  else  \<comment>\<open> op = 11 0r 10, instructionrett format 3  \<close>
    parse_instr_f3 w"

text{* Evaluate icc based on the bits N, Z, V, C in PSR 
       and the type of branching instruction. 
       See Sparcv8 manual Page 178. *}
  
definition eval_icc::"sparc_operation \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> int"
where
"eval_icc instr_name n_val z_val v_val c_val \<equiv>
    if instr_name = bicc_type BNE then
      if z_val = 0 then 1 else 0
    else if instr_name = bicc_type BE then 
      if z_val = 1 then 1 else 0
    else if instr_name = bicc_type BG then
      if (bitOR z_val (n_val XOR v_val)) = 0 then 1 else 0
    else if instr_name = bicc_type BLE then
      if (bitOR z_val (n_val XOR v_val)) = 1 then 1 else 0
    else if instr_name = bicc_type BGE then
      if (n_val XOR v_val) = 0 then 1 else 0
    else if instr_name = bicc_type BL then
      if (n_val XOR v_val) = 1 then 1 else 0
    else if instr_name = bicc_type BGU then
      if (c_val = 0 \<and> z_val = 0) then 1 else 0
    else if instr_name = bicc_type BLEU then
      if (c_val = 1 \<or> z_val = 1) then 1 else 0
    else if instr_name = bicc_type BCC then
      if c_val = 0 then 1 else 0
    else if instr_name = bicc_type BCS then
      if c_val = 1 then 1 else 0
    else if instr_name = bicc_type BNEG then
      if n_val = 1 then 1 else 0
    else if instr_name = bicc_type BA then 1
    else if instr_name = bicc_type BN then 0
    else if instr_name = bicc_type BPOS then
      if n_val = 0 then 1 else 0
    else if instr_name = bicc_type BVC then
      if v_val = 0 then 1 else 0
    else if instr_name = bicc_type BVS then
      if v_val = 1 then 1 else 0
    else -1"

text {* Operational semantics for Branching insturctions. 
        Return exception or a bool value for annulment. 
        If the bool value is 1, then the delay instruciton 
        is not executed, otherwise the delay instruction
        is executed. *}
  
definition branch_instr::"proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"branch_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;
      flaga = get_operand_flag (op_list!0);
      psr_val = ctl_reg_val p PSR state;
      icc_val = eval_icc instr_name (get_icc_N psr_val) (get_icc_Z psr_val) (get_icc_V psr_val) 
                                    (get_icc_C psr_val);
      state1 = ctl_reg_mod p (ctl_reg_val p nPC state) PC state
  in
  if icc_val = 1 then
    let state2 = ctl_reg_mod p ((ctl_reg_val p PC state) + (sign_ext24 (((ucast(get_operand_w22 (op_list!1)))::word24) << 2))) nPC state1 in
    if (instr_name = bicc_type BA) \<and> (flaga = 1) then annul_mod p True state2
    else state2 
  else 
    let state2 = ctl_reg_mod p ((ctl_reg_val p nPC state) + 4) nPC state1 in
    if flaga = 1 then annul_mod p True state2
    else state2"

text {* Operational semantics for NOP *}

definition nop_instr::"proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"nop_instr p instr state \<equiv> state"

text {* Operational semantics for SETHI *}
  
definition sethi_instr::"proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"sethi_instr p instr state \<equiv>
  let op_list = snd instr;
      rd = get_operand_w5 (op_list!1)
  in
  if rd \<noteq> 0 then
    gen_reg_mod p (((ucast(get_operand_w22 (op_list!0)))::word32) << 10) (ucast rd) state
  else state"

text {* Get operand2 based on the flag i, rs1, rs2, and simm13. 
        If i = 0 then operand2 = r[rs2],
        else operand2 = sign\_ext13(simm13). 
        op\_list should be [i,rs1,rs2,...] or [i,rs1,simm13,...]. *}
  
definition get_operand2::"proc \<Rightarrow> inst_operand list \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where 
"get_operand2 p op_list s \<equiv>
  if (get_operand_flag (op_list!0)) = 0 then
    gen_reg_val p (ucast (get_operand_w5 (op_list!2))) s
  else
    sign_ext13 (get_operand_simm13 (op_list!2))"

text {* Get the address based on the flag i, rs1, rs2, and simm13. 
        If i = 0 then addr = r[rs1] + r[rs2],
        else addr = r[rs1] + sign\_ext13(simm13). 
        op\_list should be [i,rs1,rs2,...] or [i,rs1,simm13,...]. *}
  
definition get_addr::"proc \<Rightarrow> inst_operand list \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where 
"get_addr p op_list s \<equiv> (gen_reg_val p (ucast (get_operand_w5 (op_list!1))) s) + 
  (get_operand2 p op_list s)"

text {* Operational semantics for JMPL *}
  
definition jmpl_instr::"proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"jmpl_instr p instr state \<equiv>
  let op_list = snd instr;
      rd = get_operand_w5 ((snd instr)!3);
      state1 = if rd \<noteq> 0 then gen_reg_mod p (ctl_reg_val p PC state) (ucast rd) state else state;
      state2 = ctl_reg_mod p (ctl_reg_val p nPC state) PC state1
  in
  ctl_reg_mod p (get_addr p op_list state) nPC state2"

text {* Compute the result of logical operators. *}

definition logical_result :: "sparc_operation \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32" where 
"logical_result instr_name rs1_val operand2 \<equiv>
  if (instr_name = logic_type ANDs) \<or> (instr_name = logic_type ANDcc) then
    bitAND rs1_val operand2     
  else if (instr_name = logic_type ANDN) \<or> (instr_name = logic_type ANDNcc) then
    bitAND rs1_val (bitNOT operand2)
  else if (instr_name = logic_type ORs) \<or> (instr_name = logic_type ORcc) then
    bitOR rs1_val operand2
  else if instr_name \<in> {logic_type ORN,logic_type ORNcc} then 
    bitOR rs1_val (bitNOT operand2)
  else if instr_name \<in> {logic_type XORs,logic_type XORcc} then 
    bitXOR rs1_val operand2
  else  \<comment>\<open> Must be XNOR or XNORcc  \<close>
    bitXOR rs1_val (bitNOT operand2)"

text {* Get the new PSR value for logical/multiply instructions. *}

definition logical_mult_new_psr_val :: "proc \<Rightarrow> word32 \<Rightarrow> sparc_state \<Rightarrow> word32" where 
"logical_mult_new_psr_val p result s \<equiv> update_PSR_icc (ucast (result >> 31)) 
  (if result = 0 then 1 else 0) 0 0 (ctl_reg_val p PSR s)"

text {* Operational semantics for logical instructions. *}

definition logical_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"logical_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;
      rd = get_operand_w5 (op_list!3);
      result = logical_result instr_name (gen_reg_val p (ucast (get_operand_w5 (op_list!1))) state) 
        (get_operand2 p op_list state);
      state1 = if rd \<noteq> 0 then gen_reg_mod p result (ucast rd) state else state 
  in
  if instr_name \<in> {logic_type ANDcc,logic_type ANDNcc,logic_type ORcc,
      logic_type ORNcc,logic_type XORcc,logic_type XNORcc} then
    ctl_reg_mod p (logical_mult_new_psr_val p result state) PSR state1
  else state1"

text {* Operational semantics for shift instructions. *}
  
definition shift_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"shift_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;
      rs1_val = gen_reg_val p (ucast (get_operand_w5 (op_list!1))) state;
      rs2_shcnt = get_operand_w5 (op_list!2);
      rd = get_operand_w5 (op_list!3);
      shift_count = if (get_operand_flag (op_list!0)) = 0 then 
                      ucast (gen_reg_val p (ucast rs2_shcnt) state) 
                    else rs2_shcnt
  in
  if (instr_name = shift_type SLL) \<and> (rd \<noteq> 0) then
    gen_reg_mod p (rs1_val << (unat shift_count)) (ucast rd) state
  else if (instr_name = shift_type SRL) \<and> (rd \<noteq> 0) then
    gen_reg_mod p (rs1_val >> (unat shift_count)) (ucast rd) state
  else if (instr_name = shift_type SRA) \<and> (rd \<noteq> 0) then
    gen_reg_mod p (rs1_val >>> (unat shift_count)) (ucast rd) state
  else state"

text {* Calculate the new PSR value for the ADDcc and ADDXcc instructions. *}
  
definition add_new_psr_val:: "proc \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> sparc_state \<Rightarrow> word32" where
"add_new_psr_val p result rs1_val operand2 state \<equiv> 
  let result_31 = ((ucast (result >> 31))::word1);
      rs1_val_31 = ((ucast (rs1_val >> 31))::word1);
      operand2_31 = ((ucast (operand2 >> 31))::word1);
      v_val = (bitOR (bitAND rs1_val_31 
                             (bitAND operand2_31 
                                     (bitNOT result_31))) 
                     (bitAND (bitNOT rs1_val_31) 
                             (bitAND (bitNOT operand2_31) 
                                     result_31)));
     c_val = (bitOR (bitAND rs1_val_31 
                            operand2_31) 
                    (bitAND (bitNOT result_31) 
                            (bitOR rs1_val_31 
                                   operand2_31)))
  in
  update_PSR_icc result_31 (if result = 0 then 1 else 0) v_val c_val (ctl_reg_val p PSR state)"  

text {* Operational semantics for add instructions. 
        These include ADD, ADDcc, ADDX. *}
  
definition add_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"add_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;
      rd = get_operand_w5 (op_list!3);
      operand2 = get_operand2 p op_list state;
      rs1_val = gen_reg_val p (ucast (get_operand_w5 (op_list!1))) state;
      result = if (instr_name = arith_type ADD) \<or> (instr_name = arith_type ADDcc) then
                rs1_val + operand2
               else  \<comment>\<open> Must be ADDX or ADDXcc  \<close> 
                rs1_val + operand2 + (ucast (get_icc_C (ctl_reg_val p PSR state)));
      state1 = if rd \<noteq> 0 then gen_reg_mod p result (ucast rd) state else state
  in
  if (instr_name = arith_type ADDcc) \<or> (instr_name = arith_type ADDXcc) then
    ctl_reg_mod p (add_new_psr_val p result rs1_val operand2 state) PSR state1
  else state1"

text {* Calculate the new PSR value for the SUBcc and SUBXcc instructions. *}
  
definition sub_new_psr_val:: "proc \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> sparc_state \<Rightarrow> word32" where
"sub_new_psr_val p result rs1_val operand2 state \<equiv> 
  let result_31 = ((ucast (result >> 31))::word1);
      rs1_val_31 = ((ucast (rs1_val >> 31))::word1);
      operand2_31 = ((ucast (operand2 >> 31))::word1);
      v_val = (bitOR (bitAND rs1_val_31 
                             (bitAND (bitNOT operand2_31) 
                                     (bitNOT result_31))) 
                             (bitAND (bitNOT rs1_val_31) 
                                     (bitAND operand2_31 
                                             result_31)));
     c_val = (bitOR (bitAND (bitNOT rs1_val_31) 
                             operand2_31) 
                    (bitAND result_31 
                            (bitOR (bitNOT rs1_val_31) 
                                    operand2_31)))
  in
  update_PSR_icc result_31 (if result = 0 then 1 else 0) v_val c_val (ctl_reg_val p PSR state)"  

text {* Operational semantics for subtract instructions. 
        These include SUB, SUBcc, SUBX. *}
    
definition sub_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"sub_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;      
      rd = get_operand_w5 (op_list!3);
      operand2 = get_operand2 p op_list state;
      rs1_val = gen_reg_val p (ucast (get_operand_w5 (op_list!1))) state;
      result = if (instr_name = arith_type SUB) \<or> (instr_name = arith_type SUBcc) then
                rs1_val - operand2
               else  \<comment>\<open> Must be SUBX or SUBXcc  \<close> 
                rs1_val - operand2 - (ucast (get_icc_C (ctl_reg_val p PSR state)));
      state1 = if rd \<noteq> 0 then gen_reg_mod p result (ucast rd) state else state
  in
  if (instr_name = arith_type SUBcc) \<or> (instr_name = arith_type SUBXcc) then
    ctl_reg_mod p (sub_new_psr_val p result rs1_val operand2 state) PSR state1
  else state1"

text {* Operational semantics for multiply instructions. *}

definition mul_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"mul_instr p instr state \<equiv>
  let instr_name = fst instr;
      op_list = snd instr;
      rd = get_operand_w5 (op_list!3);
      operand2 = get_operand2 p op_list state;
      rs1_val = gen_reg_val p (ucast (get_operand_w5 (op_list!1))) state;
      result0 = if instr_name \<in> {arith_type UMUL,arith_type UMULcc} then 
                  (word_of_int ((uint rs1_val) * (uint operand2)))::word64
                else  \<comment>\<open> Must be SMUL or SMULcc  \<close>
                  (word_of_int ((sint rs1_val) * (sint operand2)))::word64;
      state1 = ctl_reg_mod p (ucast (result0 >> 32)) Y state;
      state2 = if rd \<noteq> 0 then gen_reg_mod p (ucast result0) (ucast rd) state1 else state1
  in
  if (instr_name = arith_type UMULcc) \<or> (instr_name = arith_type SMULcc) then
    ctl_reg_mod p (logical_mult_new_psr_val p (ucast result0) state1) PSR state2
  else state2"

definition div_comp_temp_64bit :: "instruction \<Rightarrow> word64 \<Rightarrow> 
  virtual_address \<Rightarrow> word64"
where "div_comp_temp_64bit i y_rs1 operand2 \<equiv> 
  if ((fst i) = arith_type UDIV) \<or> ((fst i) = arith_type UDIVcc) then 
    (word_of_int ((uint y_rs1) div (uint operand2)))::word64
  else  \<comment>\<open> Must be SDIV or SDIVcc.  \<close> 
     \<comment>\<open> Due to Isabelle's rounding method is not nearest to zero, 
       we have to implement division in a different way.  \<close>
    let sop1 = sint y_rs1;
        sop2 = sint operand2;
        pop1 = abs sop1;
        pop2 = abs sop2
    in
    if sop1 > 0 \<and> sop2 > 0 then 
      (word_of_int (sop1 div sop2))
    else if sop1 > 0 \<and> sop2 < 0 then
      (word_of_int (- (sop1 div pop2)))
    else if sop1 < 0 \<and> sop2 > 0 then
      (word_of_int (- (pop1 div sop2)))
    else  \<comment>\<open> sop1 < 0 \<and> sop2 < 0  \<close>
      (word_of_int (pop1 div pop2))"

definition div_comp_temp_V :: "instruction \<Rightarrow> word32 \<Rightarrow> word33 \<Rightarrow> word1"
where "div_comp_temp_V i w32 w33 \<equiv> 
  if ((fst i) = arith_type UDIV) \<or> ((fst i) = arith_type UDIVcc) then
    if w32 = 0 then 0 else 1
  else  \<comment>\<open> Must be SDIV or SDIVcc.  \<close> 
    if (w33 = 0) \<or> (w33 = (0b111111111111111111111111111111111::word33)) 
    then 0 else 1"

definition div_comp_result :: "instruction \<Rightarrow> word1 \<Rightarrow> word64 \<Rightarrow> word32"
where "div_comp_result i temp_V temp_64bit \<equiv>
  if temp_V = 1 then
    if ((fst i) = arith_type UDIV) \<or> ((fst i) = arith_type UDIVcc) then
      (0b11111111111111111111111111111111::word32)
    else if (fst i) \<in> {arith_type SDIV,arith_type SDIVcc} then  
      if temp_64bit > 0 then 
        (0b01111111111111111111111111111111::word32)
      else ((word_of_int (0 - (uint (0b10000000000000000000000000000000::word32))))::word32)
    else ((ucast temp_64bit)::word32)
  else ((ucast temp_64bit)::word32)"

definition div_psr_new_val :: "proc \<Rightarrow> word32 \<Rightarrow> word1 \<Rightarrow> sparc_state \<Rightarrow> word32" where 
"div_psr_new_val p result temp_V state \<equiv> update_PSR_icc (ucast (result >> 31)) 
  (if result = 0 then 1 else 0) temp_V 0 (ctl_reg_val p PSR state)"

definition div_comp :: "proc \<Rightarrow> instruction \<Rightarrow> word5 \<Rightarrow> word5 \<Rightarrow> virtual_address \<Rightarrow> 
  sparc_state \<Rightarrow> sparc_state" where 
"div_comp p instr rs1 rd operand2 state \<equiv>
  let temp_64bit = div_comp_temp_64bit instr (word_cat (ctl_reg_val p Y state) 
        (gen_reg_val p (ucast rs1) state)) operand2;
      temp_V = div_comp_temp_V instr (ucast (temp_64bit >> 32)) (ucast (temp_64bit >> 31));
      result = div_comp_result instr temp_V temp_64bit;
      state1 = if rd \<noteq> 0 then gen_reg_mod p result (ucast rd) state else state
  in
  ctl_reg_mod p (div_psr_new_val p result temp_V state) PSR state1"

text {* Operational semantics for divide instructions. *}
  
definition div_instr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"div_instr p instr state \<equiv>
  let op_list = snd instr;
      operand2 = get_operand2 p op_list state
  in
   \<comment>\<open> Should throw a trap here. But we don't consider traps in this model.       
     We simply return a state that is undefined.  \<close>
  if (uint operand2) = 0 then (state\<lparr>undef := True\<rparr>)     
  else div_comp p instr (get_operand_w5 (op_list!1)) (get_operand_w5 (op_list!3)) operand2 state"

text {* Operational semantics for Load instructions. 
Unlike the SPARCv8 ISA model, here we give a big-step semantics.
We don't consider traps and we restrict our model to memory access
of 32-bit word only (i.e., LD only). *}
  
definition load_addr :: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where
"load_addr p instr state \<equiv> get_addr p (snd instr) state"  
  
definition load_instr :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> virtual_address option \<Rightarrow> 
  memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"load_instr p instr opid aop vop state \<equiv> 
  let op_list = snd instr;
      rd = get_operand_w5 (op_list!3)
  in
  case (aop,vop) of (Some addr, Some v) \<Rightarrow>
    if rd \<noteq> 0 then
      mem_op_val_mod v opid (mem_op_addr_mod addr opid (gen_reg_mod p v (ucast rd) state))
    else mem_op_val_mod v opid (mem_op_addr_mod addr opid state)  
  |_ \<Rightarrow> (state\<lparr>undef := True\<rparr>)"  \<comment>\<open> Memory access error.  \<close>

text {* Operational semantics for Store instructions. 
Unlike the SPARCv8 ISA model, here we give a big-step semantics.
We don't consider traps and we restrict our model to memory access
of 32-bit word only (i.e., ST only). 

N.B. We DO NOT access memory in the store instruction. Instead, it simply 
updates the op_val and op_addr fields of the corresponding op_id. 
The memory access will be executed when the memory executes the operation (
in memory order). *}
  
definition store_instr :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"store_instr p instr opid state \<equiv> 
  let op_list = snd instr;
      val = gen_reg_val p (ucast (get_operand_w5 (op_list!3))) state; 
      addr = get_addr p op_list state 
  in
  mem_op_val_mod val opid (mem_op_addr_mod addr opid state)"

text {* Operational semantics for SWAP.
To facilitate our memory model, we split this instruction in two functions:
swap_load is the load part, and swap_store is the store part. 
The load and store operations should be done atomically by the memory. 

N.B. We DO NOT access memory in the store part. Instead, it simply 
updates the op_val and op_addr fields of the corresponding op_id. 
The memory access will be executed when the memory executes the operation (
in memory order).
*}

definition swap_load_addr:: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where
"swap_load_addr \<equiv> load_addr"  
  
definition swap_load :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> virtual_address option \<Rightarrow> 
  memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"swap_load p instr opid aop vop state \<equiv> 
  let op_list = snd instr;
      rd = get_operand_w5 (op_list!3)
  in
  case (aop,vop) of (Some addr, Some v) \<Rightarrow>
    if rd \<noteq> 0 then
      mem_op_val_mod v opid (mem_op_addr_mod addr opid (gen_reg_mod p v (ucast rd) 
        (atomic_rd_mod (gen_reg_val p (ucast rd) state) state)))
    else mem_op_val_mod v opid (mem_op_addr_mod addr opid 
        (atomic_rd_mod (gen_reg_val p (ucast rd) state) state))  
  |_ \<Rightarrow> (state\<lparr>undef := True\<rparr>)"  \<comment>\<open> Memory access error.  \<close>

definition swap_store :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"swap_store p instr opid state \<equiv> 
  let op_list = snd instr;
      addr = get_addr p op_list state 
  in
  mem_op_val_mod (atomic_rd_val state) opid (mem_op_addr_mod addr opid state)"
  
text {* The following definitions are for the CASA instruction 
from SPARCv9. Some LEON3 processors support them, some don't. There are no
documentations of their operational semantics. The implementation below is based on
my understanding of the SPARCv9 instruction definition 
(which is just a very brief explanation in English)
on page 176 of the SPARCv9 manual
and the two webpages:
https://gcc.gnu.org/ml/gcc/2014-04/msg00241.html
http://lists.llvm.org/pipermail/llvm-commits/Week-of-Mon-20160516/356670.html
 
Like the modelling for SWAP, we split the CASA operational semantics into
two functions, one for the load part, the other for the store part.
The two operations should be done atomically by the memory. 

casa_load: addr <- r[rs1]; r[rd] <- mem[addr];
casa_store: if r[rs2] = r[rd] then mem[addr] <- r[rd]; 

N.B. We DO NOT access memory in the store part. Instead, it simply 
updates the op_val and op_addr fields of the corresponding op_id. 
The memory access will be executed when the memory executes the operation (
in memory order).

ALSO N.B. SPARCv9 general registers are 64-bits, but SPARCv8 general registers
are 32-bits. The below implementation of CASA is adopted to work on SPARCv8.
That is, we DO NOT set the higher 32-bit of rd to 0, because rd only has 32-bits. *}  
  
definition casa_load_addr:: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where
"casa_load_addr p instr state \<equiv> gen_reg_val p (ucast (get_operand_w5 ((snd instr)!1))) state"  
  
definition atomic_load_addr:: "proc \<Rightarrow> instruction \<Rightarrow> sparc_state \<Rightarrow> virtual_address" where
"atomic_load_addr p instr state \<equiv> 
  if (fst instr) = load_store_type SWAP then swap_load_addr p instr state
  else casa_load_addr p instr state"  

definition casa_load :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> virtual_address option \<Rightarrow> 
  memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"casa_load p instr opid aop vop state \<equiv> 
  let op_list = snd instr;
      rd = get_operand_w5 (op_list!4)
  in
  case (aop,vop) of (Some addr, Some v) \<Rightarrow>
    if rd \<noteq> 0 then
      mem_op_val_mod v opid (mem_op_addr_mod addr opid (gen_reg_mod p v (ucast rd) 
      (atomic_rd_mod (gen_reg_val p (ucast rd) state) state)))
    else mem_op_val_mod v opid (mem_op_addr_mod addr opid 
      (atomic_rd_mod (gen_reg_val p (ucast rd) state) state))
  |_ \<Rightarrow> (state\<lparr>undef := True\<rparr>)"  \<comment>\<open> Memory access error.  \<close>  

definition casa_store :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"casa_store p instr opid state \<equiv> 
  let op_list = snd instr;       
      addr = casa_load_addr p instr state
  in
  case (atomic_flag_val state) of Some opid' \<Rightarrow>
    (case (op_val (mem_ops state opid')) of Some val \<Rightarrow>  \<comment>\<open> val is the value at addr.  \<close>
      if (gen_reg_val p (ucast (get_operand_w5 (op_list!2))) state) = val then
        mem_op_val_mod (atomic_rd_val state) opid (mem_op_addr_mod addr opid state)    
      else state
    |_ \<Rightarrow> (state\<lparr>undef := True\<rparr>))  \<comment>\<open> Memory access error.  \<close>
  |_ \<Rightarrow> (state\<lparr>undef := True\<rparr>)"  \<comment>\<open> The memory model ensures that this won't happen.  \<close>  

end

\<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
 \<close>

theory Processor_Execution
imports Main Sparc_Instruction  Misc
"HOL-Eisbach.Eisbach_Tools"
begin

text {* Program order is simply the sequence of instructions (in the order of
how the processor issues them) grouped in mem_op_blocks. We use op_id here
to identify the mem_op_block. *}

type_synonym program_order = "proc \<Rightarrow> (op_id list)"  

definition emp_program_order:: "program_order" where "emp_program_order p \<equiv> []"

type_synonym program_block_map = "op_id \<Rightarrow> program_block"  
  
definition emp_prog_block_map:: "program_block_map" where 
"emp_prog_block_map p \<equiv> emp_prog_block"  
  
text {* Given an op_id, get its processor. *}

definition proc_of_op:: "op_id \<Rightarrow> program_block_map \<Rightarrow> proc" where
"proc_of_op opid pbm \<equiv> op_proc (pbm opid)"  
  
text {* The program order predicate ";" that tests if a memory operation block op1 is before 
memory operation block op2 in the program order. *}

definition program_order_before:: "op_id \<Rightarrow> program_order \<Rightarrow> proc \<Rightarrow> op_id \<Rightarrow> bool" 
 ("_ ;_^_ _") where
"op1 ;po^p op2 \<equiv> list_before op1 (po p) op2"  

text {* A new version of program_order_before for code export. *}


lemma prog_order_before_trans: 
assumes a1: "(op1 ;po^p op2)"
and a2: "(op2 ;po^p op3)"
and a3: "non_repeat_list (po p)"
shows "(op1 ;po^p op3)"
proof -
  from a1 obtain i j where f1: "0 \<le> i \<and> i < length (po p) \<and> 0 \<le> j \<and> j < length (po p) \<and> 
    ((po p)!i) = op1 \<and> ((po p)!j) = op2 \<and> i < j"
    unfolding program_order_before_def list_before_def by auto
  from a2 obtain k l where f2: "0 \<le> k \<and> k < length (po p) \<and> 0 \<le> l \<and> l < length (po p) \<and> 
    ((po p)!k) = op2 \<and> ((po p)!l) = op3 \<and> k < l"
    unfolding program_order_before_def list_before_def by auto
  from a3 f1 f2 have f3: "j = k"
    unfolding non_repeat_list_def
    using nth_eq_iff_index_eq by blast      
    \<comment>\<open>by auto\<close>
  from f1 f2 f3 have "0 \<le> i \<and> i < length (po p) \<and> 0 \<le> l \<and> l < length (po p) \<and> 
    ((po p)!i) = op1 \<and> ((po p)!l) = op3 \<and> i < l"
    by auto
  then show ?thesis unfolding program_order_before_def list_before_def by auto
qed    

text {* The execution of an instruction. 
N.B. This is NOT the same as the ISA model where the processor 
dispatches and executions the instruction. The execution here is 
from the memory order perspective. *} 
  
definition proc_exe :: "proc \<Rightarrow> instruction \<Rightarrow> op_id \<Rightarrow> virtual_address option \<Rightarrow> 
  memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state"
where "proc_exe p instr opid a v s \<equiv> 
  let instr_name = fst instr in
  if instr_name \<in> {load_store_type LD} then
    load_instr p instr opid a v s
  else if instr_name \<in> {load_store_type ST} then
    store_instr p instr opid s
  else if instr_name \<in> {sethi_type SETHI} then
    sethi_instr p instr s
  else if instr_name \<in> {nop_type NOP} then
    nop_instr p instr s
  else if instr_name \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
    logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
    logic_type XORs,logic_type XNOR} then
    logical_instr p instr s
  else if instr_name \<in> {shift_type SLL,shift_type SRL,shift_type SRA} then
    shift_instr p instr s
  else if instr_name \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX} then
    add_instr p instr s
  else if instr_name \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX} then
    sub_instr p instr s
  else if instr_name \<in> {arith_type UMUL,arith_type SMUL,arith_type SMULcc} then
    mul_instr p instr s
  else if instr_name \<in> {arith_type UDIV,arith_type UDIVcc,arith_type SDIV} then
    div_instr p instr s
  else if instr_name \<in> {ctrl_type JMPL} then
    jmpl_instr p instr s
  else if instr_name \<in> {bicc_type BE,bicc_type BNE,bicc_type BGU,
    bicc_type BLE,bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
    bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,bicc_type BN} then
    branch_instr p instr s
  else if instr_name \<in> {load_store_type SWAP_LD} then
    swap_load p instr opid a v s
  else if instr_name \<in> {load_store_type SWAP_ST} then
    swap_store p instr opid s
  else if instr_name \<in> {load_store_type CASA_LD} then
    casa_load p instr opid a v s
  else if instr_name \<in> {load_store_type CASA_ST} then
    casa_store p instr opid s
  else s"

text {* Sequential execution of a list of instructions. *}

primrec seq_proc_exe:: "proc \<Rightarrow> instruction list \<Rightarrow> op_id \<Rightarrow> virtual_address option \<Rightarrow> 
  memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"seq_proc_exe p [] opid a v s = s"
|"seq_proc_exe p (x#xs) opid a v s = seq_proc_exe p xs opid a v (proc_exe p x opid a v s)"
  
text {* Sequential execution of n mem_op_blocks on proc in the program_order,
starting from the next of proc_exe_pos. *}

primrec seq_proc_blk_exe:: "proc \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> nat \<Rightarrow> 
  virtual_address option \<Rightarrow> memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"seq_proc_blk_exe p po pbm 0 a v s = s" 
|"seq_proc_blk_exe p po pbm (Suc n) a v s = (
  let next_pos = proc_exe_pos s p in
  if next_pos < (List.length (po p)) then 
    let opid = List.nth (po p) next_pos in
    seq_proc_blk_exe p po pbm n a v 
      (next_proc_op_pos_mod p (Suc next_pos) 
        (seq_proc_exe p (insts (pbm opid)) opid a v s))
  else s)"
  
text {* Sequential execution of a series of mem_op_blocks
from proc_exe_pos (inclusive)
to the operation at position pos in the program order (instruction list). 
Note::::::::::: if there are errors in execution, it's possibly because
pos - last_pos is negative. *} 

definition proc_exe_to:: "proc \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> nat \<Rightarrow> 
  sparc_state \<Rightarrow> sparc_state" where  
"proc_exe_to p po pbm pos s \<equiv> 
  let next_pos = proc_exe_pos s p in
  seq_proc_blk_exe p po pbm ((pos + 1) - next_pos) None None s"  
    
text {* Sequential execution of n mem_op_blocks on proc in the program_order,
starting from the next of proc_exe_pos. 
For the last block, DO NOT execute the last instruction (memory operation instruction). *}

primrec seq_proc_blk_exe_except_last:: "proc \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> nat \<Rightarrow> 
  virtual_address option \<Rightarrow> memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"seq_proc_blk_exe_except_last p po pbm 0 a v s = s" 
|"seq_proc_blk_exe_except_last p po pbm (Suc n) a v s = (
  let next_pos = proc_exe_pos s p in
  if next_pos < (List.length (po p)) then 
    let opid = List.nth (po p) next_pos in
    if n = 0 then \<comment>\<open> The last block. Don't execute the last instruction. \<close>
      seq_proc_blk_exe p po pbm n a v (seq_proc_exe p (butlast (insts (pbm opid))) opid a v s)
    else
      seq_proc_blk_exe p po pbm n a v (next_proc_op_pos_mod p (Suc next_pos) 
        (seq_proc_exe p (insts (pbm opid)) opid a v s))
  else s)"

text {* Sequential execution of a series of mem_op_block
from proc_exe_pos (inclusive)
to the instruction before the memory operation in the block pos in the program order. *}

definition proc_exe_to_previous:: "proc \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> nat \<Rightarrow> 
  sparc_state \<Rightarrow> sparc_state" where  
"proc_exe_to_previous p po pbm pos s \<equiv> 
  let next_pos = proc_exe_pos s p in
  seq_proc_blk_exe_except_last p po pbm ((pos + 1) - next_pos) None None s"  
  
text {* Execute the last instruction in the block pos. 
N.B. This is called proc_exe_last in the paper. *}

definition proc_exe_to_last:: "proc \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> nat \<Rightarrow> 
  virtual_address option \<Rightarrow> memory_value option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where  
"proc_exe_to_last p po pbm pos v a s \<equiv> 
  if pos < (List.length (po p)) then 
    let opid = List.nth (po p) pos in
      next_proc_op_pos_mod p (Suc pos) (seq_proc_exe p [last (insts (pbm opid))] opid a v s)
  else s"  

end

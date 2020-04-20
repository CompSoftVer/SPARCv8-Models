\<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
 \<close>

text {* Examples of SPARC TSO. *}
theory Examples
  imports Main Memory_Model 
begin

section {* Examples *}
  
subsection{* Indirection Through Processors *}  
  
text {* Below are the Indirection Through Processors example in 
Figure 46 of the SPARCv9 manual. *}  

text {* We first define the instructions involved in this program. *}  
  
definition il0:: "instruction list" where
"il0 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 4))]),
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 in r5 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 5))]),
(load_store_type ST, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> store the value in r5 (1) to mem[r4 (1)] \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 5))]) \<comment>\<open> That is, we assume address A = 1. \<close>
]"  \<comment>\<open> This block means: st #1 [1] \<close>

definition il1:: "instruction list" where
"il1 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 in r5\<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 5))]),
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 2 = 2 in r4\<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 2)),
                       (W5 (word_of_int 4))]),
(load_store_type ST, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> store the value in r5 (1) to mem[r4 (2)] \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 5))]) \<comment>\<open> That is, we assume address B = 2. \<close>
]"  \<comment>\<open> This block means: st #1 [2]\<close>

definition il2:: "instruction list" where
"il2 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 2 = 2 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 2)),
                       (W5 (word_of_int 4))]),
(load_store_type LD, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> load the value in mem[r4 (2)] to r1. \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 1))]) 
]" \<comment>\<open> This block means: ld [2] %r1 \<close>

definition il3:: "instruction list" where
"il3 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 3 = 3 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 3)),
                       (W5 (word_of_int 4))]),
(load_store_type ST, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> store the value in r1 (whatever the value is from previous computation) to mem[r4 (3)] \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 1))]) \<comment>\<open> That is, we assume address C = 3. \<close>
]"  \<comment>\<open> This block means: st %r1 [3] \<close>
  
definition il4:: "instruction list" where
"il4 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 3 = 3 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 3)),
                       (W5 (word_of_int 4))]),
(load_store_type LD, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> load the value in mem[r4 (3)] to r1. \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 1))]) 
]"  \<comment>\<open> This block means: ld [3] %r1 \<close>

definition il5:: "instruction list" where
"il5 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 4))]),
(load_store_type LD, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> load the value in mem[r4 (1)] to r2. \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 2))]) 
]"  \<comment>\<open> This block means: ld [1] %r2 \<close>

text {* Then we group the instructions into blocks. *}

definition pb0:: "program_block" where
"pb0 \<equiv> \<lparr>insts = il0, op_proc = 1, atom_pair_id = None\<rparr>"
  
definition pb1:: "program_block" where
"pb1 \<equiv> \<lparr>insts = il1, op_proc = 1, atom_pair_id = None\<rparr>"

definition pb2:: "program_block" where
"pb2 \<equiv> \<lparr>insts = il2, op_proc = 2, atom_pair_id = None\<rparr>"

definition pb3:: "program_block" where
"pb3 \<equiv> \<lparr>insts = il3, op_proc = 2, atom_pair_id = None\<rparr>"

definition pb4:: "program_block" where
"pb4 \<equiv> \<lparr>insts = il4, op_proc = 3, atom_pair_id = None\<rparr>"

definition pb5:: "program_block" where
"pb5 \<equiv> \<lparr>insts = il5, op_proc = 3, atom_pair_id = None\<rparr>"

definition this_pbm:: "program_block_map" where
"this_pbm \<equiv> (((((emp_prog_block_map(0 := pb0))(1 := pb1))
  (2 := pb2))(3 := pb3))(4 := pb4))(5 := pb5)"

definition this_po:: "program_order" where
"this_po \<equiv> ((emp_program_order(1 := [0,1]))(2 := [2,3]))(3 := [4,5])"

text {* Misc proofs. *}
  
lemma type_op0_st: "type_of_mem_op_block (this_pbm 0) = st_block"
  unfolding this_pbm_def pb0_def il0_def type_of_mem_op_block_def
  by auto
    
lemma type_op1_st: "type_of_mem_op_block (this_pbm 1) = st_block"
  unfolding this_pbm_def pb1_def il1_def type_of_mem_op_block_def
  by auto    

lemma type_op2_ld: "type_of_mem_op_block (this_pbm 2) = ld_block"
  unfolding this_pbm_def pb2_def il2_def type_of_mem_op_block_def
  by auto    

lemma proc_op0_1: "proc_of_op 0 this_pbm = 1"
  unfolding proc_of_op_def this_pbm_def pb0_def by auto    
    
lemma proc_op1_1: "proc_of_op 1 this_pbm = 1"
  unfolding proc_of_op_def this_pbm_def pb1_def by auto       
    
lemma proc_op2_2: "proc_of_op 2 this_pbm = 2"
  unfolding proc_of_op_def this_pbm_def pb2_def by auto
    
lemma op0_prog_before_op1: "(0 ;this_po^(proc_of_op 1 this_pbm) 1)"
  using proc_op1_1
  unfolding program_order_before_def list_before_def this_po_def
  apply auto
  by fastforce
    
lemma this_po_1: "this_po 1 = [0,1]"
  unfolding this_po_def by auto

lemma this_po_2: "this_po 2 = [2,3]"
  unfolding this_po_def by auto    
 
lemma op0_non_repeat: "non_repeat_list [0, Suc 0]"
  unfolding non_repeat_list_def
  by simp

lemma op2_non_repeat: "non_repeat_list [2::nat, 3]"
  unfolding non_repeat_list_def 
  by simp
    
lemma op0_pos: "(non_repeat_list_pos 0 (this_po (proc_of_op 0 this_pbm))) = 0"  
  using proc_op0_1 this_po_1 apply auto
  unfolding non_repeat_list_pos_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality op0_non_repeat    
  by auto 

lemma op1_pos: "(non_repeat_list_pos 1 (this_po (proc_of_op 1 this_pbm))) = 1"  
  using proc_op1_1 this_po_1 apply auto  
  unfolding non_repeat_list_pos_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality op0_non_repeat by auto 
    
lemma op2_pos: "(non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm))) = 0"
  using proc_op2_2 this_po_2 apply auto  
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto 
    
text {* The following lemma confirms Figure 46 in SPARCv9 manual that 
memory operation 1 cannot be the first one to be executed. *}

lemma op1_cannot_exe: 
  assumes a1: "exe_list = [valid_initial_exe this_po]"
  shows "\<not> (this_po this_pbm 1 \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> xseq' s')"
proof (rule ccontr)
  assume a2: "\<not> \<not> (this_po this_pbm 1 \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> xseq' s')"
  then have f1: "this_po this_pbm 1 \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> xseq' s'"
    by auto
  have f3: "\<forall>opid'. (opid' ;this_po^(proc_of_op 1 this_pbm) 1) \<and>
         (type_of_mem_op_block (this_pbm opid') = ld_block \<or>
          type_of_mem_op_block (this_pbm opid') = ald_block \<or>
          type_of_mem_op_block (this_pbm opid') = st_block \<or> 
          type_of_mem_op_block (this_pbm opid') = ast_block) \<longrightarrow>
         List.member (fst (last exe_list)) opid'"
    using mem_op_elim_store_op[OF f1 type_op1_st] by blast
  then have "List.member (fst (last exe_list)) 0"
    using f3 op0_prog_before_op1 type_op0_st by auto
  then show False 
    using a1 unfolding valid_initial_exe_def
    by (simp add: member_rec(2)) 
qed  
    
text {* Next, we show a partial execution of the sequence 012345 from 
the SPARCv9 manual. *}
  
text {* Below are lemmas about the execution of memory operation block 0. *}  
  
lemma il0_0_exe: "(proc_exe (Suc 0) (logic_type ORs, [Flag 1, W5 0, Simm13 1, W5 4]) 0 None None
                 \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg, mem = emp_mem,
                    mem_ops = emp_mem_ops, proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var,
                    glob_var = init_glob_var, undef = False\<rparr>) = 
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1)), mem = emp_mem,
       mem_ops = emp_mem_ops, proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var,
       glob_var = init_glob_var, undef = False\<rparr>"
  unfolding proc_exe_def
  apply auto
  unfolding logical_instr_def
  apply auto
  unfolding get_operand2_def
  apply auto
  unfolding logical_result_def sign_ext13_def
  apply auto
  unfolding gen_reg_val_def emp_gen_reg_def
  apply auto
  unfolding gen_reg_mod_def
  by auto
  
lemma il0_1_exe: "(proc_exe (Suc 0) (logic_type ORs, [Flag 1, W5 0, Simm13 1, W5 5]) 0 None None
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1)), mem = emp_mem,
       mem_ops = emp_mem_ops, proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var,
       glob_var = init_glob_var, undef = False\<rparr>) = 
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)), mem = emp_mem,
       mem_ops = emp_mem_ops, proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var,
       glob_var = init_glob_var, undef = False\<rparr>"
  unfolding proc_exe_def
  apply auto
  unfolding logical_instr_def
  apply auto
  unfolding get_operand2_def
  apply auto
  unfolding logical_result_def sign_ext13_def
  apply auto
  unfolding gen_reg_val_def emp_gen_reg_def
  apply auto
  unfolding gen_reg_mod_def
  by auto
    
lemma il0_2_exe: "(proc_exe (Suc 0) (load_store_type ST, [Flag 0, W5 0, W5 4, W5 5]) 0 None None
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)), mem = emp_mem,
       mem_ops = emp_mem_ops, proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var,
       glob_var = init_glob_var, undef = False\<rparr>) = 
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)), mem = emp_mem,
       mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>"
  unfolding proc_exe_def
  apply auto
  unfolding store_instr_def
  apply auto
  unfolding get_addr_def get_operand_w5_def get_operand2_def gen_reg_val_def
  apply auto
  unfolding mem_op_addr_mod_def mem_op_val_mod_def
  by auto
    
lemma il0_exe: "(mem_commit 0 (next_proc_op_pos_mod (Suc 0) (Suc 0) 
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)), mem = emp_mem,
  mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
  proc_exe_pos = \<lambda>p. 0, proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>)) =
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, 
  glob_var = init_glob_var, undef = False\<rparr>"    
  unfolding next_proc_op_pos_mod_def
  apply auto
  unfolding mem_commit_def get_mem_op_state_def
  apply auto
  unfolding mem_mod_def
  by auto  
  
lemma op0_exe:
  assumes a1: "exe_list0 = [valid_initial_exe this_po]"
  and a2: "this_po this_pbm 0 \<turnstile>m (fst (last exe_list0)) (snd (snd (last exe_list0))) \<rightarrow> xseq1 s1"
shows "xseq1 = [0] \<and> 
       s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)
    (4 := 1, 5 := 1)), mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), 
    proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>"
proof -
  have f1: "xseq1 = (fst (last exe_list0)) @ [0] \<and>
    s1 = mem_commit 0 (proc_exe_to (proc_of_op 0 this_pbm) this_po this_pbm 
     (non_repeat_list_pos 0 (this_po (proc_of_op 0 this_pbm))) 
     (snd (snd (last exe_list0))))"
    using mem_op_elim_store_op[OF a2 type_op0_st] by auto
  from f1 have f2: "xseq1 = (fst (last exe_list0)) @ [0]"
    by auto
  from a1 f2 have f2_1: "xseq1 = [0]"    
    unfolding valid_initial_exe_def
    by auto
  from f1 have f3: "s1 = mem_commit 0 (proc_exe_to (proc_of_op 0 this_pbm) this_po this_pbm 
     (non_repeat_list_pos 0 (this_po (proc_of_op 0 this_pbm))) 
     (snd (snd (last exe_list0))))"
    by auto
  then have f4: "s1 = (mem_commit 0 (proc_exe_to 1 this_po this_pbm 0  
    valid_initial_state))"
    using op0_pos proc_op0_1 a1 valid_initial_exe_def
    by auto
  then have f5: "s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)
    (4 := 1, 5 := 1)), mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), 
    proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>"
    unfolding proc_exe_to_def seq_proc_blk_exe_def valid_initial_state_def init_proc_exe_pos_def
      this_po_def this_pbm_def pb0_def il0_def
    apply auto
    using il0_0_exe il0_1_exe il0_2_exe il0_exe
    by auto
  from f2_1 f5 show ?thesis by auto
qed
  
text {* Below are lemmas about the execution of memory operation block 1. *}
  
lemma il1_0_exe: "(proc_exe (Suc 0) (logic_type ORs, [Flag 1, W5 0, Simm13 1, W5 5]) 
  (Suc 0) None None \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)
  (4 := 1, 5 := 1)), mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0
  \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), 
  proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, 
  glob_var = init_glob_var, undef = False\<rparr>"  
  unfolding proc_exe_def
  apply auto
  unfolding logical_instr_def
  apply auto
  unfolding get_operand2_def
  apply auto
  unfolding logical_result_def sign_ext13_def
  apply auto
  unfolding gen_reg_val_def emp_gen_reg_def
  apply auto
  unfolding gen_reg_mod_def
  by auto
  
lemma il1_1_exe: "(proc_exe (Suc 0) (logic_type ORs, [Flag 1, W5 0, Simm13 2, W5 4]) (Suc 0) None None
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(4 := 1, 5 := 1)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, 
  glob_var = init_glob_var, undef = False\<rparr>) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, 
  glob_var = init_glob_var, undef = False\<rparr>"    
  unfolding proc_exe_def
  apply auto
  unfolding logical_instr_def
  apply auto
  unfolding get_operand2_def
  apply auto
  unfolding logical_result_def sign_ext13_def
  apply auto
  unfolding gen_reg_val_def emp_gen_reg_def
  apply auto
  unfolding gen_reg_mod_def
  by auto  
    
lemma il1_2_exe: "(proc_exe (Suc 0) (load_store_type ST, [Flag 0, W5 0, W5 4, W5 5]) (Suc 0) None None
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, 
  glob_var = init_glob_var, undef = False\<rparr>) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
  proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
  undef = False\<rparr>"
  unfolding proc_exe_def
  apply auto
  unfolding store_instr_def
  apply auto
  unfolding get_addr_def get_operand_w5_def get_operand2_def gen_reg_val_def
  apply auto
  unfolding mem_op_addr_mod_def mem_op_val_mod_def
  by auto
  
lemma il1_exe: "mem_commit (Suc 0) (next_proc_op_pos_mod (Suc 0) (Suc (Suc 0))
  \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
  mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
  proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
  undef = False\<rparr>) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
  mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
  \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
  op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
  glob_var = init_glob_var, undef = False\<rparr>"
  unfolding next_proc_op_pos_mod_def
  apply auto
  unfolding mem_commit_def get_mem_op_state_def
  apply auto
  unfolding mem_mod_def
  by auto  
    
lemma op1_exe: 
  assumes a1: "this_po this_pbm 1 \<turnstile>m [0] s1 \<rightarrow> xseq2 s2"
  and a2: "s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)
    (4 := 1, 5 := 1)), mem = emp_mem(1 \<mapsto> 1), mem_ops = emp_mem_ops(0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc 0), 
    proc_var = init_proc_var, glob_var = init_glob_var, undef = False\<rparr>"
shows "xseq2 = [0,1] \<and>
       s2 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
    op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
proof -
  have f1: "xseq2 = [0] @ [1] \<and>
    s2 = mem_commit 1 (proc_exe_to (proc_of_op 1 this_pbm) this_po this_pbm 
    (non_repeat_list_pos 1 (this_po (proc_of_op 1 this_pbm))) s1)"
    using mem_op_elim_store_op[OF a1 type_op1_st] by auto
  from f1 have f2: "xseq2 = [0,1]"
    by auto
  from f1 have f3: "s2 = mem_commit 1 (proc_exe_to (proc_of_op 1 this_pbm) this_po this_pbm 
    (non_repeat_list_pos 1 (this_po (proc_of_op 1 this_pbm))) s1)"
    by auto
  then have f4: "s2 = mem_commit 1 (proc_exe_to 1 this_po this_pbm 1 s1)"
    using proc_op1_1 op1_pos by auto
  then have f5: "s2 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
    op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
    using a2 apply auto
    unfolding proc_exe_to_def seq_proc_blk_exe_def this_po_def this_pbm_def pb1_def il1_def
    apply auto
    using il1_0_exe il1_1_exe il1_2_exe il1_exe by auto
  show ?thesis using f2 f5 by auto
qed
  
text {* Below are lemmas about the execution of memory operation block 2. *}  

lemma op2_pre_exe: "(proc_exe_to_previous 2 this_po this_pbm 0  
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
    op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
  mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
  proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
  glob_var = init_glob_var, undef = False\<rparr>"
  unfolding proc_exe_to_previous_def this_po_def this_pbm_def pb2_def il2_def 
  apply auto
  unfolding proc_exe_def logical_instr_def
  apply auto
  unfolding gen_reg_val_def get_operand2_def
  apply auto
  unfolding logical_result_def sign_ext13_def gen_reg_mod_def
  by auto
    
lemma op2_load_addr: "(load_addr 2 (last (insts (this_pbm 2))) 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
  mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
  op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
  proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
  glob_var = init_glob_var, undef = False\<rparr>) = 2"
  unfolding this_pbm_def pb2_def il2_def proc_of_op_def
  apply auto
  unfolding load_addr_def get_addr_def get_operand2_def get_operand_w5_def gen_reg_val_def  
  by auto
        
lemma op2_load_val_mo_st: 
  assumes a1: "s2_1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
    op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
    proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
shows "{opid'. (opid' m<[0, 1] 2) = Some True \<and> 
  (type_of_mem_op_block (this_pbm opid') \<in> {st_block, ast_block}) \<and> Some 2 = 
  op_addr (get_mem_op_state opid' s2_1)} = {1}"
proof -
  have f1: "\<not>(List.member [0,(1::nat)] (2::nat))"
    by (simp add: member_rec(1) member_rec(2))    
  have f2: "\<forall>opid'. ((opid' m<[0, 1] 2) = Some True) \<longleftrightarrow> opid'\<in>{0,1}"
    using f1 mem_order_true_cond_equiv
    by (metis insert_iff mem_order_true_cond_rev member_rec(1) member_rec(2) singletonD) 
  have f3_0: "op_addr (get_mem_op_state 0 s2_1) = Some 1"
    using a1 unfolding get_mem_op_state_def by auto
  have f3_1: "op_addr (get_mem_op_state 1 s2_1) = Some 2"
    using a1 unfolding get_mem_op_state_def by auto
  have f5: "{opid'. opid'\<in>{0,1} \<and> 
    (type_of_mem_op_block (this_pbm opid') \<in> {st_block, ast_block}) \<and> 
    Some 2 = op_addr (get_mem_op_state opid' s2_1)} = {1}"
    using type_op0_st type_op1_st f3_0 f3_1 by auto
  then show ?thesis using f2 by auto
qed
  
lemma op2_load_val_po_st:
  assumes a1: "s2_1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
    op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
    proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
shows "{opid''. (opid'' ;this_po^2 2) \<and> 
  (type_of_mem_op_block (this_pbm opid'') \<in> {st_block, ast_block}) \<and> 
  Some 2 = op_addr (get_mem_op_state opid'' s2_1)} = {}"
  unfolding this_po_def emp_program_order_def program_order_before_def
    list_before_def
  by auto
  
lemma op2_load_max_st: "max_mem_order {1} 2 this_po [0, Suc 0] = Some 1"
  unfolding max_mem_order_def
  by (auto simp add: member_rec(1))
    
lemma op2_load_val: 
  assumes a1: "s2_1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
    op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
    proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
  shows "(axiom_value 2 2 2 this_po [0, 1] this_pbm s2_1) = Some 1"
proof -
  have f1: "({opid'.
             (opid' m<[0, Suc 0] 2) = Some True \<and>
             (type_of_mem_op_block (this_pbm opid') = st_block \<or>
              type_of_mem_op_block (this_pbm opid') = ast_block) \<and>
             Some 2 = op_addr (get_mem_op_state opid' s2_1)} \<union>
            {opid''.
             (opid'' ;this_po^2 2) \<and>
             (type_of_mem_op_block (this_pbm opid'') = st_block \<or>
              type_of_mem_op_block (this_pbm opid'') = ast_block) \<and>
             Some 2 = op_addr (get_mem_op_state opid'' s2_1)}) = {1}"
    using op2_load_val_mo_st[OF a1] op2_load_val_po_st[OF a1]
    by auto
  have f2: "op_val (get_mem_op_state 1 s2_1) = Some 1"
    using a1 unfolding get_mem_op_state_def by auto
  show ?thesis
  unfolding axiom_value_def 
  apply auto
  using f1 op2_load_max_st f2
  by auto
qed    
  
lemma op2_exe: 
  assumes a1: "this_po this_pbm 2 \<turnstile>m [0,1] s2 \<rightarrow> xseq3 s3"
  and a2: "s2 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
    op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
shows "xseq3 = [0,1,2] \<and>
       s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2, 1 := 1)),
            mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>,
               2 := emp_mem_ops 2\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
            glob_var = init_glob_var, undef = False\<rparr>"
proof-
  have f1: "xseq3 = [0,1] @ [2] \<and> 
    s3 = proc_exe_to_last (proc_of_op 2 this_pbm) this_po this_pbm
    (non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm)))
    (axiom_value (proc_of_op 2 this_pbm) 2 (load_addr (proc_of_op 2 this_pbm) 
     (last (insts (this_pbm 2))) (proc_exe_to_previous (proc_of_op 2 this_pbm) this_po this_pbm
      (non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm))) s2)) 
      this_po [0, 1] this_pbm
      (proc_exe_to_previous (proc_of_op 2 this_pbm) this_po this_pbm
        (non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm))) s2))
    (Some (load_addr (proc_of_op 2 this_pbm) (last (insts (this_pbm 2))) 
    (proc_exe_to_previous (proc_of_op 2 this_pbm) this_po this_pbm
      (non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm))) s2)))
    (proc_exe_to_previous (proc_of_op 2 this_pbm) this_po this_pbm
      (non_repeat_list_pos 2 (this_po (proc_of_op 2 this_pbm))) s2)"
    using mem_op_elim_load_op[OF a1 type_op2_ld] by auto
  then have f2: "xseq3 = [0,1,2]"
    by auto
  define s2_1 where "s2_1 \<equiv> proc_exe_to_previous 2 this_po this_pbm 0 s2"
  have f3: "s2_1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, 
    op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
    proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
    using op2_pre_exe s2_1_def a2 by auto
  from f1 have f4: "s3 = proc_exe_to_last 2 this_po this_pbm 0 (axiom_value 2 2 (load_addr 2 
     (last (insts (this_pbm 2))) s2_1)  this_po [0, 1] this_pbm s2_1) 
     (Some (load_addr 2 (last (insts (this_pbm 2))) s2_1)) s2_1"
    using proc_op2_2 op2_pos s2_1_def by auto
  then have f5: "s3 = proc_exe_to_last 2 this_po this_pbm 0 (axiom_value 2 2 2 this_po [0, 1] 
    this_pbm s2_1) (Some 2) s2_1"
    using op2_load_addr f3 by auto
  then have f6: "s3 = proc_exe_to_last 2 this_po this_pbm 0 (Some 1) (Some 2) s2_1"
    using op2_load_val[OF f3] by auto 
  then have f7: "proc_exe_to_last 2 this_po this_pbm 0 (Some 1) (Some 2) s2_1 = 
    \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2, 1 := 1)),
            mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>,
               2 := emp_mem_ops 2\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
            glob_var = init_glob_var, undef = False\<rparr>"
    unfolding proc_exe_to_last_def this_po_def this_pbm_def pb2_def il2_def
    apply auto 
    unfolding proc_exe_def
    apply auto
    unfolding load_instr_def gen_reg_mod_def mem_op_addr_mod_def 
      mem_op_val_mod_def next_proc_op_pos_mod_def
    using f3 by auto
  show ?thesis using f2 f7 f6 by auto
qed  
      
lemma op2_exe_result: 
  assumes a1: "this_po this_pbm 2 \<turnstile>m [0,1] s2 \<rightarrow> xseq3 s3"
  and a2: "s2 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2)),
    mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1), mem_ops = emp_mem_ops (0 := emp_mem_ops 0
    \<lparr>op_addr := Some 1, op_val := Some 1\<rparr>, Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, 
    op_val := Some 1\<rparr>), proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
    glob_var = init_glob_var, undef = False\<rparr>"
shows "xseq3 = [0,1,2] \<and> (gen_reg s3) 2 1 = 1"
proof -
  have f1: "xseq3 = [0,1,2] \<and>
       s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(Suc 0 := (\<lambda>r. 0)(5 := 1, 4 := 2), 2 := (\<lambda>r. 0)(4 := 2, 1 := 1)),
            mem = emp_mem(1 \<mapsto> 1, 2 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>,
               2 := emp_mem_ops 2\<lparr>op_addr := Some 2, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
            glob_var = init_glob_var, undef = False\<rparr>"
    using op2_exe[OF a1 a2] by auto
  then show ?thesis by auto
qed  
  
subsection {* Spin-lock with Compare and Swap. *}  
  
definition e2il_init:: "instruction list" where
"e2il_init \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 in r4 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 4))]),
(load_store_type ST, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> store the value in r0 to mem[r4 (1)] \<close>
  (W5 (word_of_int 4)), (W5 (word_of_int 0))]) \<comment>\<open> That is, we assume address lock = 1. \<close>
]"  \<comment>\<open> This block means: st #1 [1] \<close>  
  
definition e2il0:: "instruction list" where
"e2il0 \<equiv> [
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 (ID of processor 1) in r16, which is l0 \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 16))]),
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 (address of lock)  in r1. \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 1))]),
(load_store_type CASA_LD, [(Flag (word_of_int 0)), (W5 (word_of_int 1)), \<comment>\<open> if mem[r[r1]] = 0 then swap mem[r[r1]] with r[r16]. Otherwise r[r16] <- mem[r[r1]]. \<close>
  (W5 (word_of_int 0)), (Asi (word_of_int 11)), (W5 (word_of_int 16))]) \<comment>\<open> That is, we assume address lock = 1. \<close>
]"   

definition e2il1:: "instruction list" where
  "e2il1 \<equiv> [(load_store_type CASA_ST, [(Flag (word_of_int 0)), (W5 (word_of_int 1)), \<comment>\<open> if mem[r[r1]] = 0 then swap mem[r[r1]] with r[r16]. Otherwise r[r16] <- mem[r[r1]]. \<close>
  (W5 (word_of_int 0)), (Asi (word_of_int 11)), (W5 (word_of_int 16))]) \<comment>\<open> That is, we assume address lock = 1. \<close>]"
  
definition e2il2:: "instruction list" where
"e2il2 \<equiv> [
(logic_type ORcc,[(Flag (word_of_int 0)),
                        (W5 (word_of_int 0)),
                        (W5 (word_of_int 16)),
                        (W5 (word_of_int 0))]), \<comment>\<open> Compare if r[r16] = 0. Write condition codes. \<close>
(bicc_type BE,[(Flag (word_of_int (get_a 0))),
                (W22 (word_of_int (get_disp_imm22 28)))]), \<comment>\<open> Branch to PC + 28 (out/critical region) if r[r16] != 0. \<close>
(nop_type NOP,[])
]"    
  
definition e2il5:: "instruction list" where
"e2il5 \<equiv> [
(logic_type ORcc,[(Flag (word_of_int 0)),
                        (W5 (word_of_int 0)),
                        (W5 (word_of_int 16)),
                        (W5 (word_of_int 0))]), \<comment>\<open> Compare if r[r16] = 0. Write condition codes. \<close>
(bicc_type BNE,[(Flag (word_of_int (get_a 0))),
                (W22 (word_of_int (get_disp_imm22 (-12))))]), \<comment>\<open> Branch to loop if r[r16] != 0. \<close>
(nop_type NOP,[]),
(logic_type ORs,[(Flag (word_of_int 1)), \<comment>\<open> put 0 OR 1 = 1 (address of lock)  in r1. \<close>
                       (W5 (word_of_int 0)),
                       (Simm13 (word_of_int 1)),
                       (W5 (word_of_int 1))]),
(load_store_type LD, [(Flag (word_of_int 0)), (W5 (word_of_int 0)), \<comment>\<open> load the value in mem[0 + r[r1]] to r16. \<close>
  (W5 (word_of_int 1)), (W5 (word_of_int 16))])
]"  
  
definition e2pb_init:: "program_block" where
"e2pb_init \<equiv> \<lparr>insts = e2il_init, op_proc = 3, atom_pair_id = None\<rparr>"

definition e2pb0:: "program_block" where
"e2pb0 \<equiv> \<lparr>insts = e2il0, op_proc = 1, atom_pair_id = None\<rparr>"

definition e2pb1:: "program_block" where
"e2pb1 \<equiv> \<lparr>insts = e2il1, op_proc = 1, atom_pair_id = Some 0\<rparr>"

definition e2pb2:: "program_block" where
"e2pb2 \<equiv> \<lparr>insts = e2il0, op_proc = 2, atom_pair_id = None\<rparr>"

definition e2pb3:: "program_block" where
"e2pb3 \<equiv> \<lparr>insts = e2il1, op_proc = 2, atom_pair_id = Some 2\<rparr>"

definition e2pb5:: "program_block" where
"e2pb5 \<equiv> \<lparr>insts = e2il2, op_proc = 1, atom_pair_id = None\<rparr>"

definition e2pb6:: "program_block" where
"e2pb6 \<equiv> \<lparr>insts = e2il2, op_proc = 2, atom_pair_id = None\<rparr>"

definition pbm2:: "program_block_map" where
"pbm2 \<equiv> (((((((emp_prog_block_map(0 := e2pb0))(1 := e2pb1))
  (2 := e2pb2))(3 := e2pb3)))(4 := e2pb_init))(5 := e2pb5))(6 := e2pb6)"

definition po2:: "program_order" where
"po2 \<equiv> ((emp_program_order(1 := [0,1,5]))(2 := [2,3,6]))(3 := [4])"

lemma e2_type_op4_st: "type_of_mem_op_block (pbm2 4) = st_block"
  unfolding pbm2_def e2pb_init_def e2il_init_def type_of_mem_op_block_def
  by auto    

lemma e2_type_op0_st: "type_of_mem_op_block (pbm2 0) = ald_block"
  unfolding pbm2_def e2pb0_def e2il0_def type_of_mem_op_block_def
  by auto

lemma e2_type_op1_st: "type_of_mem_op_block (pbm2 1) = ast_block"
  unfolding pbm2_def e2pb1_def e2il1_def type_of_mem_op_block_def
  by auto
    
lemma e2_type_op2_st: "type_of_mem_op_block (pbm2 2) = ald_block"
  unfolding pbm2_def e2pb2_def e2il0_def type_of_mem_op_block_def
  by auto    

lemma e2_type_op3_st: "type_of_mem_op_block (pbm2 3) = ast_block"
  unfolding pbm2_def e2pb3_def e2il1_def type_of_mem_op_block_def
  by auto
    
lemma e2_type_op5_st: "type_of_mem_op_block (pbm2 5) = o_block"
  unfolding pbm2_def e2pb5_def e2il2_def type_of_mem_op_block_def
  by auto    

lemma e2_type_op6_st: "type_of_mem_op_block (pbm2 6) = o_block"
  unfolding pbm2_def e2pb6_def e2il2_def type_of_mem_op_block_def
  by auto    
    
lemma e2_proc_op4_3: "proc_of_op 4 pbm2 = 3"
  unfolding proc_of_op_def pbm2_def e2pb_init_def by auto      
    
lemma e2_proc_op0_1: "proc_of_op 0 pbm2 = 1"
  unfolding proc_of_op_def pbm2_def e2pb0_def by auto        
    
lemma e2_proc_op1_1: "proc_of_op 1 pbm2 = 1"
  unfolding proc_of_op_def pbm2_def e2pb1_def by auto            
    
lemma e2_proc_op2_2: "proc_of_op 2 pbm2 = 2"
  unfolding proc_of_op_def pbm2_def e2pb2_def by auto                
    
lemma e2_proc_op3_2: "proc_of_op 3 pbm2 = 2"
  unfolding proc_of_op_def pbm2_def e2pb3_def by auto                    
    
lemma e2_proc_op5_1: "proc_of_op 5 pbm2 = 1"
  unfolding proc_of_op_def pbm2_def e2pb5_def by auto     
    
lemma e2_proc_op6_2: "proc_of_op 6 pbm2 = 2"
  unfolding proc_of_op_def pbm2_def e2pb6_def by auto         
    
lemma po2_3: "po2 3 = [4]"
  unfolding po2_def by auto      
    
lemma po2_1: "po2 1 = [0,1,5]"
  unfolding po2_def by auto    
    
lemma po2_2: "po2 2 = [2,3,6]"
  unfolding po2_def by auto        
   
lemma e2_op4_pos: "(non_repeat_list_pos 4 (po2 3)) = 0"  
  using po2_3 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto
    
lemma e2_op0_pos: "(non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2))) = 0"  
  using e2_proc_op0_1 po2_1 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto     
    
lemma e2_op1_pos: "(non_repeat_list_pos 1 (po2 (proc_of_op 1 pbm2))) = 1"
  using e2_proc_op1_1 po2_1 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto
    
lemma e2_op2_pos: "(non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2))) = 0"
  using e2_proc_op2_2 po2_2 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto 
    
lemma e2_op2_pos2: "(non_repeat_list_pos (2::nat) [2,3,6]) = 0"    
  using e2_op2_pos e2_proc_op2_2 unfolding po2_def
  by auto
  
lemma e2_op3_pos: "(non_repeat_list_pos 3 (po2 (proc_of_op 3 pbm2))) = 1"
  using e2_proc_op3_2 po2_2 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto     
    
lemma e2_op5_pos: "(non_repeat_list_pos 5 (po2 1)) = 2"
  using po2_1 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality   by auto
    
lemma e2_op6_pos: "(non_repeat_list_pos 6 (po2 2)) = 2"
  using po2_2 apply auto
  unfolding non_repeat_list_pos_def non_repeat_list_def
  using less_Suc_eq_0_disj nth_Cons_Suc the_equality by auto    
    
lemma e2_op4_il_exe: "mem_commit 4 (proc_exe_to 3 po2 pbm2 0 valid_initial_state) = 
\<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg(3 := (emp_gen_reg 3)(4 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  unfolding proc_exe_to_def valid_initial_state_def init_proc_exe_pos_def
    po2_def pbm2_def e2pb_init_def e2il_init_def
  apply auto
  apply (simp add: proc_exe_def)
  apply (simp add: logical_instr_def Let_def logical_result_def gen_reg_val_def 
   get_operand2_def sign_ext13_def emp_gen_reg_def gen_reg_mod_def)
  apply (simp add: store_instr_def mem_op_addr_mod_def gen_reg_val_def mem_op_val_mod_def
   get_addr_def get_operand2_def emp_mem_ops_def emp_gen_reg_def)
  by (simp add: next_proc_op_pos_mod_def mem_commit_def Let_def get_mem_op_state_def
   mem_mod_def)
    
lemma e2_op4_exe:
  assumes a1: "exe_list0 = [valid_initial_exe po2]"
  and a2: "po2 pbm2 4 \<turnstile>m (fst (last exe_list0)) (snd (snd (last exe_list0))) \<rightarrow> xseq1 s1"
shows "xseq1 = [4] \<and> 
       s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg(3 := (emp_gen_reg 3)(4 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"   
proof -
  have f1: "xseq1 = [4] \<and>
    s1 = mem_commit 4 (proc_exe_to (proc_of_op 4 pbm2) po2 pbm2 
    (non_repeat_list_pos 4 (po2 (proc_of_op 4 pbm2))) valid_initial_state)"
    using mem_op_elim_store_op[OF a2 e2_type_op4_st] a1 unfolding valid_initial_exe_def
    by auto
  from f1 have f2: "xseq1 = [4]"
    by auto
  from f1 have f3: "s1 = mem_commit 4 (proc_exe_to (proc_of_op 4 pbm2) po2 pbm2 
    (non_repeat_list_pos 4 (po2 (proc_of_op 4 pbm2))) valid_initial_state)"
    by auto
  then have f4: "s1 = mem_commit 4 (proc_exe_to 3 po2 pbm2 0 valid_initial_state)"
    using e2_op4_pos e2_proc_op4_3 by auto
  then show ?thesis using f2 e2_op4_il_exe by auto
qed
    
lemma e2_pre_s: 
  assumes a1: "s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg(3 := (emp_gen_reg 3)(4 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  shows "proc_exe_to_previous 1 po2 pbm2 0 s1 = 
  \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"    
  unfolding valid_initial_state_zero_mem_def proc_exe_to_previous_def 
    init_proc_exe_pos_def po2_def
  using a1
  apply auto
  unfolding pbm2_def e2pb0_def e2il0_def
  apply auto
  apply (simp add: proc_exe_def Let_def)
  apply (simp add: logical_instr_def Let_def logical_result_def)
  unfolding gen_reg_val_def gen_reg_mod_def get_operand2_def sign_ext13_def emp_gen_reg_def
  by auto    
    
lemma e2_op0_addr: "(atomic_load_addr 1 (last (insts (pbm2 0)))
      \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>) = 1"
  unfolding atomic_load_addr_def pbm2_def e2pb0_def e2il0_def
  apply auto
  unfolding casa_load_addr_def gen_reg_val_def get_operand_w5_def
  by auto        

lemma e2_op0_load_val1:
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  shows "{opid'. (opid' m<[4] 0) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} = {4}"
proof -
  have f1: "(4 m<[4] 0) = Some True"
    unfolding memory_order_before_def
    by (simp add: member_rec(1) member_rec(2))
  have f2: "type_of_mem_op_block (pbm2 4) \<in> {st_block, ast_block}"
    unfolding type_of_mem_op_block_def pbm2_def e2pb_init_def e2il_init_def
    by auto
  have f3: "Some 1 = op_addr (get_mem_op_state 4 s)"
    unfolding get_mem_op_state_def 
    using a1
    by auto
  have f4: "\<forall>opid'. ((opid' m<[4] 0) = Some True) \<longleftrightarrow> opid'\<in>{4}"
    using f1 mem_order_true_cond_equiv
    by (metis insert_iff member_rec(1) member_rec(2) singletonD)
  then show ?thesis using f1 f2 f3 by auto
qed
    
lemma e2_op0_load_val2:
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  shows "{opid''. (opid'' ;po2^1 0) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)} = {}"  
  unfolding po2_def emp_program_order_def program_order_before_def
    list_before_def
  apply auto
  using less_Suc_eq_0_disj apply fastforce
  using less_Suc_eq_0_disj by fastforce
  
lemma e2_op0_load_val: 
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  shows "(axiom_value 1 0 1 po2 [4] pbm2 s) = Some 0"    
proof -
  have f1: "{opid'. (opid' m<[4] 0) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} \<union>
            {opid''. (opid'' ;po2^1 0) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)} = {4}"
    using e2_op0_load_val1[OF a1] e2_op0_load_val2[OF a1] a1 by auto
  then have f2: "max_mem_order
           ({opid'.(opid' m<[4] 0) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} \<union>
            {opid''.(opid'' ;po2^1 0) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)})
           1 po2 [4] = Some 4"
    unfolding max_mem_order_def
    by auto
  then show ?thesis unfolding axiom_value_def
    using a1 apply auto
    unfolding get_mem_op_state_def
    by auto
qed
    
lemma e2_op0_exe_last: "proc_exe_to_last 1 po2 pbm2
    0 (Some 0) (Some 1) \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr> = 
  \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1\<rparr>, undef = False\<rparr>"
  unfolding proc_exe_to_last_def po2_def pbm2_def e2pb0_def e2il0_def
    atomic_load_addr_def casa_load_addr_def gen_reg_val_def 
  apply (auto simp add: proc_exe_def)
  by (simp add: casa_load_def gen_reg_val_def atomic_rd_mod_def
    gen_reg_mod_def mem_op_addr_mod_def mem_op_val_mod_def next_proc_op_pos_mod_def)   
    
lemma e2_op0_exe:
  assumes a1: "s1 = \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg(3 := (emp_gen_reg 3)(4 := 1)),
       mem = emp_mem(1 \<mapsto> 0), mem_ops = emp_mem_ops(4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0), proc_var = init_proc_var, glob_var = init_glob_var,
       undef = False\<rparr>"
  and a2: "po2 pbm2 0 \<turnstile>m [4] s1 \<rightarrow> xseq2 s2"
shows "xseq2 = [4,0] \<and> 
       s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
proof -
  have f1: "xseq2 = [4] @ [0] \<and>
    s2 = atomic_flag_mod (Some 0)
         (proc_exe_to_last (proc_of_op 0 pbm2) po2 pbm2
           (non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2)))
           (axiom_value (proc_of_op 0 pbm2) 0
             (atomic_load_addr (proc_of_op 0 pbm2) (last (insts (pbm2 0)))
               (proc_exe_to_previous (proc_of_op 0 pbm2) po2 pbm2
                 (non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2))) s1))
             po2 [4] pbm2
             (proc_exe_to_previous (proc_of_op 0 pbm2) po2 pbm2
               (non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2))) s1))
           (Some (atomic_load_addr (proc_of_op 0 pbm2) (last (insts (pbm2 0)))
                   (proc_exe_to_previous (proc_of_op 0 pbm2) po2 pbm2
                     (non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2))) s1)))
           (proc_exe_to_previous (proc_of_op 0 pbm2) po2 pbm2
             (non_repeat_list_pos 0 (po2 (proc_of_op 0 pbm2))) s1))"
    using mem_op_elim_atom_load_op[OF a2 e2_type_op0_st] by auto
  from f1 have f2: "xseq2 = [4] @ [0]"
    by auto
  from a1 f2 have f2_1: "xseq2 = [4,0]"    
    unfolding valid_initial_exe_zero_mem_def
    by auto
  from f1 have f3: "s2 = atomic_flag_mod (Some 0) (proc_exe_to_last 1 po2 pbm2
    0 (Some 0) (Some 1) (proc_exe_to_previous 1 po2 pbm2 0 s1))"
    using a1 valid_initial_exe_def e2_op0_pos e2_proc_op0_1 
      e2_pre_s e2_op0_addr e2_op0_load_val by auto
  then have f4: "s2 = atomic_flag_mod (Some 0) \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1\<rparr>, undef = False\<rparr>"
    using e2_pre_s[OF a1] e2_op0_exe_last 
    by auto
  then have f5: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
    unfolding atomic_flag_mod_def
    by auto
  then show ?thesis using f2_1 by auto 
qed  
  
lemma e2_op2_cannot_exe: 
  assumes a1: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
shows "\<not> (po2 pbm2 2 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"
proof (rule ccontr)
  assume a2: "\<not> \<not> (po2 pbm2 2 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"
  then have f1: "po2 pbm2 2 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s'"
    by auto
  have f3: "atomic_flag_val s2 = None"
    using mem_op_elim_atom_load_op[OF f1 e2_type_op2_st] by blast          
  then show False 
    using a1 unfolding atomic_flag_val_def by auto     
qed  
  
lemma e2_op3_cannot_exe: 
  assumes a1: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
  shows "\<not> (po2 pbm2 3 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"  
proof (rule ccontr)
  assume a2: "\<not> \<not> (po2 pbm2 3 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"
  then have f1: "po2 pbm2 3 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s'"
    by auto
  obtain opid' where f2: "atomic_flag_val s2 = Some opid' \<and> atom_pair_id (pbm2 3) = Some opid'"
    using mem_op_elim_atom_store_op[OF f1 e2_type_op3_st]
    by fastforce 
  have f3: "atom_pair_id (pbm2 3) = Some 2"
    unfolding pbm2_def e2pb3_def
    by auto
  then have f4: "atomic_flag_val s2 = Some 2" 
    using f2 by auto
  then show False
    using a1 unfolding atomic_flag_val_def
    by auto
qed
  
lemma e2_op6_cannot_exe: 
  assumes a1: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
  shows "\<not> (po2 pbm2 6 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"  
proof (rule ccontr)
  assume a2: "\<not> \<not> (po2 pbm2 6 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"
  then have f1: "po2 pbm2 6 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s'"
    by auto
  then have f2: "\<forall>opid'. (opid' ;po2^(proc_of_op 6 pbm2) 6) \<and>
      (type_of_mem_op_block (pbm2 opid') = ld_block \<or>
       type_of_mem_op_block (pbm2 opid') = ald_block \<or>
       type_of_mem_op_block (pbm2 opid') = st_block \<or>
       type_of_mem_op_block (pbm2 opid') = ast_block) \<longrightarrow>
      List.member [4, 0] opid'"
    using mem_op_elim_o_op[OF f1 e2_type_op6_st]
    by blast
  have f3: "2 ;po2^(proc_of_op 6 pbm2) 6"
    unfolding pbm2_def e2pb6_def proc_of_op_def po2_def program_order_before_def
    apply auto
    apply (simp add: list_before_def)
    by fastforce    
  have f4: "type_of_mem_op_block (pbm2 2) = ald_block" 
    unfolding type_of_mem_op_block_def pbm2_def e2pb2_def e2il0_def
    by auto
  from f2 f3 f4 have f5: "List.member [4,0] 2" using member_rec(1) member_rec(2) numeral_eq_iff
    by (metis nat.simps(3) numeral_2_eq_2)  
  then show False
    by (metis Nat.add_0_right add_Suc_right length_0_conv list.size(4) member_rec(1) member_rec(2) numeral_2_eq_2 numeral_eq_iff semiring_norm(85) semiring_norm(87))    
qed  
  
lemma e2_op5_cannot_exe: 
  assumes a1: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
  shows "\<not> (po2 pbm2 5 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"  
proof (rule ccontr)
  assume a2: "\<not> \<not> (po2 pbm2 5 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s')"
  then have f1: "po2 pbm2 5 \<turnstile>m [4,0] s2 \<rightarrow> xseq' s'"
    by auto
  then have f2: "\<forall>opid'. (opid' ;po2^(proc_of_op 5 pbm2) 5) \<and>
      (type_of_mem_op_block (pbm2 opid') = ld_block \<or>
       type_of_mem_op_block (pbm2 opid') = ald_block \<or>
       type_of_mem_op_block (pbm2 opid') = st_block \<or>
       type_of_mem_op_block (pbm2 opid') = ast_block) \<longrightarrow>
      List.member [4, 0] opid'"
    using mem_op_elim_o_op[OF f1 e2_type_op5_st]
    by blast
  have f3: "1 ;po2^(proc_of_op 5 pbm2) 5"
    unfolding pbm2_def e2pb5_def proc_of_op_def po2_def program_order_before_def
    apply auto
    apply (simp add: list_before_def)
    by (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc zero_less_Suc)        
  have f4: "type_of_mem_op_block (pbm2 1) = ast_block" 
    unfolding type_of_mem_op_block_def pbm2_def e2pb1_def e2il1_def
    by auto
  from f2 f3 f4 have f5: "List.member [4,0] 1"
    by (meson member_rec(1) member_rec(2) numeral_eq_one_iff semiring_norm(85) zero_neq_one)
  then show False
    by (metis (no_types, hide_lams) member_rec(1) member_rec(2) numeral_eq_one_iff semiring_norm(85) zero_neq_one)   
qed    
  
lemma e2_op1_exe:
  assumes a1: "s2 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
       mem = emp_mem(1 \<mapsto> 0),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 0\<rparr>, undef = False\<rparr>"
  and a2: "po2 pbm2 1 \<turnstile>m [4,0] s2 \<rightarrow> xseq3 s3"
shows "xseq3 = [4,0,1] \<and> 
       s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
            mem = emp_mem(1 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
               0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
            glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
proof -
  have f1: "xseq3 = [4,0] @ [1] \<and> 
            s3 = mem_commit 1 (atomic_flag_mod None (proc_exe_to (proc_of_op 1 pbm2) po2 pbm2
            (non_repeat_list_pos 1 (po2 (proc_of_op 1 pbm2))) s2))"
    using mem_op_elim_atom_store_op[OF a2 e2_type_op1_st] by auto
  from f1 have f2: "xseq3 = [4,0,1]" by auto
  from f1 have f3: "s3 = mem_commit 1 (atomic_flag_mod None (proc_exe_to (proc_of_op 1 pbm2) 
    po2 pbm2 (non_repeat_list_pos 1 (po2 (proc_of_op 1 pbm2))) s2))"
    by auto
  then have f4: "s3 = mem_commit 1 (atomic_flag_mod None (proc_exe_to 1 po2 pbm2 1 s2))"
    using e2_op1_pos e2_proc_op1_1 by auto
  then have f5: "s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
            mem = emp_mem(1 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
               0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
            glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
    using a1
    unfolding proc_exe_to_def 
    apply (auto simp add: Let_def)
    unfolding pbm2_def po2_def e2pb1_def e2il1_def
     apply auto
    apply (simp add: proc_exe_def casa_store_def)
    unfolding atomic_flag_val_def atomic_rd_val_def casa_load_addr_def gen_reg_val_def
      mem_op_addr_mod_def mem_op_val_mod_def next_proc_op_pos_mod_def
      atomic_flag_mod_def 
    apply auto
    unfolding mem_commit_def
    by (auto simp add: Let_def get_mem_op_state_def mem_mod_def)
  then show ?thesis using f2 by auto
qed  

lemma e2_pre_s4: 
  assumes a1: "s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
            mem = emp_mem(1 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
               0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
            glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  shows "(proc_exe_to_previous 2 po2 pbm2 0 s3) = 
  \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"    
  unfolding proc_exe_to_previous_def 
    po2_def   
  using a1 
  apply auto    
  unfolding pbm2_def e2pb2_def e2il0_def 
  apply auto
  apply (simp add: proc_exe_def Let_def)
  apply (simp add: logical_instr_def Let_def logical_result_def)
  unfolding gen_reg_val_def gen_reg_mod_def get_operand2_def sign_ext13_def emp_gen_reg_def
  by auto      
  
lemma e2_op2_addr: "atomic_load_addr 2 (last (insts (pbm2 2))) 
  \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>
   = 1"    
  unfolding atomic_load_addr_def pbm2_def e2pb2_def e2il0_def
  apply auto
  unfolding casa_load_addr_def gen_reg_val_def
  by auto

lemma e2_op2_load_val1:
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  shows "{opid'. (opid' m<[4, 0, 1] 2) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} = {4,1}"
proof -  
  have f1: "(4 m<[4,0,1] 2) = Some True"
    unfolding memory_order_before_def
    by (simp add: member_rec(1) member_rec(2))
  have f2: "type_of_mem_op_block (pbm2 4) \<in> {st_block, ast_block}"
    unfolding type_of_mem_op_block_def pbm2_def e2pb_init_def e2il_init_def
    by auto
  have f3: "Some 1 = op_addr (get_mem_op_state 4 s)"
    unfolding get_mem_op_state_def 
    using a1
    by auto
  have f4: "(1 m<[4,0,1] 2) = Some True"
    unfolding memory_order_before_def
    by (simp add: member_rec(1) member_rec(2))
  have f5: "type_of_mem_op_block (pbm2 1) \<in> {st_block, ast_block}"
    unfolding type_of_mem_op_block_def pbm2_def e2pb1_def e2il1_def
    by auto
  have f6: "Some 1 = op_addr (get_mem_op_state 1 s)"
    unfolding get_mem_op_state_def 
    using a1
    by auto
  have f7: "(0 m<[4,0,1] 2) = Some True"
    unfolding memory_order_before_def
    by (simp add: member_rec(1) member_rec(2))
  have f8: "type_of_mem_op_block (pbm2 0) \<notin> {st_block, ast_block}"
    unfolding type_of_mem_op_block_def pbm2_def e2pb0_def e2il0_def
    by auto
  have f9: "\<forall>opid'. ((opid' m<[4,0,1] 2) = Some True) \<longleftrightarrow> opid'\<in>{4,0,1}"
    using f1 f4 f7 mem_order_true_cond_equiv
    by (metis insert_iff member_rec(1) member_rec(2) singletonD)
  then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 by auto
qed
    
lemma e2_op2_load_val2:
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  shows "{opid''. (opid'' ;po2^2 2) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)} = {}"  
  unfolding po2_def emp_program_order_def program_order_before_def
    list_before_def
  using less_Suc_eq_0_disj by fastforce
  
lemma e2_op2_load_val_sub1: 
assumes a1: "(4 m<[(4::nat), 0, 1] 1) = Some True"
and a2: "(1 m<[(4::nat), 0, 1] 4) \<noteq> Some True"
shows "(THE opid. (opid = 4 \<or> opid = Suc 0) \<and>
  (\<forall>opid'. (opid' = 4 \<or> opid' = Suc 0) \<and> opid' \<noteq> opid \<longrightarrow>
  (opid' m<[4, 0, Suc 0] opid) = Some True \<or> (opid' ;po2^2 opid))) =
  Suc 0"    
proof -
  have f1: "(\<forall>opid'. (opid' = 4 \<or> opid' = Suc 0) \<and> opid' \<noteq> 1 \<longrightarrow>
    (opid' m<[4, 0, Suc 0] 1) = Some True \<or> (opid' ;po2^2 1))"
    using a1 by auto
  have f2_0: "\<forall>opid'. ((opid' = 4 \<or> opid' = Suc 0) \<and> opid' \<noteq> 4) = (opid' = Suc 0)"
    by auto
  have f2_1: "\<not> (\<forall>opid'. opid' = Suc 0 \<longrightarrow>
    (opid' m<[4, 0, Suc 0] 4) = Some True \<or> (opid' ;po2^2 4))"    
    using a2
    apply auto
    unfolding program_order_before_def po2_def list_before_def
    using less_Suc_eq_0_disj by fastforce
  have f2: "\<not> (\<forall>opid'. (opid' = 4 \<or> opid' = Suc 0) \<and> opid' \<noteq> 4 \<longrightarrow>
    (opid' m<[4, 0, Suc 0] 4) = Some True \<or> (opid' ;po2^2 4))"  
    using a2 f2_0 f2_1
    by simp
  then show ?thesis using f1 by auto
qed  
    
lemma e2_op2_load_val: 
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  shows "(axiom_value 2 2 1 po2 [4, 0, 1] pbm2 s) = Some 1"    
proof -
  have f0_0: "non_repeat_list [(4::nat), 0, 1]"
    unfolding non_repeat_list_def
    apply auto 
    done  
    \<comment>\<open>  
    by (metis less_2_cases less_antisym nth_Cons_0 nth_Cons_Suc numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_eq_iff semiring_norm(85) zero_neq_numeral)  
    \<close>      
  have f0_1: "list_before 4 [(4::nat),0,1] 1"
    unfolding list_before_def    
    apply auto
    by (metis (no_types, lifting) diff_Suc_1 lessI less_Suc_eq_0_disj nth_Cons_0 nth_Cons_numeral numeral_1_eq_Suc_0 numeral_2_eq_2) 
  have f0_2: "\<not> (list_before 1 [(4::nat),0,1] 4)"
    using non_repeat_list_before[OF f0_0 f0_1] by auto    
  have f0_3: "(4 m<[4, 0, 1] 1) = Some True" 
    unfolding memory_order_before_def
    using f0_1
    by (simp add: member_rec(1))
  have f0_4: "(1 m<[4, 0, 1] 4) = Some False"
    unfolding memory_order_before_def
    using f0_2
    by (simp add: member_rec(1))
  then have f0_5: "\<not> ((1 m<[4, 0, 1] 4) = Some True)"
    by auto
  have f1: "{opid'. (opid' m<[4, 0, 1] 2) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} \<union>
            {opid''. (opid'' ;po2^2 2) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)} = {4,1}"
    using e2_op2_load_val1[OF a1] e2_op2_load_val2[OF a1] a1 by auto 
  then have f2: "max_mem_order
           ({opid'. (opid' m<[4, 0, 1] 2) = Some True \<and>
             type_of_mem_op_block (pbm2 opid') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid' s)} \<union>
            {opid''. (opid'' ;po2^2 2) \<and>
             type_of_mem_op_block (pbm2 opid'') \<in> {st_block, ast_block} \<and>
             Some 1 = op_addr (get_mem_op_state opid'' s)})
           2 po2 [4, 0, 1] = Some 1"
    unfolding max_mem_order_def    
    apply auto
    using e2_op2_load_val_sub1[OF f0_3 f0_5] by auto
  then show ?thesis 
    unfolding axiom_value_def
    using a1 apply auto
    unfolding get_mem_op_state_def
    by auto 
qed
    
lemma e2_op2_exe_last: 
  assumes a1: "s = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(16 := 1, 1 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  shows "(proc_exe_to_last 2 po2 pbm2 0 (Some 1) (Some 1) s) = 
  \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty init_glob_var\<lparr>atomic_rd := 1\<rparr>, undef = False\<rparr>"  
  unfolding proc_exe_to_last_def po2_def pbm2_def e2pb2_def e2il0_def
  apply auto
  using a1
  apply (simp add: proc_exe_def casa_load_def gen_reg_val_def atomic_rd_mod_def gen_reg_mod_def
      mem_op_addr_mod_def mem_op_val_mod_def)
  unfolding next_proc_op_pos_mod_def
  by auto
  
lemma e2_op2_exe:
  assumes a1: "s3 = \<lparr>ctl_reg = emp_ctl_reg,
            gen_reg = (\<lambda>p r. 0)(3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0)),
            mem = emp_mem(1 \<mapsto> 1),
            mem_ops = emp_mem_ops
              (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
               0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
               Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
            proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0)), proc_var = init_proc_var,
            glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  and a2: "po2 pbm2 2 \<turnstile>m [4,0,1] s3 \<rightarrow> xseq4 s4"  
shows "xseq4 = [4,0,1,2] \<and>
       s4 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 2\<rparr>, undef = False\<rparr>"
proof -
  have f1: "xseq4 = [4,0,1] @ [2] \<and>
    s4 = atomic_flag_mod (Some 2)
         (proc_exe_to_last (proc_of_op 2 pbm2) po2 pbm2
           (non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2)))
           (axiom_value (proc_of_op 2 pbm2) 2
             (atomic_load_addr (proc_of_op 2 pbm2) (last (insts (pbm2 2)))
               (proc_exe_to_previous (proc_of_op 2 pbm2) po2 pbm2
                 (non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2))) s3))
             po2 [4, 0, 1] pbm2
             (proc_exe_to_previous (proc_of_op 2 pbm2) po2 pbm2
               (non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2))) s3))
           (Some (atomic_load_addr (proc_of_op 2 pbm2) (last (insts (pbm2 2)))
                   (proc_exe_to_previous (proc_of_op 2 pbm2) po2 pbm2
                     (non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2))) s3)))
           (proc_exe_to_previous (proc_of_op 2 pbm2) po2 pbm2
             (non_repeat_list_pos 2 (po2 (proc_of_op 2 pbm2))) s3))"
    using mem_op_elim_atom_load_op[OF a2 e2_type_op2_st] by auto
  from f1 have f2: "xseq4 = [4,0,1] @ [2]"
    by auto
  from a1 f2 have f2_1: "xseq4 = [4,0,1,2]"    
    unfolding valid_initial_exe_zero_mem_def
    by auto
  from f1 have f3: "s4 = atomic_flag_mod (Some 2) (proc_exe_to_last 2 po2 pbm2 0 (Some 1) (Some 1) 
    (proc_exe_to_previous 2 po2 pbm2 0 s3))"
    using a1 valid_initial_exe_def e2_op2_pos e2_proc_op2_2 
      e2_pre_s4 e2_op2_addr e2_op2_load_val by auto
  then have f4: "s4 = atomic_flag_mod (Some 2) \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty init_glob_var\<lparr>atomic_rd := 1\<rparr>, undef = False\<rparr>"
    using e2_pre_s4[OF a1] e2_op2_exe_last 
    by auto
  then have f5: "s4 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 2\<rparr>, undef = False\<rparr>"
    unfolding atomic_flag_mod_def
    by auto
  then show ?thesis using f2_1 by auto       
qed  

lemma e2_op3_exe:
  assumes a1: "s4 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 2\<rparr>, undef = False\<rparr>"
  and a2: "po2 pbm2 3 \<turnstile>m [4,0,1,2] s4 \<rightarrow> xseq5 s5"  
shows "xseq5 = [4,0,1,2,3] \<and>
       s5 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc (Suc 0)),
       proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
proof -
  have f1: "xseq5 = [4,0,1,2] @ [3] \<and> 
            s5 = mem_commit 3
            (atomic_flag_mod None
              (proc_exe_to (proc_of_op 3 pbm2) po2 pbm2
                (non_repeat_list_pos 3 (po2 (proc_of_op 3 pbm2))) s4))"
    using mem_op_elim_atom_store_op[OF a2 e2_type_op3_st] by auto
  from f1 have f2: "xseq5 = [4,0,1,2,3]" by auto
  from f1 have f3: "s5 = mem_commit 3 (atomic_flag_mod None (proc_exe_to (proc_of_op 3 pbm2) 
    po2 pbm2 (non_repeat_list_pos 3 (po2 (proc_of_op 3 pbm2))) s4))"
    by auto
  then have f4: "s5 = mem_commit 3 (atomic_flag_mod None (proc_exe_to 2 po2 pbm2 1 s4))"
    using e2_op3_pos e2_proc_op3_2 by auto
  then have f5: "s5 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc (Suc 0)),
       proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
    using a1
    unfolding proc_exe_to_def 
    apply (auto simp add: Let_def)
    unfolding pbm2_def po2_def e2pb3_def e2il1_def
     apply auto
    apply (simp add: proc_exe_def casa_store_def)
    unfolding atomic_flag_val_def atomic_rd_val_def casa_load_addr_def gen_reg_val_def
      mem_op_addr_mod_def mem_op_val_mod_def next_proc_op_pos_mod_def
      atomic_flag_mod_def 
    apply auto
    unfolding mem_commit_def
    by (auto simp add: Let_def get_mem_op_state_def mem_mod_def emp_mem_ops_def)
  then show ?thesis using f2 by auto
qed  
  
lemma e2_op3_exe_result:
  assumes a1: "s4 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          0 := emp_mem_ops 0\<lparr>op_addr := Some 1, op_val := Some 0\<rparr>,
          Suc 0 := emp_mem_ops (Suc 0)\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>,
          2 := emp_mem_ops 2\<lparr>op_addr := Some 1, op_val := Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc 0), proc_var = init_proc_var,
       glob_var = init_glob_var\<lparr>atomic_rd := 1, atomic_flag := Some 2\<rparr>, undef = False\<rparr>"
  and a2: "po2 pbm2 3 \<turnstile>m [4,0,1,2] s4 \<rightarrow> xseq5 s5"  
shows "(gen_reg s5) 1 16 = 0 \<and> (gen_reg s5) 2 16 = 1"  
proof -
  have f1: "s5 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc (Suc 0)),
       proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
    using e2_op3_exe[OF a1 a2] by auto
  then show ?thesis by auto
qed  
  
lemma e2_op5_exe:
  assumes a1: "s5 = \<lparr>ctl_reg = emp_ctl_reg,
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc 0), 2 := Suc (Suc 0)),
       proc_var = init_proc_var,
       glob_var = atomic_flag_update Map.empty (init_glob_var\<lparr>atomic_rd := 1\<rparr>), undef = False\<rparr>"
  and a2: "po2 pbm2 5 \<turnstile>m [4,0,1,2,3] s5 \<rightarrow> xseq6 s6"  
shows "xseq6 = [4,0,1,2,3,5] \<and>
       s6 = \<lparr>ctl_reg = emp_ctl_reg(Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, 2 := Suc (Suc 0), Suc 0 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
proof -
  have f1: "xseq6 = [4,0,1,2,3] @ [5] \<and>
    s6 = proc_exe_to (proc_of_op 5 pbm2) po2 pbm2 (non_repeat_list_pos 5 (po2 
    (proc_of_op 5 pbm2))) s5"
    using mem_op_elim_o_op[OF a2 e2_type_op5_st] by auto
  from f1 have f2: "xseq6 = [4,0,1,2,3,5]"
    by auto
  from f1 have f3: "s6 = proc_exe_to 1 po2 pbm2 2 s5"
    using e2_op5_pos e2_proc_op5_1 by auto
  then have f4: "s6 = \<lparr>ctl_reg = emp_ctl_reg(Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, 2 := Suc (Suc 0), Suc 0 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
    unfolding proc_exe_to_def pbm2_def e2pb5_def e2il2_def po2_def
    using a1 apply auto
    apply (simp add: proc_exe_def)
    apply (simp add: logical_instr_def ctl_reg_mod_def logical_result_def 
        get_operand2_def Let_def gen_reg_val_def logical_mult_new_psr_val_def ctl_reg_val_def
        update_PSR_icc_def emp_ctl_reg_def get_disp_imm22_def branch_instr_def)
    apply (simp add: ctl_reg_val_def ctl_reg_mod_def nop_instr_def next_proc_op_pos_mod_def)
    apply (simp add: eval_icc_def)
    by (simp add: ctl_reg_val_def ctl_reg_mod_def sign_ext24_def emp_ctl_reg_def 
        get_icc_Z_def init_glob_var_def)
  then show ?thesis using f2 by auto
qed  
  
lemma e2_op6_exe:
  assumes a1: "s6 = \<lparr>ctl_reg = emp_ctl_reg(Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, 2 := Suc (Suc 0), Suc 0 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
  and a2: "po2 pbm2 6 \<turnstile>m [4,0,1,2,3,5] s6 \<rightarrow> xseq7 s7"  
shows "xseq7 = [4,0,1,2,3,5,6] \<and>
       s7 = \<lparr>ctl_reg = emp_ctl_reg
       (Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112),
        2 := (emp_ctl_reg 2)(PSR := 0, PC := 0, nPC := 4)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc (Suc 0)), 2 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
proof -
  have f1: "xseq7 = [4,0,1,2,3,5] @ [6] \<and>
    s7 = proc_exe_to (proc_of_op 6 pbm2) po2 pbm2 (non_repeat_list_pos 6 (po2 
    (proc_of_op 6 pbm2))) s6"
    using mem_op_elim_o_op[OF a2 e2_type_op6_st] by auto
  from f1 have f2: "xseq7 = [4,0,1,2,3,5,6]"
    by auto
  from f1 have f3: "s7 = proc_exe_to 2 po2 pbm2 2 s6"
    using e2_op6_pos e2_proc_op6_2 by auto
  then have f4: "s7 = \<lparr>ctl_reg = emp_ctl_reg
       (Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112),
        2 := (emp_ctl_reg 2)(PSR := 0, PC := 0, nPC := 4)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc (Suc 0)), 2 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
    unfolding proc_exe_to_def pbm2_def e2pb6_def e2il2_def po2_def
    using a1 apply auto
    apply (simp add: proc_exe_def)
    apply (simp add: logical_instr_def ctl_reg_mod_def logical_result_def 
        get_operand2_def Let_def gen_reg_val_def logical_mult_new_psr_val_def ctl_reg_val_def
        update_PSR_icc_def emp_ctl_reg_def get_disp_imm22_def branch_instr_def)
    apply (simp add: ctl_reg_val_def ctl_reg_mod_def nop_instr_def next_proc_op_pos_mod_def)
    apply (simp add: eval_icc_def)
    by (simp add: ctl_reg_val_def ctl_reg_mod_def sign_ext24_def emp_ctl_reg_def 
        get_icc_Z_def init_glob_var_def get_a_def)
  then show ?thesis using f2 by auto
qed  
  
lemma e2_op6_exe_result:
  assumes a1: "s6 = \<lparr>ctl_reg = emp_ctl_reg(Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, 2 := Suc (Suc 0), Suc 0 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
  and a2: "po2 pbm2 6 \<turnstile>m [4,0,1,2,3,5] s6 \<rightarrow> xseq7 s7"  
shows "(ctl_reg s7) 1 nPC = (ctl_reg s7) 1 PC + 112 \<and> (ctl_reg s7) 2 nPC = (ctl_reg s7) 2 PC + 4"
proof -
  have f1: "s7 = \<lparr>ctl_reg = emp_ctl_reg
       (Suc 0 := (emp_ctl_reg (Suc 0))(PSR := 4194304, PC := 0, nPC := 112),
        2 := (emp_ctl_reg 2)(PSR := 0, PC := 0, nPC := 4)),
       gen_reg = (\<lambda>p r. 0)
         (3 := (\<lambda>r. 0)(4 := 1), Suc 0 := (\<lambda>r. 0)(1 := 1, 16 := 0), 2 := (\<lambda>r. 0)(1 := 1, 16 := 1)),
       mem = emp_mem(1 \<mapsto> 1),
       mem_ops = emp_mem_ops
         (4 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>, 0 := \<lparr>op_addr = Some 1, op_val = Some 0\<rparr>,
          Suc 0 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>, 2 := \<lparr>op_addr = Some 1, op_val = Some 1\<rparr>),
       proc_exe_pos = (\<lambda>p. 0)(3 := Suc 0, Suc 0 := Suc (Suc (Suc 0)), 2 := Suc (Suc (Suc 0))),
       proc_var = init_proc_var, glob_var = \<lparr>atomic_flag = None, atomic_rd = 1\<rparr>, undef = False\<rparr>"
    using e2_op6_exe[OF a1 a2] by auto
  then show ?thesis by auto
qed  
  
end  
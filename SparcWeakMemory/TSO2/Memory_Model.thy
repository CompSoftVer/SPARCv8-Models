\<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 \<close>

text {* SPARC V8 TSO memory model*}
theory Memory_Model 
imports Main Processor_Execution 
begin   
  
text {* This theory models the SPARC TSO memory model. *}      
  
text {* The sequence of executed meomry operation blocks. *}
  
type_synonym executed_mem_ops = "op_id list"  
  
text {* Given a sequence of executed mem_op_block, the memory order op1 m< op2 is 
true when op1 is in the sequence before op2. 
If both are not in the sequence, the result is None.
If one of them is not in the sequence, then it is later than the one
that occurs in the sequence.  *}

  
definition memory_order_before:: "op_id \<Rightarrow> executed_mem_ops \<Rightarrow> op_id \<Rightarrow> 
  bool option" ("_ m<_ _") where
"op1 m<xseq op2 \<equiv> 
  if (List.member xseq op1) \<and> (List.member xseq op2) then
    if list_before op1 xseq op2 then Some True
    else Some False
  else if List.member xseq op1 then Some True
  else if List.member xseq op2 then Some False
  else None"    

definition memory_order_before_pred:: "(op_id \<Rightarrow> bool) \<Rightarrow> executed_mem_ops  \<Rightarrow>  op_id \<Rightarrow> 
  op_id set" ("_ m<;_ _") where
"P m<;xseq op  \<equiv> 
  {a. P a \<and> ((a m<xseq op) = Some True)}"  


definition max_memory_order_before::"(op_id \<Rightarrow> bool) \<Rightarrow> executed_mem_ops  \<Rightarrow>  op_id \<Rightarrow> 
  op_id option" ("_ M<;_ _")
  where
"P M<;xseq op1 \<equiv> if (P m<;xseq op1)\<noteq>{} then 
                   Some (THE x. (x \<in>(P m<;xseq op1)) \<and> 
                                 (\<forall>x'\<in> (P m<;xseq op1). (x' m<xseq x) = Some True))
                 else None"


lemma memory_order_before_tran:
assumes 
  a0:"distinct xseq" and
  a1:"(op1 m<xseq op2) = Some True" and
  a2:"(op2 m<xseq op3) = Some True" 
shows
  "(op1 m<xseq op3) = Some True" 
  unfolding memory_order_before_def using a0 a1 a2
  by (metis list_before_tran memory_order_before_def option.distinct(1) option.inject)
   


lemma mem_order_not_sym: assumes 
  a0:"distinct xseq" and
  a1:"(op1 m<xseq op2) = Some True" 
shows "\<not> ((op2 m<xseq op1) = Some True)"
  using a0 a1 unfolding memory_order_before_def
  apply auto
  by (metis list_before_not_sym option.inject)

lemma exists_mem_order_list_member:
      "finite z \<Longrightarrow>
       z\<noteq>{} \<Longrightarrow>
       distinct l \<Longrightarrow>
       z\<subseteq>{x. List.member l x} \<Longrightarrow>      
       \<exists>x. x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> (x' m<l x) = Some True)"
proof(induction rule: Finite_Set.finite_ne_induct)
case (singleton x)
  then show ?case
    by blast 
next
  case (insert x F)
  then obtain x1 where hp:"x1\<in>F \<and> (\<forall>x'\<in>F. x'\<noteq>x1 \<longrightarrow> (x' m<l x1) = Some True)"
    by auto    
  then have neq:"x\<noteq>x1" using insert by auto
  { assume "(x m<l x1) = Some True"
    then have ?case using hp neq by fastforce
  }note l1 =this
  {
    assume assm:"(x1 m<l x) = Some True"
    then have ?case using hp neq insert(3)  memory_order_before_tran
      by (metis (full_types) insert.prems(1) insert_iff)                  
  }note l2 = this
  show ?case
    by (metis insert.prems(2) insert_subset l1 l2 list_elements_before 
             mem_Collect_eq memory_order_before_def neq)   
qed

lemma unique_max_order_before:
  assumes
        a2:"distinct l" and       
       a4:"x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> (x' m<l x) = Some True)"
     shows "\<forall>x'. x'\<in>z \<and> (\<forall>x''\<in>z. x''\<noteq>x' \<longrightarrow> (x'' m<l x') = Some True) \<longrightarrow> x' = x "
  using mem_order_not_sym[OF a2] a4 by metis

lemma exists_unique_mem_order_list:"distinct l \<Longrightarrow>
       z\<subseteq>{x. List.member l x} \<Longrightarrow>
       z\<noteq>{} \<Longrightarrow>
       \<exists>!x. x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> (x' m<l x) = Some True)"        
  apply (frule exists_mem_order_list_member[OF finite_subset_list],assumption+)  
  apply clarsimp 
  by (frule unique_max_order_before, auto simp add: Ex1_def)


lemma mem_order_false_cond: "(op1 m<xseq op2) = Some False \<Longrightarrow> 
  ((List.member xseq op1) \<and> (List.member xseq op2) \<and> \<not>(list_before op1 xseq op2)) \<or> 
  (\<not>(List.member xseq op1) \<and> (List.member xseq op2))"  
  unfolding memory_order_before_def
  by (metis option.distinct(1) option.inject)
  
lemma mem_order_true_cond: "(op1 m<xseq op2) = Some True \<Longrightarrow> 
  ((List.member xseq op1) \<and> (List.member xseq op2) \<and> (list_before op1 xseq op2)) \<or> 
  ((List.member xseq op1) \<and> \<not>(List.member xseq op2))"    
  unfolding memory_order_before_def
  by (metis option.distinct(1) option.inject)
    
lemma mem_order_true_cond_rev: "((List.member xseq op1) \<and> (List.member xseq op2) \<and> 
  (list_before op1 xseq op2)) \<or> 
  ((List.member xseq op1) \<and> \<not>(List.member xseq op2)) \<Longrightarrow> (op1 m<xseq op2) = Some True"    
  unfolding memory_order_before_def
  by auto
    
lemma mem_order_true_cond_equiv: "(op1 m<xseq op2) = Some True = 
  ((List.member xseq op1) \<and> (List.member xseq op2) \<and> (list_before op1 xseq op2)) \<or> 
  ((List.member xseq op1) \<and> \<not>(List.member xseq op2))"   
  using mem_order_true_cond mem_order_true_cond_rev by auto
    
    
section{* The axiomatic model. *}

text {* This section gives an axiomatic definition of the TSO model a la 
SPARCv8 manual. *}
  
definition axiom_order:: "op_id \<Rightarrow> op_id \<Rightarrow> executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> bool" where
"axiom_order opid opid' xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and> 
   (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
   (opid \<in> (set xseq) \<and> 
    opid' \<in> (set xseq) \<and> opid \<noteq> opid')) \<longrightarrow> 
  ((opid m<xseq opid') = Some True \<or> (opid' m<xseq opid) = Some True)"  

text {* A new version of axiom_order for code export. *}
 
  
definition axiom_atomicity:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_atomicity opid opid' po xseq pbm \<equiv> 
  ((atom_pair_id (pbm opid') = Some opid) \<and> 
   (type_of_mem_op_block (pbm opid) = ald_block) \<and>
   (type_of_mem_op_block (pbm opid') = ast_block) \<and>
   (opid ;po^(proc_of_op opid pbm) opid')) \<longrightarrow> 
  (((opid m<xseq opid') = Some True) \<and> 
   (\<forall>opid''. ((type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
              List.member xseq opid'' \<and> \<comment>\<open> opid'' \<noteq> opid is true because their types are different. \<close>
              opid'' \<noteq> opid') \<longrightarrow>
             ((opid'' m<xseq opid) = Some True \<or> (opid' m<xseq opid'') = Some True)))"    
  

definition axiom_storestore:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_storestore opid opid' po xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
   (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
   (opid ;po^(proc_of_op opid pbm) opid')) \<longrightarrow>
  (opid m<xseq opid') = Some True"  

text {* A new version of axiom_storestore for code export. *}
  
    



  
text {* Since our operational semantics always terminate, the axiom Termination
is trivialised to whether a store is eventually committed by the memory. 
Thus we only need to check if it is in the (final) executed sequence or not. *}  


definition axiom_termination:: "op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_termination opid po xseq pbm \<equiv> 
 ( (\<exists>p. List.member (po  p) opid \<and> p<(Suc max_proc)) \<and>
  (type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block})) \<longrightarrow>
  List.member xseq opid" 

  
definition max_mem_order:: "op_id set \<Rightarrow> proc \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  op_id option" where
"max_mem_order opids p po xseq \<equiv> 
  if opids \<noteq> {} then
    Some (THE opid. (opid \<in> opids \<and>  
                    (\<forall>opid'. ((opid' \<in> opids \<and> opid' \<noteq> opid) \<longrightarrow>
                             ((opid' m<xseq opid) = Some True \<or> 
                              (opid' ;po^p opid))))))
  else None"  
  
text {* A new definition for max_mem_order for code export. *}

\<comment>\<open> primrec max_mem_order_list:: "op_id list \<Rightarrow> proc \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  op_id option \<Rightarrow> op_id option" where
"max_mem_order_list [] p po xseq opidop = opidop"
|"max_mem_order_list (x#xl) p po xseq opidop = (
  case opidop of None \<Rightarrow> max_mem_order_list xl p po xseq (Some x)
  |Some opid \<Rightarrow> (if (x m<2xseq opid) = Some True \<or> (x 2;po^p opid) then 
                  max_mem_order_list xl p po xseq (Some opid)
                 else max_mem_order_list xl p po xseq (Some x)))"
 
lemma max_mem_order_code_equal1: 
  "x=max_mem_order_list opids p po xseq None \<Longrightarrow> 
  x= max_mem_order (set opids) p po xseq"    
  sorry

lemma max_mem_order_code_equal2: 
  "x= max_mem_order (set opids) p po xseq \<Longrightarrow>
   x=max_mem_order_list opids p po xseq None"    
  unfolding max_mem_order_def sorry
  
    
lemma max_mem_order_code_equal3: 
  "max_mem_order (set opids) p po xseq =
   max_mem_order_list opids p po xseq None"    
  using max_mem_order_code_equal1 max_mem_order_code_equal2 by auto
    
definition max_mem_order2:: "op_id set \<Rightarrow> proc \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  op_id option" where
"max_mem_order2 opids p po xseq \<equiv> 
  max_mem_order_list (sorted_list_of_set opids) p po xseq None" \<close>

lemma xx:"finite opids \<Longrightarrow> 
          set (sorted_list_of_set opids) = opids"
  by simp

lemma list_before_x: "list_before x xlist opid \<Longrightarrow> list_before x (a#xlist) opid"
  unfolding list_before_def
  by (metis Suc_less_eq le0 length_Cons nth_Cons_Suc)
    
lemma list_before_x': "x\<noteq>a \<Longrightarrow> list_before x (a#xlist) opid \<Longrightarrow> list_before x xlist opid"
  unfolding list_before_def     
proof auto
  fix i :: nat and j :: nat
  assume a1: "(a # xlist) ! i \<noteq> a"
  assume a2: "i < j"
  assume a3: "j < Suc (length xlist)"
  have "\<forall>n na. \<not> (n::nat) < na \<or> na \<noteq> 0"
    by linarith
  then have f4: "j \<noteq> 0"
    using a2 by metis
  obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  f5: "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
  by moura
  have "i < Suc (length xlist)"
    using a3 a2 dual_order.strict_trans by blast
  then show "\<exists>n<length xlist. \<exists>na<length xlist. xlist ! n = (a # xlist) ! i \<and> xlist ! na = xlist ! (j - Suc 0) \<and> n < na"
    using f5 f4 a3 a2 a1 by (metis (no_types) One_nat_def diff_Suc_1 less_Suc_eq_0_disj nth_Cons')
qed    

definition axiom_value:: "proc \<Rightarrow> op_id \<Rightarrow> virtual_address \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
                           program_block_map \<Rightarrow> sparc_state \<Rightarrow> memory_value option" where
"axiom_value p opid addr po xseq pbm state \<equiv> 
  case (max_mem_order ({opid'. (opid' m<xseq opid) = Some True \<and> 
                         (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
                         Some addr = op_addr (get_mem_op_state opid' state)} \<union> 
                        {opid''. (opid'' ;po^p opid) \<and>
                         (type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
                         Some addr = op_addr (get_mem_op_state opid'' state)}) p po xseq) of
  Some opid''' \<Rightarrow> op_val (get_mem_op_state opid''' state)
  |None \<Rightarrow> None"  

definition st_blocks_addr::"virtual_address \<Rightarrow> program_block_map \<Rightarrow>  sparc_state \<Rightarrow> op_id \<Rightarrow> bool"
  where "st_blocks_addr addr pbm s  \<equiv> \<lambda>opid.  
                         (type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and> 
                         Some addr = op_addr (get_mem_op_state opid s)"


definition axiom_value'::"proc \<Rightarrow> op_id \<Rightarrow> virtual_address \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> 
  sparc_state \<Rightarrow> memory_value option" where
"axiom_value' p opid addr po xseq pbm state \<equiv> 
  case (max_mem_order (((st_blocks_addr addr pbm state) m<;xseq opid) \<union> 
                        {opid''. (opid'' ;po^p opid) \<and> st_blocks_addr addr pbm state opid''}) p po xseq) of
  Some opid''' \<Rightarrow> op_val (get_mem_op_state opid''' state)
  |None \<Rightarrow> None"  

lemma eq_mem_order_before_pred:
  "(st_blocks_addr addr pbm state) m<;xseq opid = {opid'. (opid' m<xseq opid) = Some True \<and> 
   (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
   Some addr = op_addr (get_mem_op_state opid' state)}"
  unfolding st_blocks_addr_def memory_order_before_pred_def
  by auto

lemma "axiom_value' = axiom_value"
  unfolding axiom_value'_def axiom_value_def 
  using eq_mem_order_before_pred
  by (auto simp add: st_blocks_addr_def)


  
definition axiom_loadop:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_loadop opid opid' po xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {ld_block, ald_block}) \<and>
   (opid ;po^(proc_of_op opid pbm) opid')) \<longrightarrow> 
             (opid m<xseq opid') = Some True"    

section {* Operational model. *}

text {* This section defines an inference rule based operational TSO model. *}

text {* Given an address and the executed sequence of mem_op_block ids, return 
the id of the first store in the executed sequence at the same address. 
If there are none, return None. 
N.B. We could formulate the below functions more mathematically (i.e., using sets
and first-order logic), but we choose the define it in a more operational way
for performance reasons. *}

primrec get_first_store:: "virtual_address \<Rightarrow> op_id list \<Rightarrow> program_block_map \<Rightarrow>
  sparc_state \<Rightarrow> op_id option" where
"get_first_store addr [] pbm state = None"
|"get_first_store addr (x#xs) pbm state = (
  if Some addr = (op_addr (get_mem_op_state x state)) \<and>
     type_of_mem_op_block (pbm x) \<in> {st_block, ast_block} 
  then
    Some x
  else get_first_store addr xs pbm state)" 
  
definition mem_most_recent_store:: "virtual_address \<Rightarrow> executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow>
  sparc_state \<Rightarrow> op_id option" where
"mem_most_recent_store addr xseq pbm state \<equiv> get_first_store addr (List.rev xseq) pbm state"  

text {* Given a load operation id and the program order, return the id of most recent
store at the same address in the program order that is before the load.
If there are none, return None. *}
  
definition proc_most_recent_store:: "proc \<Rightarrow> virtual_address \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> 
  program_block_map \<Rightarrow> sparc_state \<Rightarrow> op_id option" where
"proc_most_recent_store p addr opid po pbm state \<equiv> 
  get_first_store addr (List.rev (sub_list_before opid (po p))) pbm state"    
  
text {* The value of the load operation based on the axiom value. *}  
  
definition load_value:: "proc \<Rightarrow> virtual_address \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> 
  executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> sparc_state \<Rightarrow> memory_value option" where  
"load_value p addr opid po xseq pbm state \<equiv> 
  case ((mem_most_recent_store addr xseq pbm state),(proc_most_recent_store p addr opid po pbm state)) of 
  (Some s1, Some s2) \<Rightarrow> (case (s1 m<xseq s2) of 
    Some True \<Rightarrow> op_val (get_mem_op_state s2 state)
    |Some False \<Rightarrow> op_val (get_mem_op_state s1 state)
    |None \<Rightarrow> None)
  |(None, Some s2) \<Rightarrow> op_val (get_mem_op_state s2 state)
  |(Some s1, None) \<Rightarrow> op_val (get_mem_op_state s1 state)
  |(None, None) \<Rightarrow> None"   
  
text {* A new version of load_value for code export. *}
  



text {* Assuming that when calling this function, the address and value of the store
is already computed in the process of proc_exe_to. 
Commit the store to the memory. *}

definition mem_commit:: "op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"mem_commit opid s \<equiv> 
  let opr = get_mem_op_state opid s in
  case ((op_addr opr),(op_val opr)) of
   (Some addr, Some val) \<Rightarrow> mem_mod val addr s
  |_ \<Rightarrow> s"  

text {* Definition of the "inference rules" in our operational TSO model.  *}

inductive 
"mem_op"::"[program_order, program_block_map, op_id, executed_mem_ops, sparc_state, 
  executed_mem_ops, sparc_state] \<Rightarrow> bool"
("_ _ _ \<turnstile>m (_ _ \<rightarrow>/ _ _)" 100)
  for po::"program_order" and pbm::"program_block_map" and opid::"op_id"
  where
load_op: 
  "\<lbrakk>p = proc_of_op opid pbm;    
    (type_of_mem_op_block (pbm opid) = ld_block);
    \<forall>opid'. (((opid' ;po^p opid) \<and> 
              (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block})) \<longrightarrow> 
             (List.member xseq opid'));
    s' = proc_exe_to_previous p po pbm (non_repeat_list_pos opid (po p)) s;
    addr = load_addr p (List.last (insts (pbm opid))) s';
    vop = axiom_value p opid addr po xseq pbm s'\<rbrakk> \<Longrightarrow>           
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] 
      (proc_exe_to_last p po pbm (non_repeat_list_pos opid (po p)) vop (Some addr) s')" 
|store_op: 
  "\<lbrakk>p = proc_of_op opid pbm;
    (type_of_mem_op_block (pbm opid) = st_block);
    (atomic_flag_val s) = None;
    \<forall>opid'. (((opid' ;po^p opid) \<and> 
              (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
             (List.member xseq opid'))\<rbrakk> \<Longrightarrow>           
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] 
      (mem_commit opid (proc_exe_to p po pbm (non_repeat_list_pos opid (po p)) s))" 
|atom_load_op: 
  "\<lbrakk>p = proc_of_op opid pbm;    
    (type_of_mem_op_block (pbm opid) = ald_block);
    (atomic_flag_val s) = None;
    \<forall>opid'. (((opid' ;po^p opid) \<and> 
              (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
             (List.member xseq opid'));
    s' = proc_exe_to_previous p po pbm (non_repeat_list_pos opid (po p)) s;
    addr = atomic_load_addr p (List.last (insts (pbm opid))) s';
    vop = axiom_value p opid addr po xseq pbm s'\<rbrakk> \<Longrightarrow>           
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] 
      (atomic_flag_mod (Some opid) (proc_exe_to_last p po pbm (non_repeat_list_pos opid (po p)) 
      vop (Some addr) s'))"
|atom_store_op: 
  "\<lbrakk>p = proc_of_op opid pbm;
    (type_of_mem_op_block (pbm opid) = ast_block);
    (atomic_flag_val s) = Some opid';
    atom_pair_id (pbm opid) = Some opid';
    \<forall>opid'. (((opid' ;po^p opid) \<and> 
              (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
             (List.member xseq opid'))\<rbrakk> \<Longrightarrow>           
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] 
      (mem_commit opid (atomic_flag_mod None 
      (proc_exe_to p po pbm (non_repeat_list_pos opid (po p)) s)))"  
|o_op: 
  "\<lbrakk>p = proc_of_op opid pbm;
    (type_of_mem_op_block (pbm opid) = o_block);
    \<forall>opid'. (((opid' ;po^p opid) \<and> 
             (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
            (List.member xseq opid'))\<rbrakk> \<Longrightarrow>
   po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] 
    (proc_exe_to p po pbm (non_repeat_list_pos opid (po p)) s)"    
  
text {* The lemmas below are for inverse inference of the above rules.   *}      
  
inductive_cases mem_op_elim_cases:
"(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"

lemma mem_op_elim_load_op:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = ld_block)" 
and a3: "(xseq' = xseq @ [opid] \<Longrightarrow>
        s' = proc_exe_to_last (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
         (axiom_value (proc_of_op opid pbm) opid (load_addr (proc_of_op opid pbm) 
         (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) po xseq pbm (proc_exe_to_previous 
         (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
          s)) (Some (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) 
          (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
         (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s) \<Longrightarrow>
        type_of_mem_op_block (pbm opid) = ld_block \<Longrightarrow>
        (\<forall>opid'. ((opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block)) \<longrightarrow>
                List.member xseq opid') \<Longrightarrow> P)"
shows "P"
  using a2 a3 by (auto intro:mem_op_elim_cases[OF a1])
  
lemma mem_op_elim_store_op:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = st_block)" 
and a3: "(xseq' = xseq @ [opid] \<Longrightarrow>
 s' = mem_commit opid (proc_exe_to (proc_of_op opid pbm) po pbm 
     (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s) \<Longrightarrow>
 type_of_mem_op_block (pbm opid) = st_block \<Longrightarrow>
 atomic_flag_val s = None \<Longrightarrow>
 \<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
         List.member xseq opid' \<Longrightarrow> P)"
shows "P"          
  using a2 a3 by (auto intro:mem_op_elim_cases[OF a1])

lemma mem_op_elim_atom_load_op:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = ald_block)" 
and a3: "xseq' = xseq @ [opid] \<Longrightarrow>
        s' = atomic_flag_mod (Some opid) (proc_exe_to_last (proc_of_op opid pbm) po pbm 
          (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
          (axiom_value (proc_of_op opid pbm) opid (atomic_load_addr (proc_of_op opid pbm) 
          (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
          po xseq pbm (proc_exe_to_previous (proc_of_op opid pbm) 
          po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))
           (Some (atomic_load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) 
            (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
           (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) \<Longrightarrow>
        type_of_mem_op_block (pbm opid) = ald_block \<Longrightarrow>
        atomic_flag_val s = None \<Longrightarrow>
        \<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                List.member xseq opid' \<Longrightarrow> P"
shows "P"      
  using a2 a3 by (auto intro:mem_op_elim_cases[OF a1])  

lemma mem_op_elim_atom_store_op:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = ast_block)" 
and a3: "(\<And>opid'. xseq' = xseq @ [opid] \<Longrightarrow>
          s' = mem_commit opid (atomic_flag_mod None (proc_exe_to (proc_of_op opid pbm) 
            po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) \<Longrightarrow>
          type_of_mem_op_block (pbm opid) = ast_block \<Longrightarrow>
          atomic_flag_val s = Some opid' \<Longrightarrow>
          atom_pair_id (pbm opid) = Some opid' \<Longrightarrow>
          \<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                  (type_of_mem_op_block (pbm opid') = ld_block \<or>
                   type_of_mem_op_block (pbm opid') = ald_block \<or>
                   type_of_mem_op_block (pbm opid') = st_block \<or> 
                   type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                  List.member xseq opid' \<Longrightarrow> P)"
shows "P"     
  using a2 a3 by (auto intro:mem_op_elim_cases[OF a1])   
  
lemma mem_op_elim_o_op:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = o_block)" 
and a3: "(xseq' = xseq @ [opid] \<Longrightarrow>
 s' = proc_exe_to (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
    (proc_of_op opid pbm))) s \<Longrightarrow>
 type_of_mem_op_block (pbm opid) = o_block \<Longrightarrow>
 \<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
         List.member xseq opid' \<Longrightarrow> P)"
shows "P"     
  using a2 a3 by (auto intro:mem_op_elim_cases[OF a1]) 
 
lemma atomic_flag_mod_state: "s' = atomic_flag_mod (Some opid) s \<Longrightarrow>
      atomic_flag (glob_var s') = Some opid"   
  unfolding atomic_flag_mod_def
  by auto  
    
lemma mem_op_atom_load_op_atomic_flag:
assumes a1: "(po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
and a2: "(type_of_mem_op_block (pbm opid) = ald_block)" 
shows "atomic_flag (glob_var s') = Some opid"
proof -
  have "xseq' = xseq @ [opid] \<Longrightarrow>
        s' = atomic_flag_mod (Some opid) (proc_exe_to_last (proc_of_op opid pbm) po pbm 
          (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
          (axiom_value (proc_of_op opid pbm) 
            opid (atomic_load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) 
            (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
          po xseq pbm (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))
           (Some (atomic_load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) 
          (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
           (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) \<Longrightarrow>
        type_of_mem_op_block (pbm opid) = ald_block \<Longrightarrow>
        atomic_flag_val s = None \<Longrightarrow>
        \<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                List.member xseq opid' \<Longrightarrow> 
        atomic_flag (glob_var s') = Some opid"
    using atomic_flag_mod_state by auto
  then show ?thesis using a1 a2 mem_op_elim_atom_load_op
    by metis 
qed  
    
text {* Given a program_order, define a transition from (xseq, rops, state) 
to (xseq', rops', state'), where xseq is the executed sequence of memory operations,
rops is the set of remaining unexecuted memory operations. *}  
  
definition mem_state_trans:: "program_order \<Rightarrow> program_block_map \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state) \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state) \<Rightarrow> bool" 
 ("_ _ \<turnstile>t (_ \<rightarrow>/ _)" 100) where  
"po pbm \<turnstile>t pre \<rightarrow> post \<equiv> 
  (\<exists>opid. opid \<in> (fst (snd pre)) \<and> 
          (po pbm opid \<turnstile>m (fst pre) (snd (snd pre)) \<rightarrow> (fst post) (snd (snd post))) \<and>
          (fst (snd post)) = (fst (snd pre)) - {opid})"    

text {* Define the conditions for a program to be valid. *}

definition valid_program:: "program_order \<Rightarrow> program_block_map \<Rightarrow> bool" where
"valid_program po pbm \<equiv> 
(\<forall>opid opid' opid''. (atom_pair_id (pbm opid) = Some opid' \<and> opid \<noteq> opid'') \<longrightarrow>
                      (atom_pair_id (pbm opid'') \<noteq> Some opid')) \<and>
(\<forall>opid p. (List.member (po p) opid \<and> type_of_mem_op_block (pbm opid) = ald_block) \<longrightarrow> 
          (\<exists>opid'. (opid ;po^p opid') \<and> type_of_mem_op_block (pbm opid') = ast_block \<and>
           atom_pair_id (pbm opid') = Some opid)) \<and>
(\<forall>opid' p. (List.member (po p) opid' \<and> type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow> 
          (\<exists>opid. (opid ;po^p opid') \<and> type_of_mem_op_block (pbm opid) = ald_block \<and>
           atom_pair_id (pbm opid') = Some opid)) \<and>
(\<forall>p. non_repeat_list (po p)) \<and>
(\<forall>opid opid' p. (opid ;po^p opid') \<longrightarrow> (proc_of_op opid pbm = proc_of_op opid' pbm
   \<and> p = proc_of_op opid pbm)) \<and>
(\<forall>opid p. (List.member (po p) opid) \<longrightarrow> (proc_of_op opid pbm = p))"  

text {* The definition of a valid complete sequence of memory executions. *}

definition valid_mem_exe_seq:: "program_order \<Rightarrow> program_block_map \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state) list \<Rightarrow> bool" where
"valid_mem_exe_seq po pbm exe_list \<equiv> 
  valid_program po pbm \<and>
  List.length exe_list > 0 \<and>
  fst (List.hd exe_list) = [] \<and> \<comment>\<open> Nothing has been executed in the initial state. \<close>
  (\<forall>opid. (\<exists>p. List.member (po p) opid) = 
    (opid \<in> fst (snd (List.hd exe_list)))) \<and> \<comment>\<open> Initially the *to be executed* set of op_ids include every op_id in the program order. \<close>
  \<comment>\<open>non_repeat_list (fst (last exe_list)) \<and>  Each op_id is unique. \<close>
  (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and> \<comment>\<open> In the initial state, the atomic flag is None. \<close>
  \<comment>\<open>fst (snd (List.last exe_list)) = {} \<and>  Nothing is remaining to be executed in the final state. (Redundant)\<close>
  (\<forall>i. i < (List.length exe_list) - 1 \<longrightarrow> \<comment>\<open> Each adjacent states are from a mem_state_trans. \<close>
       (po pbm \<turnstile>t (exe_list!i) \<rightarrow> (exe_list!(i+1))))"  

definition valid_mem_exe_seq_final:: "program_order \<Rightarrow> program_block_map \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state) list \<Rightarrow> bool" where
"valid_mem_exe_seq_final po pbm exe_list \<equiv> 
  valid_mem_exe_seq po pbm exe_list \<and> 
  fst (snd (List.hd exe_list)) = set (fst (List.last exe_list)) \<comment>\<open> Everything has been executed in the final state. \<close>"

section {* The equivalence of the axiomatic model and the operational model. *}

subsection {* Soundness of the operational TSO model *}  
  
text {* This subsection shows that every valid sequence of memory operations 
executed by the operational TSO model satisfies the TSO axioms. *}  
  
text {* First, we show that each valid_mem_exe_seq satisfies all the axioms. *}  
  
lemma mem_op_exe: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s' \<Longrightarrow> xseq' = xseq@[opid]"  
  unfolding mem_op.simps
  by auto      
  
lemma mem_state_trans_op: "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s') \<Longrightarrow> 
 List.butlast xseq' = xseq \<and> {List.last xseq'} \<union> rops' = rops" 
  unfolding mem_state_trans_def
  apply simp
  using mem_op_exe
  by fastforce  
    
lemma mem_state_trans_op2: 
assumes a1: "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')" 
shows "xseq' = xseq@(List.sorted_list_of_set (rops - rops'))" 
proof -
  from a1 have f1: "\<exists>opid. opid \<in> rops \<and> (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s') \<and> rops' = rops - {opid}"
    using mem_state_trans_def by simp
  then obtain opid::op_id where 
    f2: "opid \<in> rops \<and> (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s') \<and> rops' = rops - {opid}"
    by auto    
  then have f3: "xseq' = xseq@[opid]"
    using mem_op_exe by auto
  from f2 have "rops - rops' = {opid}"
    by auto
  then have f4: "List.sorted_list_of_set (rops - rops') = [opid]"
    by auto    
  then show ?thesis
    using f3 by auto
qed
  
lemma mem_state_trans_op3: 
assumes a1: "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')" 
shows "\<exists>opid. xseq' = xseq@[opid] \<and> rops = rops' \<union> {opid}"   
proof -
  from a1 have f1: "\<exists>opid. opid \<in> rops \<and> (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s') \<and> rops' = rops - {opid}"
    using mem_state_trans_def by simp
  then obtain opid::op_id where 
    f2: "opid \<in> rops \<and> (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s') \<and> rops' = rops - {opid}"
    by auto
  then have f3: "xseq' = xseq@[opid]"
    using mem_op_exe by auto
  then show ?thesis using f2 by auto    
qed    
  
lemma mem_state_trans_op4:
  assumes a1: "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')"
  shows "(set xseq) \<union> rops = (set xseq') \<union> rops'"
proof -
  show ?thesis using a1 mem_state_trans_op3
    by fastforce    
qed
  
lemma mem_state_trans_unique_op_id: 
assumes a1:"\<forall>opid. opid \<in> rops \<longrightarrow> \<not>(List.member xseq opid)"
and a2:"non_repeat_list xseq"
and a3:"po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')" 
shows "non_repeat_list xseq' \<and> (\<forall>opid. opid \<in> rops' \<longrightarrow> \<not>(List.member xseq' opid))"
proof -
  from a3 have "\<exists>opid. xseq' = xseq@[opid] \<and> opid \<in> (rops - rops')"
    using mem_state_trans_op2 mem_state_trans_op3 
    apply auto
    by (metis DiffD2 mem_op_exe mem_state_trans_def prod.sel(1) prod.sel(2) singletonI)    
  then obtain opid::op_id where f1: "xseq' = xseq@[opid] \<and> opid \<in> (rops - rops')"    
    by auto
  then have "\<not>(List.member xseq opid)"
    using a1 by auto  
  then have f2: "non_repeat_list xseq'"   
    using f1 a2 non_repeat_list_extend by fastforce
  from f1 a3 mem_state_trans_op have f3: "rops' = rops - {opid}"
    apply auto
    apply blast
    by fastforce
  then have f4: "\<forall>opid'. opid' \<in> rops - {opid} \<longrightarrow> \<not>(List.member (xseq@[opid]) opid')"
    using a1
    by (metis DiffD1 DiffD2 UnE list.set(1) list.simps(15) member_def set_append)       
  then show ?thesis 
    using f2 f3 f1 by auto
qed  
  
lemma mem_exe_seq_op_unique: 
  assumes a1: "List.length exe_list > 0"
  and a2: "(\<forall>i. i < (List.length exe_list) - 1 \<longrightarrow> 
                (po pbm \<turnstile>t (List.nth exe_list i) \<rightarrow> (List.nth exe_list (i+1))))"
  and a3: "non_repeat_list (fst (List.hd exe_list))"
  and a4: "\<forall>opid. opid \<in> (fst (snd (List.hd exe_list))) \<longrightarrow> 
                  \<not>(List.member (fst (List.hd exe_list)) opid)"
shows "non_repeat_list (fst (List.last exe_list)) \<and> 
       (\<forall>opid. opid \<in> (fst (snd (List.last exe_list))) \<longrightarrow> 
               \<not>(List.member (fst (List.last exe_list)) opid))"
proof (insert assms, induction "exe_list" arbitrary: po rule: rev_induct)
  case Nil
  then show ?case 
    by auto
next
  case (snoc x xs)  
  then show ?case 
  proof (cases "List.length xs > 0")
    case True
    then have f1: "List.length xs > 0"
      by auto
    then have f2: "hd (xs@[x]) = hd xs"
      by auto
    from f1 have f3: "\<forall>i<(length xs - 1). (po pbm \<turnstile>t (xs ! i) \<rightarrow> (xs ! (i + 1)))"
      using snoc(3)
    proof -
      { fix nn :: nat
        have ff1: "\<forall>n. 1 + n = Suc n"
          by (metis One_nat_def add.left_neutral plus_nat.simps(2))
        have "\<forall>n. \<not> n < length (butlast xs) \<or> Suc n < length xs"
          by (metis (no_types) One_nat_def Suc_less_eq Suc_pred f1 length_butlast)
        then have "\<not> nn < length xs - 1 \<or> (po pbm \<turnstile>t (xs ! nn) \<rightarrow> (xs ! (nn + 1)))"
          using ff1 by (metis (no_types) Suc_less_eq add.commute butlast_snoc length_butlast less_Suc_eq nth_append snoc.prems(2)) }
      then show ?thesis
        by meson
    qed
    from f2 have f4: "non_repeat_list (fst (hd xs))"  
      using snoc(4) by auto
    from f2 have f5: "\<forall>opid. opid \<in> fst (snd (hd xs)) \<longrightarrow> \<not> List.member (fst (hd xs)) opid"
      using snoc(5) by auto
    define xseq where "xseq = (fst (List.last xs))"
    define rops where "rops = (fst (snd (List.last xs)))"
    define s where "s = (snd (snd (List.last xs)))"
    define xseq' where "xseq' = (fst (List.last (xs@[x])))"
    define rops' where "rops' = (fst (snd (List.last (xs@[x]))))"
    define s' where "s' = (snd (snd (List.last (xs@[x]))))"    
    from f1 f3 f4 f5 have f6: "non_repeat_list xseq \<and>
      (\<forall>opid. opid \<in> rops \<longrightarrow> \<not> List.member xseq opid)"
      using snoc(1) xseq_def rops_def by auto
    have f7: "List.last xs = (xs@[x])!(List.length (xs@[x]) - 2)"
      by (metis (no_types, lifting) One_nat_def Suc_pred butlast_snoc diff_diff_left f1 last_conv_nth length_butlast length_greater_0_conv lessI nat_1_add_1 nth_append)
    have f8: "List.last (xs@[x]) = (xs@[x])!(List.length (xs@[x]) - 1)"
      by simp     
    from snoc(3) f7 f8 have "po pbm \<turnstile>t (List.last xs) \<rightarrow> (List.last (xs@[x]))"              
      by (metis (no_types, lifting) Nat.add_0_right One_nat_def Suc_pred add_Suc_right butlast_snoc diff_diff_left f1 length_butlast lessI nat_1_add_1) 
    then have "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')"
      using xseq_def rops_def s_def xseq'_def rops'_def s'_def
      by auto
    then have "non_repeat_list xseq' \<and> (\<forall>opid. opid \<in> rops' \<longrightarrow> \<not>(List.member xseq' opid))"
      using f6 mem_state_trans_unique_op_id
      by blast    
    then show ?thesis 
      using xseq'_def rops'_def         
      by auto
  next
    case False
    then have "List.length xs = 0"
      by auto
    then have "xs@[x] = [x]" 
      by auto
    then have "hd (xs@[x]) = last (xs@[x])"
      by auto
    then show ?thesis 
      using snoc by auto
  qed
qed
  
lemma valid_mem_exe_seq_op_unique0: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list" 
  and a2: "i < (List.length exe_list) - 1"  
shows "non_repeat_list (fst (exe_list!i)) \<and> 
       (\<forall>opid. opid \<in> (fst (snd (exe_list!i))) \<longrightarrow> \<not>(List.member (fst (exe_list!i)) opid))"
proof (insert assms, induction i)
  case 0
  then have "(fst (exe_list!0)) = []"
    unfolding valid_mem_exe_seq_def
  proof -
    assume "valid_program po pbm \<and> 0 < length exe_list \<and> fst (hd exe_list) = [] \<and> (\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (hd exe_list)))) \<and> (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and> (\<forall>i<length exe_list - 1. (po pbm \<turnstile>t exe_list ! i \<rightarrow> (exe_list ! (i + 1))))"
    then show ?thesis
      by (metis hd_conv_nth length_greater_0_conv)
  qed  
  then show ?case 
    using non_repeat_list_emp
    by (simp add: member_rec(2))       
next
  case (Suc i)
  have f1: "non_repeat_list (fst (exe_list ! i)) \<and>
    (\<forall>opid. opid \<in> fst (snd (exe_list ! i)) \<longrightarrow> \<not> List.member (fst (exe_list ! i)) opid)"
    using Suc by auto
  have f2: "(po pbm \<turnstile>t exe_list ! i \<rightarrow> (exe_list ! (i + 1)))"
    using Suc unfolding valid_mem_exe_seq_def
    by auto
  define xseq where "xseq \<equiv> (fst (exe_list ! i))"
  define rops where "rops \<equiv> (fst (snd (exe_list ! i)))"
  define s where "s \<equiv> (snd (snd (exe_list ! i)))"
  define xseq' where "xseq' \<equiv> (fst (exe_list ! (i+1)))"
  define rops' where "rops' \<equiv> (fst (snd (exe_list ! (i+1))))"
  define s' where "s' \<equiv> (snd (snd (exe_list ! (i+1))))"
  from f1 have f3: "\<forall>opid. opid \<in> rops \<longrightarrow> \<not>(List.member xseq opid) \<and> non_repeat_list xseq"  
    using rops_def xseq_def by auto
  from f2 have f4: "po pbm \<turnstile>t (xseq,rops,s) \<rightarrow> (xseq',rops',s')" 
    using xseq_def xseq'_def rops_def rops'_def s_def s'_def
    by auto
  from f3 f4 have "non_repeat_list xseq' \<and> (\<forall>opid. opid \<in> rops' \<longrightarrow> \<not>(List.member xseq' opid))"
    using mem_state_trans_unique_op_id
    by (metis f1 xseq_def)    
  then show ?case 
    using xseq'_def rops'_def
    by auto      
qed  
  
lemma valid_mem_exe_seq_op_unique:
  assumes a1:  "valid_mem_exe_seq po pbm exe_list" 
  shows "non_repeat_list (fst (List.last exe_list))"      
proof -
  have f1: "non_repeat_list (fst (List.hd exe_list))"
    using a1 unfolding valid_mem_exe_seq_def
    using non_repeat_list_emp by auto
  have f2: "\<forall>opid. opid \<in> (fst (snd (List.hd exe_list))) \<longrightarrow> 
                  \<not>(List.member (fst (List.hd exe_list)) opid)"
    using a1 unfolding valid_mem_exe_seq_def
    apply auto
    by (simp add: member_rec(2))
  show ?thesis 
    using mem_exe_seq_op_unique a1 f1 f2
    unfolding valid_mem_exe_seq_def
    by auto
qed  
  
lemma valid_mem_exe_seq_op_unique1:
  assumes a1:  "valid_mem_exe_seq po pbm exe_list" 
  and a2: "i < (List.length exe_list)"
  shows "non_repeat_list (fst (exe_list!i))"  
proof -
  show ?thesis using a1
    using valid_mem_exe_seq_op_unique0 valid_mem_exe_seq_op_unique
    by (metis (no_types, hide_lams) One_nat_def Suc_pred a2 last_conv_nth length_0_conv less_Suc_eq less_irrefl_nat valid_mem_exe_seq_def)    
qed  
 
lemma valid_mem_exe_seq_op_unique2:
  assumes a1: "valid_mem_exe_seq po pbm exe_list" 
  and a2: "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"  
  and a3: "i < (List.length exe_list) - 1"
shows "\<not> (List.member (fst (exe_list!i)) opid)"
proof (rule ccontr)  
  assume "\<not> \<not> List.member (fst (exe_list ! i)) opid"
  then have "List.member (fst (exe_list ! i)) opid"
    by auto
  then have f1: "\<exists>n. n \<le> length (fst (exe_list ! i)) - 1 \<and> (fst (exe_list ! i))!n = opid"
    by (metis (no_types, lifting) One_nat_def Suc_pred eq_imp_le in_set_conv_nth in_set_member length_pos_if_in_set less_Suc_eq less_imp_le)        
  have f2: "(fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]"
    using a2 mem_op_exe by auto
  from f1 f2 have f3: "\<exists>n. n \<le> length (fst (exe_list!(i+1))) - 2 \<and> 
                            (fst (exe_list!(i+1)))!n = opid"
    by (metis (no_types, hide_lams) Suc_1 Suc_eq_plus1 diff_diff_add last_conv_nth le_less_trans length_butlast not_less nth_append snoc_eq_iff_butlast)
  from f2 have f4: "\<exists>m. m = length (fst (exe_list!(i+1))) - 1 \<and> 
                        (fst (exe_list!(i+1)))!m = opid"
    by auto    
  then have f5: "\<exists>m. m > length (fst (exe_list!(i+1))) - 2 \<and> m = length (fst (exe_list!(i+1))) - 1 \<and>
                        (fst (exe_list!(i+1)))!m = opid"
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 \<open>\<not> \<not> List.member (fst (exe_list ! i)) opid\<close> add_diff_cancel_right diff_add_inverse2 diff_less f2 length_append length_pos_if_in_set lessI list.size(3) list.size(4) member_def nat_1_add_1)    
  from f3 f5 have "\<exists>m n. m \<noteq> n \<and>  n \<le> length (fst (exe_list!(i+1))) - 2 \<and>
                     m = length (fst (exe_list!(i+1))) - 1 \<and>
                   ((fst (exe_list!(i+1)))!m = (fst (exe_list!(i+1)))!n)"
    by (metis not_less)
  then have "\<exists>m n. m \<noteq> n \<and>  n < length (fst (exe_list!(i+1))) \<and>
                   m < length (fst (exe_list!(i+1))) \<and>
                   ((fst (exe_list!(i+1)))!m = (fst (exe_list!(i+1)))!n)"
    by (metis (no_types, hide_lams) One_nat_def diff_less f5 le_antisym length_0_conv length_greater_0_conv lessI less_imp_diff_less less_irrefl_nat not_less zero_diff)    
  then have f6: "\<not> (non_repeat_list (fst (exe_list!(i+1))))"
    unfolding non_repeat_list_def
    using nth_eq_iff_index_eq by auto      
 \<comment>\<open>   by auto \<close>
  from a3 have f7: "i+1 < length exe_list"
    by auto
  then have f7: "non_repeat_list (fst (exe_list!(i+1)))"
    using valid_mem_exe_seq_op_unique1 a1
    by auto
  then show False
    using f6 by auto      
qed  
   
lemma valid_exe_op_include:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"      
  and a2: "(opid m<(fst (List.last exe_list)) opid') = Some True"
  and a3: "(opid \<in> fst (snd (List.hd exe_list)) \<and> 
            opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid')"  
shows "(List.member (fst (last exe_list)) opid) \<and> (List.member (fst (last exe_list)) opid')"
proof -
  show ?thesis using assms
    unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def memory_order_before_def
    apply simp
    using in_set_member
    by fastforce
qed    
  
lemma valid_exe_all_order: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow> 
  \<forall>opid opid'. (opid \<in> fst (snd (List.hd exe_list)) \<and> 
                opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid') \<longrightarrow>
               ((opid m<(fst (List.last exe_list)) opid') = Some True \<or> 
                (opid' m<(fst (List.last exe_list)) opid) = Some True)"
  unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
  apply auto      
  apply (subgoal_tac "List.member (fst (last exe_list)) opid' \<and> List.member (fst (last exe_list)) opid")        
  unfolding memory_order_before_def
   apply simp
   prefer 2
  using in_set_member
   apply fastforce
  apply auto
  using valid_mem_exe_seq_op_unique list_elements_before
  by metis 
  
text {* The lemma below shows that the axiom Order is satisfied 
in any valid execution sequence of our operational model. 
We assume that each op_id is unique in executed_mem_ops. 
As a consequence, for any two op_ids in executed_mem_ops, 
either op_id1 < op_id2 or op_id2 < op_id1 in the list. *}
   
lemma axiom_order_sat: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow>  
  axiom_order opid opid' (fst (List.last exe_list)) pbm"   
proof -
  assume a1: "valid_mem_exe_seq_final po pbm exe_list"  
  show ?thesis unfolding axiom_order_def
  proof (rule impI)
    assume a2: "type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block} \<and>
      type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block} \<and>
      opid \<in> set (fst (last exe_list)) \<and> opid' \<in> set (fst (last exe_list)) \<and> opid \<noteq> opid'"
    then have "(opid \<in> fst (snd (List.hd exe_list)) \<and> 
                opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid')"
      using a1 unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def by auto      
    then show "(opid m<(fst (last exe_list)) opid') = Some True \<or> 
          (opid' m<(fst (last exe_list)) opid) = Some True" 
      using a1 valid_exe_all_order by auto
  qed  
qed 
  
  
lemma valid_mem_exe_seq_ops: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow> 
  (\<forall>opid. (\<exists>p. List.member (po p) opid \<and> p<(Suc max_proc)) \<longrightarrow> (List.member (fst (List.last exe_list)) opid))"    
  unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
  using in_set_member by fastforce

text {* The lemma below shows that the axiom Termination is (trivially) satisfied 
in any valid execution sequence of our operational model. *}   
    
lemma axiom_termination_sat: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow> 
  axiom_termination opid po (fst (List.last exe_list)) pbm"
  unfolding axiom_termination_def using valid_mem_exe_seq_ops
  by auto    
  
text {* The axiom Value is trivially satisfied in our operational model 
because our operational model directly uses the axiom to obtain the value of 
load operations. *}    
  
lemma valid_exe_xseq_sublist:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"
  and a2: "i < (List.length exe_list) - 1"
shows "(set (fst (List.nth exe_list i))) \<union> (fst (snd (List.nth exe_list i))) = 
       (set (fst (last exe_list)))"  
proof (insert assms, induction i)
  case 0
  then show ?case 
    unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
  proof -
    assume a1: "(valid_program po pbm \<and>
     0 < length exe_list \<and>
     fst (hd exe_list) = [] \<and>
     (\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (hd exe_list)))) \<and>
     (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and>
     (\<forall>i<length exe_list - 1. (po pbm \<turnstile>t (exe_list ! i) \<rightarrow> (exe_list ! (i + 1))))) \<and>
     fst (snd (hd exe_list)) = set (fst (last exe_list))"
    then have a1f: "valid_program po pbm \<and> 0 < length exe_list \<and> fst (hd exe_list) = [] \<and> (\<forall>n. (\<forall>na. \<not> List.member (po na) n) \<or> n \<in> fst (snd (hd exe_list))) \<and> fst (snd (hd exe_list)) = set (fst (last exe_list)) \<and> (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and> (\<forall>n. \<not> n < length exe_list - 1 \<or> (po pbm \<turnstile>t exe_list ! n \<rightarrow> (exe_list ! (n + 1))))"
      by blast
    assume a2: "0 < length exe_list - 1"
    then show ?thesis using a1f
      by (metis (no_types) hd_conv_nth length_greater_0_conv list.set(1) sup_bot.left_neutral)
  qed            
next
  case (Suc i)
  have f1: "(po pbm \<turnstile>t (List.nth exe_list i) \<rightarrow> (List.nth exe_list (i+1)))"
    using Suc unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
    using Suc_lessD by blast
  have f2: "(set (fst (exe_list ! i))) \<union> (fst (snd (exe_list ! i))) = 
            (set (fst (exe_list ! (i+1)))) \<union> (fst (snd (exe_list ! (i+1))))"
    using f1 mem_state_trans_op4
    by (metis prod.collapse)    
  then show ?case 
    using Suc by auto
qed  
  
lemma valid_exe_xseq_sublist2:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list) - 1"  
shows "\<exists>opid. (fst (exe_list!i))@[opid] = (fst (exe_list!(i+1)))"  
proof -
  have f1: "(po pbm \<turnstile>t (List.nth exe_list i) \<rightarrow> (List.nth exe_list (i+1)))"
    using a1 a2 unfolding valid_mem_exe_seq_def by auto
  then show ?thesis
    using mem_state_trans_op3  mem_op_exe 
    by (metis (no_types) f1 mem_op_exe mem_state_trans_def)
qed  
  
lemma valid_exe_xseq_sublist3:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < j"
  and a3: "j < (List.length exe_list)"
shows "is_sublist (fst (exe_list!i)) (fst (exe_list!j))"
proof (insert assms, induction j arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then show ?case 
  proof (cases "i = j")
    case True
    then have "\<exists>opid. (fst (exe_list!i))@[opid] = (fst (exe_list!(j+1)))"  
      using Suc(2) Suc(4) valid_exe_xseq_sublist2
      by (metis Suc_eq_plus1 less_diff_conv)    
    then show ?thesis 
      unfolding is_sublist_def
      by auto
  next
    case False
    then have f1: "i < j"
      using Suc(3) by auto
    have f2: "j < length exe_list"
      using Suc(4) by auto
    from f1 f2 have f3: "is_sublist (fst (exe_list ! i)) (fst (exe_list ! j))"
      using Suc(1) Suc(2) by auto
    have f4: "\<exists>opid. (fst (exe_list!j))@[opid] = (fst (exe_list!(j+1)))"  
      using Suc(2) Suc(4) valid_exe_xseq_sublist2  
      by auto  
    then show ?thesis 
      using f3 unfolding is_sublist_def
      by (metis Suc_eq_plus1 append.assoc)      
  qed  
qed
  
lemma valid_exe_xseq_sublist4:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list)"
shows "is_sublist (fst (exe_list!i)) (fst (List.last exe_list))"  
proof (cases "i = (List.length exe_list) - 1")
  case True
  then have "(fst (exe_list!i)) = (fst (List.last exe_list))"
    using a1 last_conv_nth valid_mem_exe_seq_def by fastforce      
  then show ?thesis 
    using is_sublist_id by auto
next
  case False
  then have "i < (List.length exe_list) - 1"
    using a2 by auto
  then have "is_sublist (fst (exe_list!i)) (fst (exe_list!((List.length exe_list) - 1)))"
    using a1 valid_exe_xseq_sublist3 by auto      
  then show ?thesis
    using a1 last_conv_nth valid_mem_exe_seq_def by fastforce     
qed 
  
lemma valid_exe_xseq_sublist5:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < j"
  and a3: "j < (List.length exe_list)"
  and a4: "po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))"
shows "List.member (fst (exe_list!j)) opid"  
proof -
  from a4 have "(fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]"
    using mem_op_exe by auto
  then have f1: "List.member (fst (exe_list!(i+1))) opid"
    by (metis One_nat_def Suc_eq_plus1 in_set_member length_append less_add_one list.size(3) list.size(4) nth_append_length nth_mem)
  show ?thesis
  proof (cases "i + 1 = j")
    case True          
    then show ?thesis 
      using f1 by auto
  next
    case False
    then have "i+1 < j"
      using a2 by auto
    then have f2: "is_sublist (fst (exe_list!(i+1))) (fst (exe_list!j))"
      using a1 a3 valid_exe_xseq_sublist3 by auto
    then show ?thesis 
      using f1 sublist_member by auto
  qed    
qed  
  
lemma valid_exe_xseq_sublist6:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list) - 1"
shows "(set (fst (List.nth exe_list i))) \<union> (fst (snd (List.nth exe_list i))) = 
       (fst (snd (hd exe_list)))"  
proof (insert assms, induction i)
  case 0
  then show ?case 
    unfolding valid_mem_exe_seq_def 
  proof -
    assume a1: "(valid_program po pbm \<and>
     0 < length exe_list \<and>
     fst (hd exe_list) = [] \<and>
     (\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (hd exe_list)))) \<and>
     (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and>
     (\<forall>i<length exe_list - 1. (po pbm \<turnstile>t (exe_list ! i) \<rightarrow> (exe_list ! (i + 1)))))"
    then have a1f: "valid_program po pbm \<and> 0 < length exe_list \<and> fst (hd exe_list) = [] \<and> 
      (\<forall>n. (\<forall>na. \<not> List.member (po na) n) \<or> n \<in> fst (snd (hd exe_list))) \<and>        
      (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and> 
      (\<forall>n. \<not> n < length exe_list - 1 \<or> (po pbm \<turnstile>t exe_list ! n \<rightarrow> (exe_list ! (n + 1))))"
      by blast
    assume a2: "0 < length exe_list - 1"
    then show ?thesis using a1f
      by (metis (no_types) hd_conv_nth length_greater_0_conv list.set(1) sup_bot.left_neutral)
  qed            
next
  case (Suc i)
  have f1: "(po pbm \<turnstile>t (List.nth exe_list i) \<rightarrow> (List.nth exe_list (i+1)))"
    using Suc unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
    using Suc_lessD by blast
  have f2: "(set (fst (exe_list ! i))) \<union> (fst (snd (exe_list ! i))) = 
            (set (fst (exe_list ! (i+1)))) \<union> (fst (snd (exe_list ! (i+1))))"
    using f1 mem_state_trans_op4
    by (metis prod.collapse)    
  then show ?case 
    using Suc by auto
qed    
  
lemma valid_exe_xseq_sublist7:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list)"
shows "(set (fst (List.nth exe_list i))) \<union> (fst (snd (List.nth exe_list i))) = 
       (fst (snd (hd exe_list)))"  
proof (cases "i < (List.length exe_list) - 1")
  case True  
  then show ?thesis using valid_exe_xseq_sublist6[OF a1 True] by auto
next
  case False
  then have f1: "i = (List.length exe_list) - 1"
    using a2 by auto
  then show ?thesis 
  proof (cases "(List.length exe_list) > 1")
    case True
    then obtain j where f2: "0 \<le> j \<and> j = i - 1"
      using f1 by auto
    then have f3: "(set (fst (List.nth exe_list j))) \<union> (fst (snd (List.nth exe_list j))) = 
       (fst (snd (hd exe_list)))"
      using valid_exe_xseq_sublist6[OF a1] f1
      using True by auto 
    from a1 f1 f2 True have f4: "(po pbm \<turnstile>t (exe_list!j) \<rightarrow> (exe_list!i))"
      unfolding valid_mem_exe_seq_def
      by (metis diff_add diff_diff_cancel diff_is_0_eq le_eq_less_or_eq less_one nat_neq_iff)
    then have f5: "(set (fst (exe_list!j))) \<union> (fst (snd (exe_list!j))) = 
      (set (fst (exe_list!i))) \<union> (fst (snd (exe_list!i)))"
      using mem_state_trans_op4
      by (metis surjective_pairing) 
    then show ?thesis using f3 by auto
  next
    case False
    then have f6: "(length exe_list) = 1"
      using a1 unfolding valid_mem_exe_seq_def
      by linarith 
    then have f7: "(exe_list!i) = (hd exe_list)"
      using f1
      by (metis diff_self_eq_0 hd_conv_nth list.size(3) zero_neq_one)
    then show ?thesis using a1 unfolding valid_mem_exe_seq_def by auto
  qed  
qed  
  
lemma valid_exe_xseq_sublist_last:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
shows "(set (fst (last exe_list))) \<union> (fst (snd (last exe_list))) = 
       (fst (snd (hd exe_list)))"  
proof -
  from a1 have f1: "length exe_list > 0"
    unfolding valid_mem_exe_seq_def by auto
  then obtain i where f2: "i \<ge> 0 \<and> i = (length exe_list) - 1"
    by simp
  then have f3: "i < length exe_list"      
    using f1 by auto
  then have "(set (fst (exe_list!i))) \<union> (fst (snd (exe_list!i))) = 
       (fst (snd (hd exe_list)))"
    using valid_exe_xseq_sublist7[OF a1 f3] by auto
  then show ?thesis using f1 f2
    by (simp add: last_conv_nth)  
qed  
  
lemma valid_exe_xseq_sublist_length:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list)"
shows "List.length (fst (exe_list!i)) = i"    
proof (insert assms, induction i)
  case 0
  then show ?case 
    unfolding valid_mem_exe_seq_def
  proof -
    assume "valid_program po pbm \<and> 0 < length exe_list \<and> fst (hd exe_list) = [] \<and> (\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (hd exe_list)))) \<and> (atomic_flag_val (snd (snd (hd exe_list))) = None) \<and> (\<forall>i<length exe_list - 1. (po pbm \<turnstile>t exe_list ! i \<rightarrow> (exe_list ! (i + 1))))"
    then show ?thesis
      by (metis (no_types) gr_implies_not0 hd_conv_nth length_0_conv)
  qed    
next
  case (Suc i)  
  have f1: "length (fst (exe_list ! i)) = i"
    using Suc by auto
  from Suc(3) have "i < length exe_list - 1"  
    by auto    
  then have "(po pbm \<turnstile>t (exe_list!i) \<rightarrow> (exe_list!(i+1)))"
    using Suc(2) unfolding valid_mem_exe_seq_def
    by auto
  then have "length (fst (exe_list ! i)) + 1 = length (fst (exe_list ! (i+1)))"
    using mem_state_trans_op
    by (metis (no_types, lifting) One_nat_def Suc.prems(1) Suc_eq_plus1 \<open>i < length exe_list - 1\<close> length_append list.size(3) list.size(4) valid_exe_xseq_sublist2)  
  then show ?case 
    using f1 by auto 
qed  
  
lemma valid_exe_xseq_sublist_length2:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  shows "List.length (fst (List.last exe_list)) = (List.length exe_list) - 1"      
proof -
  from a1 have "List.length exe_list > 0" 
    unfolding valid_mem_exe_seq_def by auto
  then have "(List.length exe_list) - 1 < (List.length exe_list)"
    by auto
  then show ?thesis 
    using a1 valid_exe_xseq_sublist_length \<open>0 < length exe_list\<close> last_conv_nth by fastforce  
qed  
  
lemma op_exe_xseq: 
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
    and a2: "opid \<noteq> opid'"
    and a3: "\<not> (List.member xseq opid')"
  shows "\<not> (List.member xseq' opid')"
proof -
  show ?thesis 
    using mem_op_exe
    by (metis a1 a2 a3 in_set_member rotate1.simps(2) set_ConsD set_rotate1)    
qed
  
lemma valid_exe_op_exe_exist0:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "\<forall>opid i. ((i < (List.length exe_list - 1)) \<and> 
                     (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
                     (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))) \<longrightarrow>
                    opid \<noteq> opid'"
  and a3: "n < (List.length exe_list - 1)"
shows "\<not> (List.member (fst (exe_list!n)) opid')"  
proof -
  have f1: "\<forall>i<length exe_list - 1. (po pbm \<turnstile>t (exe_list ! i) \<rightarrow> (exe_list ! (i + 1)))"
    using a1 unfolding valid_mem_exe_seq_def
    by auto
  then have f2: "\<forall>i<length exe_list - 1. (\<exists>opid. opid \<in> (fst (snd (List.nth exe_list i))) \<and> 
          (po pbm opid \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow> (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1))))) \<and>
          (fst (snd (List.nth exe_list (i+1)))) = (fst (snd (List.nth exe_list i))) - {opid})"
    unfolding mem_state_trans_def
    by auto
  then have f3: "\<forall>i<length exe_list - 1. (\<exists>opid. opid \<in> (fst (snd (List.nth exe_list i))) \<and> 
          (po pbm opid \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow> (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1))))) \<and>
          (fst (snd (List.nth exe_list (i+1)))) = (fst (snd (List.nth exe_list i))) - {opid} \<and>
          opid \<noteq> opid')"
    using a2
    by meson     
  show ?thesis
  proof (insert a3, induction n)
    case 0
    then show ?case 
      using a1 unfolding valid_mem_exe_seq_def
      apply auto
      by (metis (no_types) hd_conv_nth member_rec(2))      
  next
    case (Suc n)
    obtain opid where f4: "(po pbm opid \<turnstile>m (fst (exe_list ! n)) (snd (snd (exe_list ! n))) \<rightarrow>
                         (fst (exe_list ! Suc n)) (snd (snd (exe_list ! Suc n)))) \<and>
                       opid \<noteq> opid'"  
      using f3 Suc
      by (metis Suc_eq_plus1 Suc_lessD)        
    then show ?case 
      using Suc(1) op_exe_xseq Suc.prems Suc_lessD 
      by blast 
  qed
qed
  
lemma valid_exe_op_exe_exist1:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "\<forall>opid i. ((i < (List.length exe_list - 1)) \<and> 
                     (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
                     (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))) \<longrightarrow>
                    opid \<noteq> opid'"
shows "\<not> (List.member (fst (List.last exe_list)) opid')"    
proof -
  have f1: "\<not> (List.member (fst (exe_list!(List.length exe_list - 2))) opid')"
    using assms valid_exe_op_exe_exist0      
  proof -
    have f1: "Suc (Suc 0) = 2"
      by linarith
    have "0 < length exe_list"
      using a1 valid_mem_exe_seq_def by blast
    then have f2: "length exe_list - 2 = length (butlast (butlast exe_list))"
      using f1 by (metis (no_types) One_nat_def Suc_pred diff_Suc_Suc length_butlast)
    have "\<forall>ps f fa n. \<exists>na. \<forall>nb nc. (\<not> valid_mem_exe_seq f fa ps \<or> \<not> List.member (fst (ps ! nb)) n \<or> \<not> nb < length ps - 1 \<or> na < length ps - 1) \<and> (\<not> valid_mem_exe_seq f fa ps \<or> \<not> List.member (fst (ps ! nc)) n \<or> \<not> nc < length ps - 1 \<or> (f fa n \<turnstile>m (fst (ps ! na)) (snd (snd (ps ! na))) \<rightarrow> (fst (ps ! (na + 1))) (snd (snd (ps ! (na + 1))))))"
      using valid_exe_op_exe_exist0 by blast
    then show ?thesis
      using f2
      by (metis (no_types, lifting) \<open>0 < length exe_list\<close> a1 a2 add_lessD1 diff_less in_set_member length_butlast length_pos_if_in_set less_diff_conv less_numeral_extra(1) valid_exe_xseq_sublist_length zero_less_numeral)
  qed      
  then show ?thesis 
  proof (cases "List.length exe_list > 1")
    case True
    then have "(List.length exe_list - 2) < (List.length exe_list - 1)"
      by auto
    then obtain opid where "(po pbm opid \<turnstile>m (fst (exe_list!(List.length exe_list - 2))) (snd (snd (exe_list!(List.length exe_list - 2)))) \<rightarrow>
                     (fst (exe_list!(List.length exe_list - 1))) (snd (snd (exe_list!(List.length exe_list - 1))))) \<and>
                    opid \<noteq> opid'"
      using a1 a2 unfolding valid_mem_exe_seq_def mem_state_trans_def
      apply auto
      by (metis (no_types, hide_lams) Suc_1 Suc_diff_Suc True numeral_1_eq_Suc_0 numeral_One)
    then have "\<not> (List.member (fst (exe_list!(List.length exe_list - 1))) opid')" 
      using op_exe_xseq f1
      by blast
    then show ?thesis 
      using True a1 last_conv_nth valid_mem_exe_seq_def by fastforce               
  next
    case False
    then have "length exe_list = 1"
      using a1 less_linear valid_mem_exe_seq_def by fastforce
    then have "(fst (last exe_list)) = (fst (hd exe_list))"
      by (metis cancel_comm_monoid_add_class.diff_cancel hd_conv_nth last_conv_nth length_0_conv zero_neq_one)        
    then show ?thesis 
      using a1 unfolding valid_mem_exe_seq_def
      by (simp add: member_rec(2))      
  qed    
qed    
  
lemma valid_exe_op_exe_exist2:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"  
  and a2: "opid \<in> fst (snd (List.hd exe_list))"
shows "\<exists>i. (i < (List.length exe_list - 1)) \<and> 
           (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"  
proof (rule ccontr)
  assume a3: "\<not> (\<exists>i. (i < (List.length exe_list - 1)) \<and> 
           (po pbm opid \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow>
            (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1))))))"
  have f1: "\<forall>i<length exe_list - 1. 
            (\<exists>opid.(po pbm opid \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow>
            (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1))))))"
    using a1 unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def mem_state_trans_def
    by auto      
  then have f2: "\<forall>i<length exe_list - 1. 
            (\<forall>opid'.(po pbm opid' \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow>
            (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1))))) \<longrightarrow>
             opid' \<noteq> opid)"
    using a3 by auto    
  then have f3: "\<forall>opid' i. ((i < (List.length exe_list - 1)) \<and> 
                     (po pbm opid' \<turnstile>m (fst (List.nth exe_list i)) (snd (snd (List.nth exe_list i))) \<rightarrow>
                     (fst (List.nth exe_list (i+1))) (snd (snd (List.nth exe_list (i+1)))))) \<longrightarrow>
                    opid \<noteq> opid'" 
    by auto
  then have f4: "\<not> (List.member (fst (List.last exe_list)) opid)"
    using valid_exe_op_exe_exist1 a1 valid_mem_exe_seq_final_def by blast 
  have f5: "List.member (fst (List.last exe_list)) opid"
    using a2 a1 unfolding valid_mem_exe_seq_final_def valid_mem_exe_seq_def
    by (simp add: in_set_member)      
  show False 
    using f4 f5
    by auto  
qed  

lemma valid_exe_op_exe_unique:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "opid \<in> fst (snd (List.hd exe_list))"
  and a3: "i < (List.length exe_list - 1)"
  and a4: "po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))"
  and a5: "i \<noteq> j \<and> j < (List.length exe_list - 1)"  
shows "\<not> (po pbm opid \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
           (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"   
proof (rule ccontr)
  assume "\<not> \<not>(po pbm opid \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
           (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"
  then have f1: "po pbm opid \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
           (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))"
    by auto
  from a5 have "i < j \<or> j < i"
    by auto  
  then show False 
  proof (rule disjE)
    assume a6: "i < j"
    then have f2: "List.member (fst (exe_list!j)) opid" 
      using a1 a4 a5 valid_exe_xseq_sublist5 by auto
    from f1 have f3: "(fst (exe_list!(j+1))) = (fst (exe_list!j))@[opid]"
      using mem_op_exe by auto
    then have f4: "\<not> (non_repeat_list (fst (exe_list!(j+1))))"
      using f2 unfolding non_repeat_list_def
      apply auto
      using a1 a5 f1 valid_mem_exe_seq_op_unique2 by auto
    from a1 a5 have "is_sublist (fst (exe_list!(j+1))) (fst (List.last exe_list))"  
      using valid_exe_xseq_sublist4 by auto
    then have "\<not> (non_repeat_list (fst (List.last exe_list)))"
      using f4 sublist_repeat by auto    
    then show False 
      using a1 valid_mem_exe_seq_op_unique by auto
  next    
    assume a7: "j < i"
    then have f2: "List.member (fst (exe_list!i)) opid" 
      using a1 a3 a5 f1 valid_exe_xseq_sublist5 by auto
    then have f5: "(fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]"
      using a4 mem_op_exe by auto
    then have f4: "\<not> (non_repeat_list (fst (exe_list!(i+1))))"
      using f2 unfolding non_repeat_list_def
      apply auto
      using a1 a3 a4 valid_mem_exe_seq_op_unique2 by auto
    from a1 a3 have "is_sublist (fst (exe_list!(i+1))) (fst (List.last exe_list))"  
      using valid_exe_xseq_sublist4 by auto
    then have "\<not> (non_repeat_list (fst (List.last exe_list)))"
      using f4 sublist_repeat by auto    
    then show False 
      using a1 valid_mem_exe_seq_op_unique by auto
  qed
qed  
  
lemma valid_exe_op_exe_pos:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "(fst (List.last exe_list))!i = opid"
  and a3: "i < (List.length exe_list - 1)"
shows "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))" 
proof -
  have "(po pbm \<turnstile>t (exe_list!i) \<rightarrow> (exe_list!(i+1)))"
    using a1 a3 unfolding valid_mem_exe_seq_def
    by auto
  then have "\<exists>opid. opid \<in> (fst (snd (exe_list!i))) \<and> 
          (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow> 
                          (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and>
          (fst (snd (exe_list!(i+1)))) = (fst (snd (exe_list!i))) - {opid}" 
    unfolding mem_state_trans_def by auto
  then have f1: "\<exists>opid. opid \<in> (fst (snd (exe_list!i))) \<and> 
          (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow> 
                          (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and>
          (fst (snd (exe_list!(i+1)))) = (fst (snd (exe_list!i))) - {opid} \<and>
          (fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]" 
    using mem_op_exe
    by fastforce
  then have f2: "List.length (fst (exe_list!(i+1))) = i + 1"
    using valid_exe_xseq_sublist_length a1 a3 by auto
  also have f3: "is_sublist (fst (exe_list!(i+1))) (fst (List.last exe_list))"
    using a1 a3 valid_exe_xseq_sublist4 by auto
  then have "(fst (exe_list!(i+1)))!i = (fst (List.last exe_list))!i"
    using sublist_element f2 by fastforce
  then have "(fst (exe_list!(i+1)))!i = opid"
    using a2 by auto
  then have "List.last (fst (exe_list!(i+1))) = opid"
    using f2
    by (metis add_diff_cancel_right' append_is_Nil_conv f1 last_conv_nth list.distinct(1))
  then have "opid \<in> (fst (snd (exe_list!i))) \<and> 
          (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow> 
                          (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and>
          (fst (snd (exe_list!(i+1)))) = (fst (snd (exe_list!i))) - {opid} \<and>
          (fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]"
    using f1 by fastforce
  then show ?thesis by blast
qed  
  
lemma valid_exe_op_exe_pos2:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "i < (List.length exe_list - 1)"
shows "(po pbm ((fst (List.last exe_list))!i) \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"   
  using a1 a2 valid_exe_op_exe_pos
  by blast

lemma valid_exe_op_exe_pos3:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "i < (List.length exe_list - 1)"
  and a3: "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"       
shows "((fst (List.last exe_list))!i) = opid"
proof -
  from a1 a2 have "(po pbm ((fst (List.last exe_list))!i) \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
    using valid_exe_op_exe_pos2 by auto
  then have f1: "(fst (exe_list!(i+1))) = (fst (exe_list!i))@[((fst (List.last exe_list))!i)]"
    using mem_op_exe by auto
  from a3 have "(fst (exe_list!(i+1))) = (fst (exe_list!i))@[opid]"
    using mem_op_exe by auto
  then show ?thesis using f1
    by auto
qed  
    
lemma valid_exe_op_exe_pos_unique:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "i < (List.length exe_list - 1) \<and> j < (List.length exe_list - 1) \<and> i \<noteq> j"
  and a3: "po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))"
  and a4: "po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
        (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))"
shows "opid \<noteq> opid'"
proof (rule ccontr)
  assume "\<not> opid \<noteq> opid'"
  then have f0: "opid = opid'"
    by auto
  from a1 a2 have f01: "i < length (fst (last exe_list)) \<and> j < length (fst (last exe_list))"
    using valid_exe_xseq_sublist_length2 by auto
  from a1 have f1: "non_repeat_list (fst (List.last exe_list))"
    using valid_mem_exe_seq_op_unique by auto
  from a1 a2 a3 have f2: "((fst (List.last exe_list))!i) = opid"
    using valid_exe_op_exe_pos3 by auto
  from a1 a2 a4 have f3: "((fst (List.last exe_list))!j) = opid'"
    using valid_exe_op_exe_pos3 by auto
  from f0 f2 f3 have "((fst (List.last exe_list))!i) = ((fst (List.last exe_list))!j)"
    by auto
  then show False using a2 f1 f01 unfolding non_repeat_list_def
    using nth_eq_iff_index_eq by auto  
   \<comment>\<open> by auto \<close>
qed  
  
lemma valid_exe_op_order0:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"  
  and a2: "(opid m<(fst (List.last exe_list)) opid') = Some True"
  and a3: "(opid \<in> fst (snd (List.hd exe_list)) \<and> 
            opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid')" 
shows "\<exists>i j.(i < (List.length exe_list - 1)) \<and>
            (j < (List.length exe_list - 1)) \<and>
            (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
            (po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and>
            i < j"
proof -
  from a1 a3 have "opid \<in> set (fst (List.last exe_list)) \<and> 
                opid' \<in> set (fst (List.last exe_list)) \<and> opid \<noteq> opid'"    
    unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def by auto
  then have "List.member (fst (List.last exe_list)) opid \<and> 
             List.member (fst (List.last exe_list)) opid' \<and> opid \<noteq> opid'"
    by (simp add: in_set_member)
  then have "list_before opid (fst (List.last exe_list)) opid'"
    using a2 unfolding memory_order_before_def
    apply auto
    using option.inject by fastforce
  then have "\<exists>i j. 0 \<le> i \<and> i < length (fst (List.last exe_list)) \<and> 
                   0 \<le> j \<and> j < length (fst (List.last exe_list)) \<and> 
                   ((fst (List.last exe_list))!i) = opid \<and> 
                   ((fst (List.last exe_list))!j) = opid' \<and> i < j"    
    unfolding list_before_def by simp
  then have "\<exists>i j. 0 \<le> i \<and> i < length exe_list - 1 \<and> 
                   0 \<le> j \<and> j < length exe_list - 1 \<and> 
                   ((fst (List.last exe_list))!i) = opid \<and> 
                   ((fst (List.last exe_list))!j) = opid' \<and> i < j"
    using valid_exe_xseq_sublist_length a1 valid_mem_exe_seq_final_def
    by (metis valid_exe_xseq_sublist_length2)
  then have "\<exists>i j. 0 \<le> i \<and> i < length exe_list - 1 \<and> 
                   0 \<le> j \<and> j < length exe_list - 1 \<and> 
                   (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
                    (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
                   (po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
                    (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and> i < j"   
    using valid_exe_op_exe_pos a1 valid_mem_exe_seq_final_def
    by blast
  then show ?thesis by auto
qed    
  
lemma valid_exe_op_order:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"  
  and a2: "(opid m<(fst (List.last exe_list)) opid') = Some True"
  and a3: "(opid \<in> fst (snd (List.hd exe_list)) \<and> 
            opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid')" 
shows "\<exists>i. (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
           \<not> (List.member (fst (exe_list!i)) opid')"
proof (rule ccontr)
  assume a4: "\<nexists>i. (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and>
        \<not> List.member (fst (exe_list ! i)) opid'"
  obtain i j where f1: "(i < (List.length exe_list - 1)) \<and>
            (j < (List.length exe_list - 1)) \<and>
            (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
            (po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and>
            i < j"
    using assms valid_exe_op_order0 by blast
  from a4 f1 have f2: "List.member (fst (exe_list ! i)) opid'"
    by auto
  from a1 f1 have f3: "is_sublist (fst (exe_list!i)) (fst (exe_list!j))"
    using valid_exe_xseq_sublist3 valid_mem_exe_seq_final_def by auto
  then have f4: "List.member (fst (exe_list ! j)) opid'"
    using f2 sublist_member by fastforce
  then show False
    using a1 f1 valid_mem_exe_seq_op_unique2 valid_mem_exe_seq_final_def by blast 
qed  
  
lemma valid_exe_op_order2:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"  
  and a2: "(List.member (fst (List.last exe_list)) opid \<and>
            List.member (fst (List.last exe_list)) opid' \<and> opid \<noteq> opid')" 
shows "((opid m<(fst (List.last exe_list)) opid') = Some True \<or> 
        (opid' m<(fst (List.last exe_list)) opid) = Some True)"  
proof -
  from a2 have "(opid \<in> set (fst (List.last exe_list))) \<and> (opid' \<in> set (fst (List.last exe_list)))" 
    by (simp add: in_set_member)
  then have "(opid \<in> fst (snd (List.hd exe_list))) \<and> (opid' \<in> fst (snd (List.hd exe_list)))"
    using a1 unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def
    by auto
  then show ?thesis
    using a1 valid_exe_all_order a2 by auto
qed  
  
lemma valid_exe_op_order_3ops:
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"  
  and a2: "(opid m<(fst (List.last exe_list)) opid') = Some True"
  and a3: "(opid \<in> fst (snd (List.hd exe_list)) \<and> 
            opid' \<in> fst (snd (List.hd exe_list)) \<and> opid \<noteq> opid')" 
  and a4: "(opid' m<(fst (List.last exe_list)) opid'') = Some True"
  and a5: "opid'' \<in> fst (snd (List.hd exe_list)) \<and> opid' \<noteq> opid''"
shows "\<exists>i j k.(i < (List.length exe_list - 1)) \<and>
            (j < (List.length exe_list - 1)) \<and>
            (k < (List.length exe_list - 1)) \<and>
            (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
            (po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and>
            (po pbm opid'' \<turnstile>m (fst (exe_list!k)) (snd (snd (exe_list!k))) \<rightarrow>
             (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1))))) \<and>
            i < j \<and> j < k"
proof-
  from a3 a5 have f0: "opid \<noteq> opid' \<and> opid' \<noteq> opid''"
    by auto
  from a1 a3 a5 have "opid \<in> set (fst (List.last exe_list)) \<and> 
                opid' \<in> set (fst (List.last exe_list)) \<and>
                opid'' \<in> set (fst (List.last exe_list))"
    unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def by auto
  then have f1: "List.member (fst (List.last exe_list)) opid \<and> 
             List.member (fst (List.last exe_list)) opid' \<and>
             List.member (fst (List.last exe_list)) opid''"
    by (simp add: in_set_member)
  then have f2: "list_before opid (fst (List.last exe_list)) opid' \<and> 
                 list_before opid' (fst (List.last exe_list)) opid''"    
    using a2 a4 unfolding memory_order_before_def
    apply auto      
    using option.inject apply fastforce      
    using option.inject by fastforce
  then have f3: "\<exists>i j. 0 \<le> i \<and> i < length (fst (List.last exe_list)) \<and> 
                   0 \<le> j \<and> j < length (fst (List.last exe_list)) \<and> 
                   ((fst (List.last exe_list))!i) = opid \<and> 
                   ((fst (List.last exe_list))!j) = opid' \<and> i < j"    
    unfolding list_before_def by simp
  from f2 have f4: "\<exists>jb k. 0 \<le> jb \<and> jb < length (fst (List.last exe_list)) \<and> 
                   0 \<le> k \<and> k < length (fst (List.last exe_list)) \<and> 
                   ((fst (List.last exe_list))!jb) = opid' \<and> 
                   ((fst (List.last exe_list))!k) = opid'' \<and> jb < k"    
    unfolding list_before_def by simp    
  from a1 have "non_repeat_list (fst (List.last exe_list))"
    using valid_mem_exe_seq_op_unique valid_mem_exe_seq_final_def by auto
  then have "\<exists>i j k. 0 \<le> i \<and> i < length (fst (List.last exe_list)) \<and> 
                   0 \<le> j \<and> j < length (fst (List.last exe_list)) \<and> 
                   0 \<le> k \<and> k < length (fst (List.last exe_list)) \<and> 
                   ((fst (List.last exe_list))!i) = opid \<and> 
                   ((fst (List.last exe_list))!j) = opid' \<and> 
                   ((fst (List.last exe_list))!k) = opid'' \<and> i < j \<and> j < k"
    using non_repeat_list_pos_unique f3 f4 by metis
  then have "\<exists>i j k. 0 \<le> i \<and> i < length exe_list - 1 \<and> 
                   0 \<le> j \<and> j < length exe_list - 1 \<and> 
                   0 \<le> k \<and> k < length exe_list - 1 \<and> 
                   ((fst (List.last exe_list))!i) = opid \<and> 
                   ((fst (List.last exe_list))!j) = opid' \<and> 
                   ((fst (List.last exe_list))!k) = opid'' \<and> i < j \<and> j < k" 
    using valid_exe_xseq_sublist_length a1 valid_mem_exe_seq_final_def
    by (metis valid_exe_xseq_sublist_length2)
  then have "\<exists>i j k. 0 \<le> i \<and> i < length exe_list - 1 \<and> 
                   0 \<le> j \<and> j < length exe_list - 1 \<and> 
                   0 \<le> k \<and> k < length exe_list - 1 \<and> 
                   (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
                    (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
                   (po pbm opid' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
                    (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and> 
                   (po pbm opid'' \<turnstile>m (fst (exe_list!k)) (snd (snd (exe_list!k))) \<rightarrow>
                    (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1))))) \<and> i < j \<and> j < k"
    using valid_exe_op_exe_pos a1 valid_mem_exe_seq_final_def by blast
  then show ?thesis by auto
qed  
  
lemma prog_order_op_unique: 
  assumes a1: "valid_program po pbm"
  and a2: "opid ;po^p opid'"  
shows "opid \<noteq> opid'"
proof -
  from a1 a2 have f1: "non_repeat_list (po p)"
    unfolding valid_program_def
    by blast
  from a2 have "\<exists>i j. 0 \<le> i \<and> i < length (po p) \<and> 0 \<le> j \<and> j < length (po p) \<and>
                ((po p)!i) = opid \<and> ((po p)!j) = opid' \<and> i < j"
    unfolding program_order_before_def list_before_def
    by auto
  then show ?thesis using f1
    unfolding non_repeat_list_def
    using nth_eq_iff_index_eq by auto
\<comment>\<open>    by auto   \<close>
qed   
  
lemma prog_order_op_exe: 
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"
  and a2: "opid ;po^p opid'"
shows "List.member (fst (List.last exe_list)) opid \<and> 
       List.member (fst (List.last exe_list)) opid'"
proof -
  from a2 have "\<exists>i j. 0 \<le> i \<and> i < length (po p) \<and> 0 \<le> j \<and> j < length (po p) \<and> 
                     ((po p)!i) = opid \<and> ((po p)!j) = opid' \<and> i < j"
    unfolding program_order_before_def list_before_def
    by auto   
  then have "List.member (po p) opid \<and> List.member (po p) opid'"
    using list_mem_range_rev
    by metis 
  then have "(opid \<in> fst (snd (List.hd exe_list))) \<and> (opid' \<in> fst (snd (List.hd exe_list)))"
    using a1 unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def
    by auto
  then have "(opid \<in> set (fst (List.last exe_list))) \<and> (opid' \<in> set (fst (List.last exe_list)))"
    using a1 unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def
    by auto      
  then show ?thesis
    by (simp add: in_set_member)         
qed  
  
lemma prog_order_op_exe2: 
  assumes a1: "valid_mem_exe_seq_final po pbm exe_list"
  and a2: "opid ;po^p opid'"
shows "((opid m<(fst (List.last exe_list)) opid') = Some True \<or> 
        (opid' m<(fst (List.last exe_list)) opid) = Some True)"  
proof -   
  from assms have f1: "List.member (fst (List.last exe_list)) opid \<and> 
                       List.member (fst (List.last exe_list)) opid'"
    using prog_order_op_exe by auto
  have f4: "opid \<noteq> opid'"    
    using prog_order_op_unique a1 a2 valid_mem_exe_seq_def valid_mem_exe_seq_final_def
    by blast         
  then show ?thesis
    using a1 f1 valid_exe_op_order2 by auto 
qed  
    
text {* The lemma below shows that the LoadOp axiom is satisfied in every valid
sequence of executions in the operational TSO model. *}  
  
lemma axiom_loadop_sat: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow> 
  axiom_loadop opid opid' po (fst (List.last exe_list)) pbm"
proof -
  assume a1: "valid_mem_exe_seq_final po pbm exe_list"
  show "axiom_loadop opid opid' po (fst (List.last exe_list)) pbm"
  proof (rule ccontr)
    assume a2: "\<not>(axiom_loadop opid opid' po (fst (List.last exe_list)) pbm)"
    then obtain p where f1: "(type_of_mem_op_block (pbm opid) \<in> {ld_block, ald_block}) \<and>
      (p = proc_of_op opid pbm) \<and> (opid ;po^p opid') \<and> 
      \<not> ((opid m<(fst (List.last exe_list)) opid') = Some True)"
      unfolding axiom_loadop_def
      by auto
    from a1 f1 have f2: "(opid' m<(fst (List.last exe_list)) opid) = Some True"
      using prog_order_op_exe2 by blast
    from a1 f1 have f3: "List.member (fst (List.last exe_list)) opid \<and> 
      List.member (fst (List.last exe_list)) opid' \<and> opid \<noteq> opid'" 
      using prog_order_op_exe prog_order_op_unique valid_mem_exe_seq_def valid_mem_exe_seq_final_def by blast
    then obtain i where f4: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
           \<not> (List.member (fst (exe_list!i)) opid)"
      using f2 a1 valid_exe_op_order valid_mem_exe_seq_final_def
      by (metis in_set_member)  
    then have f5: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"   
      by auto
    have "(\<forall>opid''. ((opid'' ;po^(proc_of_op opid pbm) opid') \<and>
          (type_of_mem_op_block (pbm opid'') = ld_block \<or>
          type_of_mem_op_block (pbm opid'') = ald_block)) \<longrightarrow>
          List.member (fst (exe_list!i)) opid'') \<Longrightarrow> False"  
      using f1 f4 by auto               
    then have f6: "(\<forall>opid''. ((opid'' ;po^(proc_of_op opid' pbm) opid') \<and>
               (type_of_mem_op_block (pbm opid'') = ld_block \<or>
                 type_of_mem_op_block (pbm opid'') = ald_block)) \<longrightarrow>
                List.member (fst (exe_list!i)) opid'') \<Longrightarrow> False"
      using a1 unfolding valid_mem_exe_seq_def valid_program_def valid_mem_exe_seq_final_def
      using f1 by force     
    have "\<forall>opid'a. (opid'a ;po^(proc_of_op opid pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"   
      using f1 f4 by auto
    then have f7: "\<forall>opid'a. (opid'a ;po^(proc_of_op opid' pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"
      using a1 unfolding valid_mem_exe_seq_def valid_program_def valid_mem_exe_seq_final_def
      using f1 by force
    show False 
    proof (cases "type_of_mem_op_block (pbm opid')")
      case ld_block             
      then show ?thesis 
        using mem_op_elim_load_op[OF f5 ld_block] f6
        by (metis (full_types))                     
    next
      case st_block 
      then show ?thesis 
        using mem_op_elim_store_op[OF f5 st_block] f7
        by (metis (full_types))
    next
      case ald_block
      then show ?thesis 
        using mem_op_elim_atom_load_op[OF f5 ald_block] f7
        by (metis (full_types))
    next
      case ast_block
      then show ?thesis 
        using mem_op_elim_atom_store_op[OF f5 ast_block] f7
        by (metis (full_types))
    next
      case o_block
      then show ?thesis 
        using mem_op_elim_o_op[OF f5 o_block] f7
        by (metis (full_types))
    qed
  qed  
qed  

text {* The lemma below shows that the StoreStore axiom is satisfied in every valid
sequence of executions in the operational TSO model. *}   
  
lemma axiom_storestore_sat: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow> 
  axiom_storestore opid opid' po (fst (List.last exe_list)) pbm"
proof -
  assume a1: "valid_mem_exe_seq_final po pbm exe_list"
  show "axiom_storestore opid opid' po (fst (List.last exe_list)) pbm"
  proof (rule ccontr)
    assume a2: "\<not>(axiom_storestore opid opid' po (fst (List.last exe_list)) pbm)"
    then obtain p where f1: "((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
      (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
      ((p = proc_of_op opid pbm) \<and> (opid ;po^p opid'))) \<and>
     \<not> ((opid m<(fst (List.last exe_list)) opid') = Some True)"
      unfolding axiom_storestore_def
      by auto
    from a1 f1 have f2: "(opid' m<(fst (List.last exe_list)) opid) = Some True"
      using prog_order_op_exe2 by blast
    from a1 f1 have f3: "List.member (fst (List.last exe_list)) opid \<and> 
      List.member (fst (List.last exe_list)) opid' \<and> opid \<noteq> opid'" 
      using prog_order_op_exe prog_order_op_unique 
      valid_mem_exe_seq_def valid_mem_exe_seq_final_def by blast
    then obtain i where f4: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
           \<not> (List.member (fst (exe_list!i)) opid)"
      using f2 a1 valid_exe_op_order 
      by (metis in_set_member valid_mem_exe_seq_final_def)  
    then have f5: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"   
      by auto
    have "\<forall>opid'a. (opid'a ;po^(proc_of_op opid pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"   
      using f1 f4 by auto
    then have f7: "\<forall>opid'a. (opid'a ;po^(proc_of_op opid' pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"
      using a1 unfolding valid_mem_exe_seq_def valid_program_def valid_mem_exe_seq_final_def
      using f1 by force
    show False 
    proof (cases "type_of_mem_op_block (pbm opid')")
      case ld_block             
      then show ?thesis using f1 by auto
    next
      case st_block 
      then show ?thesis 
        using mem_op_elim_store_op[OF f5 st_block] f7
        by (metis (full_types))
    next
      case ald_block
      then show ?thesis using f1 by auto
    next
      case ast_block
      then show ?thesis 
        using mem_op_elim_atom_store_op[OF f5 ast_block] f7
        by (metis (full_types))
    next
      case o_block
      then show ?thesis using f1 by auto
    qed
  qed  
qed    
  
lemma axiom_atomicity_sub1: 
assumes a1: "valid_mem_exe_seq_final po pbm exe_list" 
and a2: "(atom_pair_id (pbm opid') = Some opid) \<and> 
   (type_of_mem_op_block (pbm opid) = ald_block) \<and>
   (type_of_mem_op_block (pbm opid') = ast_block) \<and>
   (opid ;po^(proc_of_op opid pbm) opid')" 
shows "(opid m<(fst (List.last exe_list)) opid') = Some True"  
proof (rule ccontr)
  assume a3: "\<not> ((opid m<(fst (List.last exe_list)) opid') = Some True)"
  then have f1: "(opid' m<(fst (List.last exe_list)) opid) = Some True"  
    using a1 a2 prog_order_op_exe2 by fastforce
  from a1 a2 have f2: "List.member (fst (List.last exe_list)) opid \<and> 
      List.member (fst (List.last exe_list)) opid' \<and> opid \<noteq> opid'" 
    using prog_order_op_exe prog_order_op_unique 
    valid_mem_exe_seq_def valid_mem_exe_seq_final_def by blast
  then obtain i where f3: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
           \<not> (List.member (fst (exe_list!i)) opid)"
    using f1 a1 valid_exe_op_order      
    by (metis in_set_member valid_mem_exe_seq_final_def) 
  then have f4: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
            (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"   
    by auto
  have "\<forall>opid'a. (opid'a ;po^(proc_of_op opid pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"   
    using a1 a2 f3 by auto   
  then have f5: "\<forall>opid'a. (opid'a ;po^(proc_of_op opid' pbm) opid') \<and>
         (type_of_mem_op_block (pbm opid'a) = ld_block \<or>
          type_of_mem_op_block (pbm opid'a) = ald_block \<or>
          type_of_mem_op_block (pbm opid'a) = st_block \<or> 
          type_of_mem_op_block (pbm opid'a) = ast_block) \<longrightarrow>
         List.member (fst (exe_list!i)) opid'a \<Longrightarrow> False"
    using a1 unfolding valid_mem_exe_seq_def valid_program_def valid_mem_exe_seq_final_def
    using a1 a2 by force  
  from a2 have f6: "(type_of_mem_op_block (pbm opid') = ast_block)"    
    by auto
  show False 
    using mem_op_elim_atom_store_op[OF f4 f6] f5
    by (metis (full_types))
qed  

text {* The below block of proofs show that the following operations 
do not modify the atomic flag in the state. *}  
  
lemma gen_reg_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
 atomic_flag_val (gen_reg_mod p val reg s) = r"
  unfolding atomic_flag_val_def gen_reg_mod_def
  by auto

lemma mem_op_addr_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (mem_op_addr_mod addr opid' s) = r"  
  unfolding atomic_flag_val_def mem_op_addr_mod_def
  by auto
    
lemma mem_op_val_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (mem_op_val_mod addr opid' s) = r"     
  unfolding atomic_flag_val_def mem_op_val_mod_def
  by auto    

lemma annul_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (annul_mod p b s) = r"         
  unfolding annul_mod_def atomic_flag_val_def by auto
  
lemma ctl_reg_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (ctl_reg_mod p val reg s) = r"         
  unfolding ctl_reg_mod_def atomic_flag_val_def by auto    
    
lemma next_proc_op_pos_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (next_proc_op_pos_mod p pos s) = r"         
  unfolding next_proc_op_pos_mod_def atomic_flag_val_def by auto      
    
lemma mem_mod_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (mem_mod v a s) = r"        
 unfolding mem_mod_def atomic_flag_val_def by auto
    
lemma mem_commit_atomic_flag: "atomic_flag_val s = r \<Longrightarrow>
  atomic_flag_val (mem_commit opid s) = r"         
  unfolding mem_commit_def  
  using mem_mod_atomic_flag 
  apply auto     
  apply (simp add: Let_def)
  apply (cases "op_addr (get_mem_op_state opid s)")
   apply auto
  apply (cases "op_val (get_mem_op_state opid s)")
  by auto         
    
lemma atomic_flag_mod_none: "atomic_flag_val (atomic_flag_mod None s) = None"
  unfolding atomic_flag_mod_def atomic_flag_val_def by auto
    
lemma atomic_flag_mod_some: "atomic_flag_val (atomic_flag_mod (Some opid) s) = Some opid"
  unfolding atomic_flag_mod_def atomic_flag_val_def by auto    
    
lemma load_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (load_instr p instr opid' a v s) = r"   
  using a1 unfolding load_instr_def Let_def atomic_flag_val_def    
  apply auto  
  apply (cases "a")
   apply auto
  apply (cases "v")
   apply auto
  using gen_reg_mod_atomic_flag mem_op_addr_mod_atomic_flag
   mem_op_val_mod_atomic_flag   
   apply ( simp add: atomic_flag_val_def)     
  using mem_op_addr_mod_atomic_flag mem_op_val_mod_atomic_flag
  by (simp add: atomic_flag_val_def)                   
  
lemma store_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (store_instr p instr opid' s) = r"    
  using a1 unfolding store_instr_def Let_def atomic_flag_val_def    
  using mem_op_addr_mod_atomic_flag mem_op_val_mod_atomic_flag    
  by (simp add: atomic_flag_val_def)       

lemma sethi_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (sethi_instr p instr s) = r"     
  using a1 unfolding sethi_instr_def Let_def atomic_flag_val_def
  apply (cases "get_operand_w5 (snd instr ! 1) \<noteq> 0")
   apply auto
  using gen_reg_mod_atomic_flag 
  by (simp add: atomic_flag_val_def)

lemma nop_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (nop_instr p instr s) = r" 
  using a1 unfolding nop_instr_def by auto
  
lemma logical_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (logical_instr p instr s) = r" 
  using a1 unfolding logical_instr_def Let_def 
  apply (cases "fst instr \<in> {logic_type ANDcc, logic_type ANDNcc, logic_type ORcc, 
               logic_type ORNcc, logic_type XORcc, logic_type XNORcc}")
   apply clarsimp    
   apply (cases "get_operand_w5 (snd instr ! 3) \<noteq> 0")    
    apply clarsimp
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag 
    apply auto[1] 
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag     
   apply auto[1]
  apply auto
  using atomic_flag_val_def gen_reg_mod_atomic_flag 
  by auto    

lemma shift_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (shift_instr p instr s) = r"     
  using a1 unfolding shift_instr_def Let_def 
  apply auto  
  using atomic_flag_val_def gen_reg_mod_atomic_flag by auto
    
lemma add_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (add_instr p instr s) = r"       
  using a1 unfolding add_instr_def Let_def
  apply auto
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag by auto

lemma sub_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (sub_instr p instr s) = r"       
  using a1 unfolding sub_instr_def Let_def
  apply auto
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag by auto    

lemma mul_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (mul_instr p instr s) = r"       
  using a1 unfolding mul_instr_def Let_def
  apply auto
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag by auto     
  
lemma div_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (div_instr p instr s) = r"       
  using a1 unfolding div_instr_def Let_def
  apply auto
  using atomic_flag_val_def apply auto
  unfolding div_comp_def apply auto
  apply (cases "get_operand_w5 (snd instr ! 3) \<noteq> 0")
   apply auto
  unfolding Let_def  
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag by auto
  
lemma jmpl_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (jmpl_instr p instr s) = r" 
  using a1 unfolding jmpl_instr_def Let_def
  apply auto
  using ctl_reg_mod_atomic_flag atomic_flag_val_def gen_reg_mod_atomic_flag by auto

lemma branch_instr_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (branch_instr p instr s) = r"  
  using a1 unfolding branch_instr_def Let_def
  apply auto
  using ctl_reg_mod_atomic_flag atomic_flag_val_def 
  gen_reg_mod_atomic_flag annul_mod_atomic_flag
         by auto
    
lemma swap_load_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (swap_load p instr opid' a v s) = r"     
  using a1 unfolding swap_load_def Let_def atomic_flag_val_def    
  apply auto  
  apply (cases "a")
   apply auto
  apply (cases "v")
   apply auto
  using gen_reg_mod_atomic_flag mem_op_addr_mod_atomic_flag
   mem_op_val_mod_atomic_flag atomic_rd_mod_def
   apply ( simp add: atomic_flag_val_def)     
  using mem_op_addr_mod_atomic_flag mem_op_val_mod_atomic_flag atomic_rd_mod_def
  by (simp add: atomic_flag_val_def)                     
  
lemma swap_store_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (swap_store p instr opid' s) = r"     
  using a1 unfolding swap_store_def Let_def atomic_flag_val_def    
  using mem_op_addr_mod_atomic_flag mem_op_val_mod_atomic_flag atomic_rd_val_def
  by (simp add: atomic_flag_val_def)       
    
lemma casa_load_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (casa_load p instr opid' a v s) = r"     
  using a1 unfolding casa_load_def Let_def
  apply auto  
  apply (cases "a")
   apply (simp add: atomic_flag_val_def)      
  apply (cases "v")    
   apply (simp add: atomic_flag_val_def)  
  using gen_reg_mod_atomic_flag mem_op_addr_mod_atomic_flag    
   mem_op_val_mod_atomic_flag gen_reg_val_def atomic_rd_mod_def
  by (simp add: atomic_flag_val_def)         
   
lemma casa_store_atomic_flag:
assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (casa_store p instr opid' s) = r"     
proof (cases "(atomic_flag_val s)")
  case None
  then show ?thesis 
    using a1 unfolding casa_store_def Let_def
    apply auto
    by (simp add: atomic_flag_val_def)
next
  case (Some a)
  then have f1: "atomic_flag_val s = Some a"
    by auto
  then show ?thesis 
  proof (cases "op_val (mem_ops s a)")
    case None
    then show ?thesis 
      using a1 unfolding casa_store_def Let_def
      apply auto        
      using Some None
      by (simp add: atomic_flag_val_def)
  next
    case (Some a)
    then show ?thesis 
      using a1 unfolding casa_store_def Let_def
      apply auto
      using f1 Some mem_op_addr_mod_atomic_flag mem_op_val_mod_atomic_flag
      by (simp add: atomic_flag_val_def )
  qed    
qed
    
lemma proc_exe_atomic_flag:
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (proc_exe p instr opid' a v s) = r"   
  using a1 unfolding proc_exe_def Let_def
  apply (cases "fst instr \<in> {load_store_type LD}")
   apply (simp add: load_instr_atomic_flag)
  apply (cases "fst instr \<in> {load_store_type ST}")
   apply (simp add: store_instr_atomic_flag)
  apply (cases "fst instr \<in> {sethi_type SETHI}")
   apply (simp add: sethi_instr_atomic_flag)
  apply (cases "fst instr \<in> {nop_type NOP}")
   apply (simp add: nop_instr_atomic_flag) 
  apply (cases "fst instr \<in> {logic_type ANDs, logic_type ANDcc, logic_type ANDN,
                             logic_type ANDNcc, logic_type ORs, logic_type ORcc, logic_type ORN,
                             logic_type XORs, logic_type XNOR}")
   apply (simp add: logical_instr_atomic_flag) 
  apply (cases "fst instr \<in> {shift_type SLL, shift_type SRL, shift_type SRA}")
   apply (simp add: shift_instr_atomic_flag) 
  apply (cases "fst instr \<in> {arith_type ADD, arith_type ADDcc, arith_type ADDX}")
   apply (simp add: add_instr_atomic_flag) 
  apply (cases "fst instr \<in> {arith_type SUB, arith_type SUBcc, arith_type SUBX}")
   apply (simp add: sub_instr_atomic_flag) 
  apply (cases "fst instr \<in> {arith_type UMUL, arith_type SMUL, arith_type SMULcc}")
   apply (simp add: mul_instr_atomic_flag) 
  apply (cases "fst instr \<in> {arith_type UDIV, arith_type UDIVcc, arith_type SDIV}")
   apply (simp add: div_instr_atomic_flag)
  apply (cases "fst instr \<in> {ctrl_type JMPL}")
   apply (simp add: jmpl_instr_atomic_flag)
  apply (cases "fst instr \<in> {bicc_type BE, bicc_type BNE, bicc_type BGU, bicc_type BLE, bicc_type BL,
                 bicc_type BGE, bicc_type BNEG, bicc_type BG, bicc_type BCS, bicc_type BLEU,
                 bicc_type BCC, bicc_type BA, bicc_type BN}")
   apply (simp add: branch_instr_atomic_flag) 
  apply (cases "fst instr \<in> {load_store_type SWAP_LD}")
   apply (simp add: swap_load_atomic_flag)
  apply (cases "fst instr \<in> {load_store_type SWAP_ST}")
   apply (simp add: swap_store_atomic_flag)
  apply (cases "fst instr \<in> {load_store_type CASA_LD}")
   apply (simp add: casa_load_atomic_flag)
  apply (cases "fst instr \<in> {load_store_type CASA_ST}")
   apply (simp add: casa_store_atomic_flag)
  by auto
  
lemma seq_proc_exe_atomic_flag:
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (seq_proc_exe p l opid' a v s) = r"    
proof (insert assms, induction l arbitrary: s)
  case Nil
  then show ?case 
    unfolding seq_proc_exe.simps using a1 by auto
next
  case (Cons a l)
  then show ?case 
    unfolding seq_proc_exe.simps using a1 proc_exe_atomic_flag by auto
qed  
  
lemma seq_proc_blk_exe_atomic_flag:
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (seq_proc_blk_exe p po pbm n a v s) = r"   
proof (insert assms, induction n arbitrary: "(s::sparc_state)")
  case 0
  then show ?case 
    unfolding seq_proc_blk_exe.simps by auto      
next
  case (Suc n)
  then show ?case 
    unfolding seq_proc_blk_exe.simps Let_def
    apply (cases "proc_exe_pos s p < length (po p)")
     prefer 2
     apply auto[1]           
    apply clarsimp      
    using next_proc_op_pos_mod_atomic_flag seq_proc_exe_atomic_flag 
    by auto  
qed
  
lemma proc_exe_to_atomic_flag: 
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (proc_exe_to p po pbm pos s) = r"
  unfolding proc_exe_to_def Let_def 
  using a1 seq_proc_blk_exe_atomic_flag by auto
  
lemma seq_proc_blk_exe_except_last_atomic_flag:
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (seq_proc_blk_exe_except_last p po pbm n a v s) = r"   
proof (insert assms, induction n arbitrary: "(s::sparc_state)")
  case 0
  then show ?case 
    unfolding seq_proc_blk_exe.simps by auto      
next
  case (Suc n)
  then show ?case 
    unfolding seq_proc_blk_exe.simps Let_def
    apply (cases "proc_exe_pos s p < length (po p)")
     prefer 2
     apply auto[1]           
    apply clarsimp      
    apply (cases "n = 0")
    apply (simp add: Let_def)
    using next_proc_op_pos_mod_atomic_flag seq_proc_exe_atomic_flag 
     apply auto
    apply (simp add: Let_def)
     using next_proc_op_pos_mod_atomic_flag seq_proc_exe_atomic_flag
     using seq_proc_blk_exe_atomic_flag by auto            
qed    
    
lemma proc_exe_to_previous_atomic_flag: 
  assumes a1: "atomic_flag_val s = r"
shows "atomic_flag_val (proc_exe_to_previous p po pbm pos s) = r"
  unfolding proc_exe_to_previous_def Let_def 
  using seq_proc_blk_exe_except_last_atomic_flag[OF a1] by auto    
    
lemma proc_exe_to_last_atomic_flag: 
  assumes a1: "atomic_flag_val s = r"
  shows "atomic_flag_val (proc_exe_to_last p po pbm pos v a s) = r"    
  unfolding proc_exe_to_last_def
  using a1 apply auto
  apply (simp add: Let_def)
  using next_proc_op_pos_mod_atomic_flag proc_exe_atomic_flag
  by auto
    
text {* The above finishes the proof that atomic_flag is not modified in 
 processor_execution. *}    
    
lemma ast_op_unique:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "opid' \<noteq> opid"
  and a3: "atom_pair_id (pbm opid) = Some opid''"
shows "atom_pair_id (pbm opid') \<noteq> Some opid''"     
  using a1 unfolding valid_mem_exe_seq_def valid_program_def
  using a2 a3 by blast  

lemma atomic_flag_exe_ld:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
  and a3: "type_of_mem_op_block (pbm opid) = ld_block"
shows "atomic_flag_val s' = None"  
proof -
  from a1 a3 have "s' = proc_exe_to_last (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) 
          opid (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
         po xseq pbm (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))
         (Some (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
         (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)"
    using mem_op_elim_load_op by metis
  then show ?thesis using a2 proc_exe_to_atomic_flag 
    proc_exe_to_previous_atomic_flag proc_exe_to_last_atomic_flag by auto
qed  
  
lemma atomic_flag_exe_st:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
  and a3: "type_of_mem_op_block (pbm opid) = st_block"
shows "atomic_flag_val s' = None"  
proof -
  from a1 a3 have "s' = mem_commit opid (proc_exe_to (proc_of_op opid pbm) po pbm 
     (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)"
    using mem_op_elim_store_op by metis
  then show ?thesis using a2 proc_exe_to_atomic_flag mem_commit_atomic_flag by auto  
qed

lemma atomic_flag_exe_ald:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
  and a3: "type_of_mem_op_block (pbm opid) = ald_block"
shows "atomic_flag_val s' = Some opid"  
proof -
  from a1 a3 have "s' = atomic_flag_mod (Some opid) (proc_exe_to_last (proc_of_op opid pbm) po pbm 
          (non_repeat_list_pos opid (po (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) 
           opid (atomic_load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
          po xseq pbm (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))
           (Some (atomic_load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
           (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))"
    using mem_op_elim_atom_load_op by metis
  then show ?thesis
    using atomic_flag_mod_some by auto
qed  
  
lemma atomic_flag_exe_ast:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
shows "type_of_mem_op_block (pbm opid) \<noteq> ast_block"
proof (rule ccontr)
  assume "\<not> type_of_mem_op_block (pbm opid) \<noteq> ast_block"
  then have "type_of_mem_op_block (pbm opid) = ast_block"
    by auto
  then have "(\<exists>opid'. atomic_flag_val s = Some opid')"
    using a1 mem_op_elim_atom_store_op by metis      
  then show False using a2 by auto
qed  
  
lemma atomic_flag_exe_o:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
  and a3: "type_of_mem_op_block (pbm opid) = o_block"
shows "atomic_flag_val s' = None"  
proof -
  from a1 a3 have "s' = proc_exe_to (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
    (proc_of_op opid pbm))) s"
    using mem_op_elim_o_op by metis
  then show ?thesis using a2 proc_exe_to_atomic_flag by auto  
qed      
    
lemma atomic_flag_exe1:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = Some opid'"
shows "type_of_mem_op_block (pbm opid) = ld_block \<or> 
       type_of_mem_op_block (pbm opid) = o_block \<or>
       (type_of_mem_op_block (pbm opid) = ast_block \<and>
        atom_pair_id (pbm opid) = Some opid')" 
proof (rule ccontr)
  assume a3: "\<not> (type_of_mem_op_block (pbm opid) = ld_block \<or>
        type_of_mem_op_block (pbm opid) = o_block \<or>
        type_of_mem_op_block (pbm opid) = ast_block \<and> atom_pair_id (pbm opid) = Some opid')"
  then have "\<not> (type_of_mem_op_block (pbm opid) = ld_block) \<and>
             \<not> (type_of_mem_op_block (pbm opid) = o_block) \<and>
             (\<not> (type_of_mem_op_block (pbm opid) = ast_block) \<or> 
              atom_pair_id (pbm opid) \<noteq> Some opid')"
    by auto
  then have f1: "(type_of_mem_op_block (pbm opid) = st_block) \<or>
             (type_of_mem_op_block (pbm opid) = ald_block) \<or>
             (type_of_mem_op_block (pbm opid) = ast_block \<and> 
              atom_pair_id (pbm opid) \<noteq> Some opid')"
    using mem_op_block_type.exhaust by blast    
  show False 
  proof (rule disjE[OF f1])
    assume a4: "type_of_mem_op_block (pbm opid) = st_block"    
    from a2 have "atomic_flag_val s = None \<Longrightarrow> False"
      by auto    
    then show False
      using a1 a4 mem_op_elim_store_op by fastforce
  next
    assume a5: "type_of_mem_op_block (pbm opid) = ald_block \<or>
      (type_of_mem_op_block (pbm opid) = ast_block \<and> 
       atom_pair_id (pbm opid) \<noteq> Some opid')"
    show False
    proof (rule disjE[OF a5])
      assume a6: "type_of_mem_op_block (pbm opid) = ald_block"
      from a2 have "atomic_flag_val s = None \<Longrightarrow> False"
      by auto    
      then show False
      using a1 a6 mem_op_elim_atom_load_op by fastforce
    next
      assume a7: "type_of_mem_op_block (pbm opid) = ast_block \<and> 
                  atom_pair_id (pbm opid) \<noteq> Some opid'"
      then have "\<And>opid'. atomic_flag_val s = Some opid' \<Longrightarrow>
          atom_pair_id (pbm opid) = Some opid' \<Longrightarrow> False"
        using a2 by auto      
      then show False 
        using a1 a7 mem_op_elim_atom_store_op by metis
    qed
  qed  
qed  
  
lemma atomic_flag_exe2:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = Some opid'"
  and a3: "type_of_mem_op_block (pbm opid) = ld_block \<or> 
           type_of_mem_op_block (pbm opid) = o_block"
shows "atomic_flag_val s' = Some opid'"   
proof -
  from a1 a3 have f1: "(\<exists>vop. s' = proc_exe_to_last (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) vop
         (Some (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
         (proc_exe_to_previous (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) \<or>
      (s' = proc_exe_to (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
    (proc_of_op opid pbm))) s)"
    using mem_op_elim_load_op mem_op_elim_o_op
    by meson       
  then show ?thesis 
    apply (rule disjE)
    using proc_exe_to_atomic_flag proc_exe_to_previous_atomic_flag 
    proc_exe_to_last_atomic_flag a2 by auto                 
qed  
  
lemma atomic_flag_exe3:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = Some opid'"
  and a3: "(type_of_mem_op_block (pbm opid) = ast_block \<and>
        atom_pair_id (pbm opid) = Some opid')"
shows "atomic_flag_val s' = None"
proof -
  from a1 a3 have f1: "s' = mem_commit opid (atomic_flag_mod None (proc_exe_to (proc_of_op opid pbm) 
            po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))"
    using mem_op_elim_atom_store_op by metis
  then have "s' = mem_commit opid (atomic_flag_mod None (proc_exe_to (proc_of_op opid pbm) 
            po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))"  
    using a3 by auto    
  then show ?thesis using atomic_flag_mod_none mem_commit_atomic_flag 
    by auto
qed  
  
lemma atomic_flag_exe4:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s = None"
  and a3: "atomic_flag_val s' = Some opid'"
shows "type_of_mem_op_block (pbm opid) = ald_block"
proof (rule ccontr)
  assume a4: "type_of_mem_op_block (pbm opid) \<noteq> ald_block"
  then have "type_of_mem_op_block (pbm opid) = ld_block \<or>
             type_of_mem_op_block (pbm opid) = st_block \<or>
             type_of_mem_op_block (pbm opid) = ast_block \<or>
             type_of_mem_op_block (pbm opid) = o_block"
    using mem_op_block_type.exhaust by blast    
  then show False 
  proof (auto)
    assume a5: "type_of_mem_op_block (pbm opid) = ld_block"  
    then have "atomic_flag_val s' = None"
      using a1 a2 atomic_flag_exe_ld by auto
    then show False using a3 by auto
  next
    assume a6: "type_of_mem_op_block (pbm opid) = st_block"
    then have "atomic_flag_val s' = None"
      using a1 a2 atomic_flag_exe_st by auto  
    then show False using a3 by auto
  next 
    assume a7: "type_of_mem_op_block (pbm opid) = ast_block"
    then show False using a1 a2 atomic_flag_exe_ast by auto
  next 
    assume a8: "type_of_mem_op_block (pbm opid) = o_block"
    then have "atomic_flag_val s' = None"
      using a1 a2 atomic_flag_exe_o by auto
    then show False using a3 by auto
  qed  
qed  
  
lemma atomic_flag_exe5:
  assumes a1: "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'"
  and a2: "atomic_flag_val s \<noteq> Some opid'"
  and a3: "opid \<noteq> opid'"
shows "atomic_flag_val s' \<noteq> Some opid'"
proof -
  from a2 have f1: "atomic_flag_val s = None \<or> 
    (\<exists>opid''. atomic_flag_val s = Some opid'' \<and> opid'' \<noteq> opid')"
    using option.collapse by fastforce    
  then show ?thesis 
  proof (rule disjE)
    assume a4: "atomic_flag_val s = None"    
    show ?thesis 
    proof (cases "type_of_mem_op_block (pbm opid)")
      case ld_block
      then have "atomic_flag_val s' = None"
        using atomic_flag_exe_ld[OF a1 a4 ld_block] by auto
      then show ?thesis by auto
    next
      case st_block
      then have "atomic_flag_val s' = None"
        using atomic_flag_exe_st[OF a1 a4 st_block] by auto
      then show ?thesis by auto
    next
      case ald_block
      then have "atomic_flag_val s' = Some opid"
        using atomic_flag_exe_ald[OF a1 a4 ald_block] by auto
      then show ?thesis using a3 by auto
    next
      case ast_block
      then show ?thesis using atomic_flag_exe_ast[OF a1 a4] by auto
    next
      case o_block
      then have "atomic_flag_val s' = None"
        using atomic_flag_exe_o[OF a1 a4 o_block] by auto
      then show ?thesis by auto
    qed
  next
    assume a5: "\<exists>opid''. atomic_flag_val s = Some opid'' \<and> opid'' \<noteq> opid'"
    then obtain opid'' where f2: "atomic_flag_val s = Some opid'' \<and> opid'' \<noteq> opid'"
      by auto
    then have "(type_of_mem_op_block (pbm opid) = ld_block \<or>
      type_of_mem_op_block (pbm opid) = o_block) \<or>
      (type_of_mem_op_block (pbm opid) = ast_block \<and> 
       atom_pair_id (pbm opid) = Some opid'')"
      using atomic_flag_exe1 a1 by auto
    then show ?thesis
    proof (rule disjE)
      assume a6: "type_of_mem_op_block (pbm opid) = ld_block \<or> 
        type_of_mem_op_block (pbm opid) = o_block"
      then show ?thesis using atomic_flag_exe2[OF a1] f2 by auto
    next
      assume a7: "type_of_mem_op_block (pbm opid) = ast_block \<and> 
        atom_pair_id (pbm opid) = Some opid''"
      then show ?thesis using atomic_flag_exe3[OF a1] f2 by auto
    qed  
  qed  
qed  
  
lemma atom_exe_valid_type1: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list - 1) \<and> k < (List.length exe_list - 1) \<and> i < k"
  and a3: "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
  and a4: "(po pbm opid' \<turnstile>m (fst (exe_list!k)) (snd (snd (exe_list!k))) \<rightarrow>
             (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1)))))"
  and a5: "(atom_pair_id (pbm opid') = Some opid) \<and> 
           (type_of_mem_op_block (pbm opid) = ald_block) \<and>
           (type_of_mem_op_block (pbm opid') = ast_block)"
  and a6: "(i < j \<and> j < k \<and> (po pbm opid'' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))))"
  and a7: "atomic_flag_val (snd (snd (exe_list!(i+1)))) = Some opid"
  and a8: "opid \<noteq> opid'' \<and> opid'' \<noteq> opid'"
  shows "(type_of_mem_op_block (pbm opid'') = ld_block \<or> 
          type_of_mem_op_block (pbm opid'') = o_block) \<and>
         atomic_flag_val (snd (snd (exe_list!j))) = Some opid"
proof (insert assms, induction "j - i" arbitrary: opid'' j)
  case 0
  then show ?case by auto 
next
  case (Suc x)
  then show ?case 
  proof (cases "j - 1 = i")
    case True
    then have "j = i + 1"
      using Suc.prems(6) by linarith 
    then have f1: "atomic_flag_val (snd (snd (exe_list!j))) = Some opid"
      using a7 by auto 
    then have f2: "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block \<or>
       (type_of_mem_op_block (pbm opid'') = ast_block \<and>
        atom_pair_id (pbm opid'') = Some opid)"
      using Suc(8) atomic_flag_exe1 by blast
    from a1 Suc(10) Suc(7) have "atom_pair_id (pbm opid'') \<noteq> Some opid"
      using ast_op_unique by auto
    then have "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block"
      using f2 by auto
    then show ?thesis using f1 by auto
  next
    case False
    then have f3: "j-1 > i"
      using Suc(8) by auto 
    then have f003: "j > 0"
      by auto    
    from Suc(2) have f03: "x = (j-1) - i"  
      by auto
    from Suc(4) Suc(8) have f4: "j-1 < length exe_list - 1"
      by auto
    then obtain opid''' where 
      "(po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! j)) (snd (snd (exe_list ! j))))"          
      using a1 unfolding valid_mem_exe_seq_def mem_state_trans_def
      by (metis (no_types, lifting) add.commute add_diff_inverse_nat f3 gr_implies_not_zero nat_diff_split_asm)
    then have f05: "(po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! ((j-1)+1))) (snd (snd (exe_list ! ((j-1)+1)))))"
      using f003 by auto
    then have f5: "i < j-1 \<and> j-1 < k \<and>
      (po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! ((j-1)+1))) (snd (snd (exe_list ! ((j-1)+1)))))"
      using f3 Suc(8) f003 by auto
    from a1 f4 Suc(4) f5 Suc(5) have f6: "opid''' \<noteq> opid"
      using valid_exe_op_exe_pos_unique False
      by (metis One_nat_def Suc_eq_plus1) 
    from a1 f4 Suc(4) f5 Suc(6) Suc(8) have f7: "opid''' \<noteq> opid'"
      using valid_exe_op_exe_pos_unique
      by (metis One_nat_def not_le order_less_imp_le) 
    from f6 f7 have f8: "opid \<noteq> opid''' \<and> opid''' \<noteq> opid'"
      by auto
    have f9: "(type_of_mem_op_block (pbm opid''') = ld_block \<or> 
               type_of_mem_op_block (pbm opid''') = o_block) \<and>
              atomic_flag_val (snd (snd (exe_list ! (j-1)))) = Some opid"
      using Suc(1)[OF f03 a1 Suc(4) Suc(5) Suc(6) Suc(7) f5 Suc(9) f8] by auto
    then have "atomic_flag_val (snd (snd (exe_list ! ((j-1)+1)))) = Some opid"
      using atomic_flag_exe2 f05 by auto
    then have f10: "atomic_flag_val (snd (snd (exe_list ! j))) = Some opid"
      using f003 by auto
    from Suc(8) have f11: "po pbm opid'' \<turnstile>m (fst (exe_list ! j)) (snd (snd (exe_list ! j))) \<rightarrow>
                    (fst (exe_list ! (j + 1))) (snd (snd (exe_list ! (j + 1))))"
      by auto
    have f12: "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block \<or>
       (type_of_mem_op_block (pbm opid'') = ast_block \<and>
        atom_pair_id (pbm opid'') = Some opid)"
      using atomic_flag_exe1[OF f11 f10] by auto
    have f13: "atom_pair_id (pbm opid'') \<noteq> Some opid"
      using ast_op_unique[OF a1] Suc(10) Suc(7) by auto
    from f12 f13 show ?thesis
      by (simp add: f10) 
  qed    
qed
  
lemma axiom_atomicity_sub2: 
assumes a1: "valid_mem_exe_seq_final po pbm exe_list" 
and a2: "(atom_pair_id (pbm opid') = Some opid) \<and> 
   (type_of_mem_op_block (pbm opid) = ald_block) \<and>
   (type_of_mem_op_block (pbm opid') = ast_block) \<and>
   (opid ;po^(proc_of_op opid pbm) opid')" 
and a3: "(opid m<(fst (List.last exe_list)) opid') = Some True"   
shows "(\<forall>opid''. ((type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
                 List.member (fst (List.last exe_list)) opid'' \<and>
                 opid'' \<noteq> opid') \<longrightarrow>
       ((opid'' m<(fst (List.last exe_list)) opid) = Some True \<or> 
        (opid' m<(fst (List.last exe_list)) opid'') = Some True))"
proof (rule ccontr)
  assume a4: "\<not> (\<forall>opid''. ((type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
                 List.member (fst (List.last exe_list)) opid'' \<and>
                 opid'' \<noteq> opid') \<longrightarrow>
       ((opid'' m<(fst (List.last exe_list)) opid) = Some True \<or> 
        (opid' m<(fst (List.last exe_list)) opid'') = Some True))"
  then obtain opid'' where f1: "(type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
                 List.member (fst (List.last exe_list)) opid'' \<and>
                 opid'' \<noteq> opid' \<and>
       \<not> ((opid'' m<(fst (List.last exe_list)) opid) = Some True \<or> 
          (opid' m<(fst (List.last exe_list)) opid'') = Some True)"
    by auto
  from a2 f1 have f2: "opid'' \<noteq> opid"
    by auto
  from a2 have f3: "List.member (fst (List.last exe_list)) opid \<and> 
       List.member (fst (List.last exe_list)) opid'"
    using a1 prog_order_op_exe by auto
  from f1 f2 f3 a1 have f4: "((opid m<(fst (List.last exe_list)) opid'') = Some True \<or> 
        (opid'' m<(fst (List.last exe_list)) opid) = Some True)"
    using valid_exe_op_order2 by blast 
  from f1 f3 a1 have f5: "((opid' m<(fst (List.last exe_list)) opid'') = Some True \<or> 
        (opid'' m<(fst (List.last exe_list)) opid') = Some True)"    
    using valid_exe_op_order2 by blast 
  from f4 f5 f1 have f6: "(type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
                 List.member (fst (List.last exe_list)) opid'' \<and>
                 opid'' \<noteq> opid' \<and>
       (opid m<(fst (List.last exe_list)) opid'') = Some True \<and> 
       (opid'' m<(fst (List.last exe_list)) opid') = Some True"    
    by auto
  from a1 a4 f3 have f7: "opid \<in> fst (snd (List.hd exe_list)) \<and>
                       opid' \<in> fst (snd (List.hd exe_list)) \<and>
                       opid'' \<in> fst (snd (List.hd exe_list))"
    unfolding valid_mem_exe_seq_def valid_mem_exe_seq_final_def
    by (simp add: f1 in_set_member)
  from a1 f6 f7 f2 obtain i j k where f8: "(i < (List.length exe_list - 1)) \<and>
            (j < (List.length exe_list - 1)) \<and>
            (k < (List.length exe_list - 1)) \<and>
            (po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1))))) \<and> 
            (po pbm opid'' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))) \<and>
            (po pbm opid' \<turnstile>m (fst (exe_list!k)) (snd (snd (exe_list!k))) \<rightarrow>
             (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1))))) \<and>
            i < j \<and> j < k"    
    using valid_exe_op_order_3ops by blast
  from a1 a2 f8 have f9: "atomic_flag (glob_var (snd (snd (exe_list!(i+1))))) = Some opid"
    using mem_op_atom_load_op_atomic_flag by auto      
  from f8 have f10: "i < length exe_list - 1 \<and> k < length exe_list - 1 \<and> i < k"
    by auto
  from f8 have f11: "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
    by auto
  from f8 have f12: "(po pbm opid'' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"
    by auto
  from f8 have f13: "(po pbm opid' \<turnstile>m (fst (exe_list!k)) (snd (snd (exe_list!k))) \<rightarrow>
             (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1)))))"
    by auto
  from a2 have f14: "atom_pair_id (pbm opid') = Some opid \<and>
    type_of_mem_op_block (pbm opid) = ald_block \<and> type_of_mem_op_block (pbm opid') = ast_block"
    by auto
  from f8 have f15: "i < j \<and> j < k \<and>
    (po pbm opid'' \<turnstile>m (fst (exe_list ! j)) (snd (snd (exe_list ! j))) \<rightarrow>
                     (fst (exe_list ! (j + 1))) (snd (snd (exe_list ! (j + 1)))))"
    by auto
  from f9 have f16: "atomic_flag_val (snd (snd (exe_list ! (i + 1)))) = Some opid "
    unfolding atomic_flag_val_def by auto
  from f2 f6 have f17: "opid \<noteq> opid'' \<and> opid'' \<noteq> opid'"
    by auto
  from a1 have a1f: "valid_mem_exe_seq po pbm exe_list"
    unfolding valid_mem_exe_seq_final_def by auto
  have "(type_of_mem_op_block (pbm opid'') = ld_block \<or> 
          type_of_mem_op_block (pbm opid'') = o_block)"
    using atom_exe_valid_type1[OF a1f f10 f11 f13 f14 f15 f16 f17] by auto  
  then show False 
    using f1 by force
qed  

text {* The lemma below shows that the Atomicity axiom is satisfied in every valid
sequence of executions in the operational TSO model. *}   
  
lemma axiom_atomicity_sat: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow>
axiom_atomicity opid opid' po (fst (List.last exe_list)) pbm"
  unfolding axiom_atomicity_def
  using axiom_atomicity_sub1 axiom_atomicity_sub2
  by auto
    
text {* The theorem below gives the soundness proof. 
Note that it does not concern the axiom Value, because it is directly incorporated 
in the operational TSO model, and it's trivially true. *}
  
theorem operational_model_sound: "valid_mem_exe_seq_final po pbm exe_list \<Longrightarrow>
  (\<forall>opid opid'. axiom_order opid opid' (fst (List.last exe_list)) pbm) \<and>
  (\<forall>opid. axiom_termination opid po (fst (List.last exe_list)) pbm) \<and>
  (\<forall>opid opid'. axiom_loadop opid opid' po (fst (List.last exe_list)) pbm) \<and>
  (\<forall>opid opid'. axiom_storestore opid opid' po (fst (List.last exe_list)) pbm) \<and>
  (\<forall>opid opid'. axiom_atomicity opid opid' po (fst (List.last exe_list)) pbm)"
  using axiom_order_sat axiom_termination_sat axiom_loadop_sat 
  axiom_storestore_sat axiom_atomicity_sat by auto
    
subsection {* Completeness of the operational TSO model *}  
  
text {* This subsection shows that if a sequence of memory operations satisfies the TSO axioms,
then there exists an execution for it in the operational TSO model. 

N.B. We are only concerned with memory operations in this proof. The order to o_blocks 
are uninteresting here. We shall just assume that the o_block of a processor is executed
after the last memory operation, which is consistent with the rule o_op. 
But we will not discuss it in the proof. *}  
  
text {* The following are the conditions that a complete sequence of memory operations
must satisfy. *}

definition op_seq_final:: "op_id list \<Rightarrow> program_order \<Rightarrow> program_block_map \<Rightarrow> bool" where
"op_seq_final op_seq po pbm \<equiv> valid_program po pbm \<and>
   List.length op_seq > 0 \<and> (\<forall>opid. (\<exists>p. List.member (po p) opid) = (List.member op_seq opid)) \<and>
   non_repeat_list op_seq \<and> (\<forall>opid. (\<exists>p. List.member (po p) opid) \<longrightarrow> 
   (type_of_mem_op_block (pbm opid) \<in> {ld_block, st_block, ald_block, ast_block}))"

text {* First we show the conditions that falsify each "inference rule" in 
the operational model.  *}
  
lemma load_op_contra: 
  assumes a1: "(type_of_mem_op_block (pbm opid) = ld_block)"  
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
  shows "\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block) \<and>
                \<not> (List.member xseq opid')"
proof (rule ccontr)
  assume a3: "\<nexists>opid'.
       (opid' ;po^(proc_of_op opid pbm) opid) \<and>
       (type_of_mem_op_block (pbm opid') = ld_block \<or>
        type_of_mem_op_block (pbm opid') = ald_block) \<and>
       \<not> List.member xseq opid'"
  then have f0: "\<forall>opid'. ((opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block)) \<longrightarrow>
                (List.member xseq opid')"
    by auto
  from mem_op.simps have f1: "(type_of_mem_op_block (pbm opid) = ld_block) \<Longrightarrow> 
    \<forall>opid'. ((opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block)) \<longrightarrow>
            (List.member xseq opid') \<Longrightarrow> 
    (po pbm opid \<turnstile>m xseq s \<rightarrow> (xseq @ [opid]) (proc_exe_to_last (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) 
          opid (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
      po xseq pbm (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))
         (Some (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))
         (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)))"
    by (metis (full_types) empty_iff insert_iff load_op)
  from a1 a2 f0 f1 have f2: "(po pbm opid \<turnstile>m xseq s \<rightarrow> (xseq @ [opid]) (proc_exe_to_last (proc_of_op opid pbm) po pbm
         (non_repeat_list_pos opid (po (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) 
          opid (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) s) po xseq pbm s)
         (Some (load_addr (proc_of_op opid pbm) (last (insts (pbm opid))) s))
         (proc_exe_to_previous (proc_of_op opid pbm) po pbm
           (non_repeat_list_pos opid (po (proc_of_op opid pbm)) - Suc 0) s)))"
    by auto
  then have "\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
    by auto
  then show False using a2 by auto 
qed  
  
lemma store_op_contra: 
  assumes a1: "(type_of_mem_op_block (pbm opid) = st_block)"  
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
shows "atomic_flag_val s \<noteq> None \<or> 
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<and>
         \<not> (List.member xseq opid'))"
proof (rule ccontr)
  assume a3: "\<not> (atomic_flag_val s \<noteq> None \<or>
        (\<exists>opid'.
            (opid' ;po^(proc_of_op opid pbm) opid) \<and>
            (type_of_mem_op_block (pbm opid') = ld_block \<or>
             type_of_mem_op_block (pbm opid') = ald_block \<or>
             type_of_mem_op_block (pbm opid') = st_block \<or>
             type_of_mem_op_block (pbm opid') = ast_block) \<and>
            \<not> List.member xseq opid'))"
  then have f0: "atomic_flag_val s = None \<and> 
                 (\<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
         List.member xseq opid')"
    by auto
  from mem_op.simps have f1: "(type_of_mem_op_block (pbm opid) = st_block) \<Longrightarrow>
    (atomic_flag_val s) = None \<Longrightarrow> \<forall>opid'. (((opid' ;po^(proc_of_op opid pbm) opid) \<and> 
    (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
    (List.member xseq opid')) \<Longrightarrow> 
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (mem_commit opid (proc_exe_to 
      (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
       s))"
    by auto
  from a1 f0 f1 have "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (mem_commit opid (proc_exe_to 
      (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po (proc_of_op opid pbm))) 
      s))"
    by auto
  then have "\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
    by auto
  then show False using a2 by auto
qed  
  
lemma atom_load_op_contra: 
  assumes a1: "(type_of_mem_op_block (pbm opid) = ald_block)"
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
shows "atomic_flag_val s \<noteq> None \<or>
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<and>
                \<not> (List.member xseq opid'))"
proof (rule ccontr)
  assume a4: "\<not> (atomic_flag_val s \<noteq> None \<or>
        (\<exists>opid'.
            (opid' ;po^(proc_of_op opid pbm) opid) \<and>
            (type_of_mem_op_block (pbm opid') = ld_block \<or>
             type_of_mem_op_block (pbm opid') = ald_block \<or>
             type_of_mem_op_block (pbm opid') = st_block \<or>
             type_of_mem_op_block (pbm opid') = ast_block) \<and>
            \<not> List.member xseq opid'))"
  then have f0: "atomic_flag_val s = None \<and>
                 (\<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                List.member xseq opid')"
    by auto
  from mem_op.simps have f1: "(type_of_mem_op_block (pbm opid) = ald_block) \<Longrightarrow>
    (atomic_flag_val s) = None \<Longrightarrow> (\<forall>opid'. (((opid' ;po^(proc_of_op opid pbm) opid) \<and> 
    (type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
    (List.member xseq opid'))) \<Longrightarrow> 
    (po pbm opid \<turnstile>m xseq s \<rightarrow> (xseq@[opid]) (atomic_flag_mod (Some opid) 
      (proc_exe_to_last (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
      (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) opid (atomic_load_addr 
      (proc_of_op opid pbm) (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
      (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) po xseq pbm 
      (proc_exe_to_previous (proc_of_op opid pbm) po pbm
             (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)) 
      (Some (atomic_load_addr (proc_of_op opid pbm) 
      (last (insts (pbm opid))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
      (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
      (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))))"
    by auto
  from a1 a2 f0 f1 have "(po pbm opid \<turnstile>m xseq s \<rightarrow> (xseq@[opid]) (atomic_flag_mod (Some opid) 
      (proc_exe_to_last (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
      (proc_of_op opid pbm))) (axiom_value (proc_of_op opid pbm) opid (atomic_load_addr 
      (proc_of_op opid pbm) 
      (last (insts (pbm opid))) s) po xseq pbm s) 
      (Some (atomic_load_addr (proc_of_op opid pbm) 
      (last (insts (pbm opid))) s)) (proc_exe_to_previous (proc_of_op opid pbm) po pbm
      (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s))))"
    by auto
  then have "\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
    by auto
  then show False using a2 by auto      
qed
  
lemma atom_store_op_contra: 
  assumes a1: "(type_of_mem_op_block (pbm opid) = ast_block)"
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
shows "(atomic_flag_val s) = None \<or>
       (atomic_flag_val s) \<noteq> atom_pair_id (pbm opid) \<or>
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<and>
                \<not> (List.member xseq opid'))"  
proof (rule ccontr)
  assume a3: "\<not> (atomic_flag_val s = None \<or>
        atomic_flag_val s \<noteq> atom_pair_id (pbm opid) \<or>
        (\<exists>opid'.
            (opid' ;po^(proc_of_op opid pbm) opid) \<and>
            (type_of_mem_op_block (pbm opid') = ld_block \<or>
             type_of_mem_op_block (pbm opid') = ald_block \<or>
             type_of_mem_op_block (pbm opid') = st_block \<or>
             type_of_mem_op_block (pbm opid') = ast_block) \<and>
            \<not> List.member xseq opid'))"
  then have f0: "atomic_flag_val s \<noteq> None \<and>
    atomic_flag_val s = atom_pair_id (pbm opid) \<and>
    (\<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                List.member xseq opid')"
    by auto
  then obtain opid' where f1: "atomic_flag_val s = Some opid'"
    by blast
  from mem_op.simps have f2: "(type_of_mem_op_block (pbm opid) = ast_block) \<Longrightarrow>
    (atomic_flag_val s) = Some opid' \<Longrightarrow> atom_pair_id (pbm opid) = Some opid' \<Longrightarrow>
    \<forall>opid'. (((opid' ;po^(proc_of_op opid pbm) opid) \<and> (type_of_mem_op_block (pbm opid') \<in> 
      {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> (List.member xseq opid')) \<Longrightarrow>
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (mem_commit opid (atomic_flag_mod None 
      (proc_exe_to (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
      (proc_of_op opid pbm))) s)))"  
    by auto
  then have "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (mem_commit opid (atomic_flag_mod None 
      (proc_exe_to (proc_of_op opid pbm) po pbm (non_repeat_list_pos opid (po 
      (proc_of_op opid pbm))) s)))"
    using a1 f0 f1 by auto
  then have "\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
    by auto
  then show False using a2 by auto
qed  
  
lemma atom_o_op_contra: 
  assumes a1: "(type_of_mem_op_block (pbm opid) = o_block)"
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
shows "(\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<and>
                \<not> (List.member xseq opid'))"  
proof (rule ccontr)
  assume a3: "\<nexists>opid'.
       (opid' ;po^(proc_of_op opid pbm) opid) \<and>
       (type_of_mem_op_block (pbm opid') = ld_block \<or>
        type_of_mem_op_block (pbm opid') = ald_block \<or>
        type_of_mem_op_block (pbm opid') = st_block \<or>
        type_of_mem_op_block (pbm opid') = ast_block) \<and>
       \<not> List.member xseq opid'"
  then have f0: "\<forall>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<longrightarrow>
                List.member xseq opid'"
    by auto
  from mem_op.simps have f1: "(type_of_mem_op_block (pbm opid) = o_block) \<Longrightarrow>
    \<forall>opid'. (((opid' ;po^(proc_of_op opid pbm) opid) \<and> (type_of_mem_op_block (pbm opid') \<in> 
      {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> (List.member xseq opid')) \<Longrightarrow> 
    po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (proc_exe_to (proc_of_op opid pbm) po pbm 
    (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)"
    by auto
  then have "po pbm opid \<turnstile>m xseq s \<rightarrow> xseq@[opid] (proc_exe_to (proc_of_op opid pbm) po pbm 
    (non_repeat_list_pos opid (po (proc_of_op opid pbm))) s)"
    using a1 f0 by auto
  then have "\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s')"
    by auto
  then show False using a2 by auto
qed  
  
text {* The lemmas below use the above lemmas to derive that if a rule is not applicable,
then at least one axiom is violated. *}  
  
text {* First, we define conditions where a partial execution violates the axioms and that
no matter how the execution continues the axioms will be violated in a complete
execution. 

We do this because it is possible that the negation of an axiom holds in a partial
execution but it doesn't hold in a continuation of the partial execution. 
The main reason for this to happen is because memory order is only partially 
observed in the partial execution. 

So we need to define conditions such that once they are violated in a partial execution,
they will be violated in any continuation of the partial execution. *}
  
definition axiom_loadop_violate:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_loadop_violate opid opid' po xseq pbm \<equiv> 
  (type_of_mem_op_block (pbm opid) \<in> {ld_block, ald_block}) \<and>
  (opid ;po^(proc_of_op opid pbm) opid') \<and> 
  (opid m<xseq opid') = Some False"   

definition axiom_storestore_violate:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_storestore_violate opid opid' po xseq pbm \<equiv> 
  (type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
  (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
  (opid ;po^(proc_of_op opid pbm) opid') \<and>
  (opid m<xseq opid') = Some False"  

definition axiom_atomicity_violate:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_atomicity_violate opid opid' po xseq pbm \<equiv> 
  (atom_pair_id (pbm opid') = Some opid) \<and> 
  (type_of_mem_op_block (pbm opid) = ald_block) \<and>
  (type_of_mem_op_block (pbm opid') = ast_block) \<and>
  (opid ;po^(proc_of_op opid pbm) opid') \<and> 
  (((opid m<xseq opid') = Some False) \<or> 
  (\<exists>opid''. type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and> 
            List.member xseq opid'' \<and> opid'' \<noteq> opid' \<and>
            (opid'' m<xseq opid) = Some False \<and> (opid' m<xseq opid'') = Some False))"  

text {* Now we show that the above conditions persist through any continuation of
execution. *}    
  
lemma mem_order_before_false_persist: 
  assumes a1: "non_repeat_list (xseq@xseq')"  
  and a2: "opid \<noteq> opid'"
  and a3: "(opid m<xseq opid') = Some False"
shows "(opid m<(xseq@xseq') opid') = Some False"
proof (insert assms, induction xseq' rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  define thisseq where "thisseq \<equiv> xseq @ xs"   
  from snoc(2) have f0: "non_repeat_list thisseq"
    using non_repeat_list_sublist append.assoc thisseq_def by blast
  then have f1: "(opid m<thisseq opid') = Some False"
    using snoc(1) thisseq_def a2 a3 by auto
  then have f2: "((List.member thisseq opid) \<and> (List.member thisseq opid') \<and> 
    \<not>(list_before opid thisseq opid')) \<or> 
    (\<not>(List.member thisseq opid) \<and> (List.member thisseq opid'))"
    using mem_order_false_cond by auto
  then have f3: "((List.member thisseq opid) \<and> (List.member thisseq opid') \<and> 
    (list_before opid' thisseq opid)) \<or> 
    (\<not>(List.member thisseq opid) \<and> (List.member thisseq opid'))"
    using dist_elem_not_before a2 by auto
  then show ?case 
  proof (rule disjE)
    assume a4: "List.member thisseq opid \<and> List.member thisseq opid' \<and> 
      list_before opid' thisseq opid"
    then have f4: "List.member (thisseq@[x]) opid" 
      unfolding list_before_def
      by (simp add: member_def)
    from a4 have f5: "List.member (thisseq@[x]) opid'" 
      unfolding list_before_def
      by (simp add: member_def)
    from a4 have f8: "list_before opid' (thisseq@[x]) opid"
      using list_before_extend by auto
    then have f9: "\<not>(list_before opid (thisseq@[x]) opid')" 
      using non_repeat_list_before snoc(2) thisseq_def
      by fastforce 
    from a2 f4 f5 f9 have f10: "(opid m<(thisseq@[x]) opid') = Some False"
      unfolding memory_order_before_def by auto 
    then show ?thesis unfolding axiom_loadop_violate_def
      thisseq_def by auto
  next
    assume a5: "\<not> List.member thisseq opid \<and> List.member thisseq opid'"
    then have f11: "List.member (thisseq@[x]) opid'"
      by (simp add: member_def)      
    then show ?thesis 
    proof (cases "x = opid")
      case True
      then have f12: "List.member (thisseq@[x]) opid"
        by (simp add: member_def)
      have f13: "list_before opid' (thisseq@[x]) opid"
        using a5 True unfolding list_before_def 
        apply auto
        by (metis a2 f11 in_set_conv_nth in_set_member length_append_singleton less_Suc_eq nth_append_length)        
      then have f14: "\<not>(list_before opid (thisseq@[x]) opid')"
        using non_repeat_list_before snoc(2) thisseq_def by fastforce
      then show ?thesis unfolding memory_order_before_def
        using f11 f12 f13 thisseq_def by auto
    next
      case False
      then have f15: "\<not>(List.member (thisseq@[x]) opid)"
        using thisseq_def a5
        by (metis insert_iff list.set(2) member_def rotate1.simps(2) set_rotate1) 
      then show ?thesis unfolding memory_order_before_def
        using f11 thisseq_def by auto
    qed
  qed
qed  
  
lemma axiom_loadop_violate_imp:
  assumes a1: "axiom_loadop_violate opid opid' po xseq pbm"
  shows "\<not>(axiom_loadop opid opid' po xseq pbm)"
  using a1 unfolding axiom_loadop_def axiom_loadop_violate_def by auto
    
lemma axiom_storestore_violate_imp:
  assumes a1: "axiom_storestore_violate opid opid' po xseq pbm"
  shows "\<not>(axiom_storestore opid opid' po xseq pbm)"
using a1 unfolding axiom_storestore_def axiom_storestore_violate_def by auto    
  
lemma axiom_atomicity_violate_imp:
  assumes a1: "axiom_atomicity_violate opid opid' po xseq pbm"
  shows "\<not>(axiom_atomicity opid opid' po xseq pbm)"
using a1 unfolding axiom_atomicity_def axiom_atomicity_violate_def by auto   
  
lemma axiom_loadop_violate_persist:
  assumes a0: "valid_program po pbm"
  assumes a1: "axiom_loadop_violate opid opid' po xseq pbm"
  assumes a2: "non_repeat_list (xseq@xseq')"
  shows "axiom_loadop_violate opid opid' po (xseq@xseq') pbm"  
proof -
  from a1 have f1: "(type_of_mem_op_block (pbm opid) \<in> {ld_block, ald_block}) \<and>
    (opid ;po^(proc_of_op opid pbm) opid') \<and> 
    (opid m<xseq opid') = Some False"
    unfolding axiom_loadop_violate_def by auto
  from a0 f1 have f2: "opid \<noteq> opid'" 
    using prog_order_op_unique by blast
  from f1 f2 a2 have f3: "(opid m<(xseq@xseq') opid') = Some False"
    using mem_order_before_false_persist by auto
  then show ?thesis unfolding axiom_loadop_violate_def
    using f1 by auto
qed  

lemma axiom_storestore_violate_persist:
  assumes a0: "valid_program po pbm"
  assumes a1: "axiom_storestore_violate opid opid' po xseq pbm"
  assumes a2: "non_repeat_list (xseq@xseq')"
  shows "axiom_storestore_violate opid opid' po (xseq@xseq') pbm" 
proof -
  from a1 have f1: "(type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
    (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
    (opid ;po^(proc_of_op opid pbm) opid') \<and>
    (opid m<xseq opid') = Some False"
    using axiom_storestore_violate_def by auto
  from a0 f1 have f2: "opid \<noteq> opid'" 
    using prog_order_op_unique by blast
  from f1 f2 a2 have f3: "(opid m<(xseq@xseq') opid') = Some False"
    using mem_order_before_false_persist by auto
  then show ?thesis unfolding axiom_storestore_violate_def
    using f1 by auto
qed
  
lemma axiom_atomicity_violate_persist:
  assumes a0: "valid_program po pbm"
  assumes a1: "axiom_atomicity_violate opid opid' po xseq pbm"
  assumes a2: "non_repeat_list (xseq@xseq')"
  shows "axiom_atomicity_violate opid opid' po (xseq@xseq') pbm"
proof -
  from a1 have f1: "(atom_pair_id (pbm opid') = Some opid) \<and> 
    (type_of_mem_op_block (pbm opid) = ald_block) \<and>
    (type_of_mem_op_block (pbm opid') = ast_block) \<and>
    (opid ;po^(proc_of_op opid pbm) opid') \<and> 
    (((opid m<xseq opid') = Some False) \<or> 
    (\<exists>opid''. type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and> 
            List.member xseq opid'' \<and> opid'' \<noteq> opid' \<and>
            (opid'' m<xseq opid) = Some False \<and> (opid' m<xseq opid'') = Some False))"    
    using axiom_atomicity_violate_def by auto
  from a0 f1 have f2: "opid \<noteq> opid'" 
    using prog_order_op_unique by blast 
  show ?thesis 
  proof (cases "((opid m<xseq opid') = Some False)")
    case True
    from True f2 a2 have f3: "(opid m<(xseq@xseq') opid') = Some False"
    using mem_order_before_false_persist by auto
  then show ?thesis unfolding axiom_atomicity_violate_def
    using f1 by auto
  next
    case False
    then obtain opid'' where f4: "type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and> 
      List.member xseq opid'' \<and> opid'' \<noteq> opid' \<and>
      (opid'' m<xseq opid) = Some False \<and> (opid' m<xseq opid'') = Some False"
      using f1 by auto
    then have f5: "List.member (xseq@xseq') opid''"
      by (meson is_sublist_def sublist_member)
    from f4 have f6: "opid'' \<noteq> opid'"
      by auto
    from f1 f4 have f7: "opid'' \<noteq> opid" by auto
    from a2 f7 f4 have f8: "(opid'' m<(xseq@xseq') opid) = Some False"
      using mem_order_before_false_persist by auto
    from a2 f6 f4 have f9: "(opid' m<(xseq@xseq') opid'') = Some False"
      using mem_order_before_false_persist by auto
    then show ?thesis unfolding axiom_atomicity_violate_def
      using f1 f4 f5 f8 f9 by auto
  qed
qed  
  
text {* We now show lemmas that says if a rule is not applicable, then
at least one axiom is violated. *}

lemma load_op_contra_violate_sub1: 
  assumes a1: "type_of_mem_op_block (pbm opid) = ld_block"
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
  and a3: "valid_program po pbm"
shows "\<exists>opid'. (axiom_loadop_violate opid' opid po (xseq@[opid]) pbm)"
proof -
  from a1 a2 obtain opid' where f1: "(opid' ;po^(proc_of_op opid pbm) opid) \<and>
    (type_of_mem_op_block (pbm opid') = ld_block \<or>
     type_of_mem_op_block (pbm opid') = ald_block) \<and>
    \<not> (List.member xseq opid')"
    using load_op_contra by blast
  then have f2: "opid \<noteq> opid'"
    using a3 prog_order_op_unique by blast
  then have f3: "\<not> (List.member (xseq@[opid]) opid')"
    using f1
    by (metis in_set_member rotate1.simps(2) set_ConsD set_rotate1)
  have f4: "List.member (xseq@[opid]) opid"
    using in_set_member by force
  then have f5: "(opid' m<(xseq@[opid]) opid) = Some False"    
    using f3 unfolding memory_order_before_def by auto  
  from a3 f1 have f6: "proc_of_op opid pbm = proc_of_op opid' pbm" 
    unfolding valid_program_def by fastforce  
  then have "\<exists>opid'. type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block} \<and>
           (opid' ;po^(proc_of_op opid' pbm) opid) \<and>
           ((opid' m<(xseq @ [opid]) opid) = Some False)"
    using f1 f5 by auto  
  then show ?thesis unfolding axiom_loadop_violate_def
    by simp    
qed  
  
lemma load_op_contra_violate: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"  
  and a2: "type_of_mem_op_block (pbm opid) = ld_block"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"
shows "\<exists>opid'. (axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm)"
proof -
  from a1 have f1: "valid_program po pbm"
    unfolding valid_mem_exe_seq_def by auto
  show ?thesis using load_op_contra_violate_sub1[OF a2 a3 f1] by auto
qed  
  
lemma atom_load_executed_sub1:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
shows "List.member (fst (last exe_list)) opid' \<and>
       type_of_mem_op_block (pbm opid') = ald_block"
proof (insert assms, induction exe_list rule: rev_induct)
  case Nil
  then show ?case unfolding valid_mem_exe_seq_def by auto
next
  case (snoc x xs)
  then show ?case 
  proof (cases "xs = []")
    case True
    then have f1: "valid_mem_exe_seq po pbm [x] \<and> 
      atomic_flag_val (snd (snd (last [x]))) = Some opid'"
      using snoc(2) snoc(3) by auto
    then have f2: "(atomic_flag_val (snd (snd (hd [x]))) = None)"
      unfolding valid_mem_exe_seq_def by auto
    then show ?thesis using f1
      by simp      
  next
    case False
    then have f3: "length xs > 0"
      by auto
    from snoc(2) have f4: "valid_program po pbm \<and> fst (List.hd (xs@[x])) = [] \<and> 
      (\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (List.hd (xs@[x]))))) \<and>
      (atomic_flag_val (snd (snd (hd (xs@[x])))) = None) \<and>
      (\<forall>i. i < (List.length (xs@[x])) - 1 \<longrightarrow> (po pbm \<turnstile>t ((xs@[x])!i) \<rightarrow> ((xs@[x])!(i+1))))"    
      unfolding valid_mem_exe_seq_def by auto
    then have f5: "fst (List.hd xs) = []"
      using f3 by auto
    have f6: "(\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (List.hd xs))))"
      using f3 f4 by auto
    have f7: "(atomic_flag_val (snd (snd (hd xs))) = None)"
      using f3 f4 by auto
    have f8: "(\<forall>i. i < (List.length xs) - 1 \<longrightarrow> (po pbm \<turnstile>t (xs!i) \<rightarrow> (xs!(i+1))))" 
      using f3 f4
    proof -
      { fix nn :: nat
        have "Suc (length (butlast xs)) = length xs"
          using f3 by auto
        then have "\<not> nn < length xs - 1 \<or> (po pbm \<turnstile>t xs ! nn \<rightarrow> (xs ! (nn + 1)))"
          by (metis (no_types) Suc_eq_plus1 Suc_less_eq butlast_snoc f4 length_butlast less_Suc_eq nth_append) }
      then show ?thesis
        by meson
    qed 
    then have f9: "valid_mem_exe_seq po pbm xs" 
      using valid_mem_exe_seq_def f3 f4 f5 f6 f7 f8 by auto
    from snoc(2) have "\<forall>i < (List.length (xs@[x])) - 1. 
      (po pbm \<turnstile>t ((xs@[x])!i) \<rightarrow> ((xs@[x])!(i+1)))"    
      unfolding valid_mem_exe_seq_def by auto
    then have f11: "(po pbm \<turnstile>t (last xs) \<rightarrow> x)"
      by (metis (no_types, lifting) False One_nat_def Suc_eq_plus1 Suc_pred append_butlast_last_id butlast_snoc diff_self_eq_0 f3 hd_conv_nth length_butlast lessI less_not_refl2 list.distinct(1) list.sel(1) nth_append)
    then have f09: "\<exists>opid. (fst x) = (fst (last xs))@[opid]"
      unfolding mem_state_trans_def using mem_op_exe
      by meson    
    from f11 obtain opid''' where f13: "po pbm opid''' \<turnstile>m (fst (last xs)) (snd (snd (last xs))) 
          \<rightarrow> (fst x) (snd (snd x))"
          unfolding mem_state_trans_def by auto    
    then show ?thesis 
    proof (cases "atomic_flag_val (snd (snd (last xs))) = Some opid'")
      case True
      then have f10: "List.member (fst (last xs)) opid' \<and> 
        type_of_mem_op_block (pbm opid') = ald_block"  
        using f9 snoc(1) by auto               
      then show ?thesis using f3 f10 f09
        by (metis (no_types, lifting) insert_iff last_snoc list.set(2) member_def rotate1.simps(2) set_rotate1) 
    next
      case False
      then have "(\<exists>opid''. atomic_flag_val (snd (snd (last xs))) = Some opid'' \<and> opid'' \<noteq> opid')
        \<or> atomic_flag_val (snd (snd (last xs))) = None"
        by auto        
      then show ?thesis 
      proof (rule disjE)
        assume a3: "\<exists>opid''. atomic_flag_val (snd (snd (last xs))) = Some opid'' \<and> opid'' \<noteq> opid'"
        then obtain opid'' where f12: "atomic_flag_val (snd (snd (last xs))) = Some opid'' \<and> 
          opid'' \<noteq> opid'"
          by auto        
        have f14: "type_of_mem_op_block (pbm opid''') = ld_block \<or> 
          type_of_mem_op_block (pbm opid''') = o_block \<or>
          (type_of_mem_op_block (pbm opid''') = ast_block \<and>
            atom_pair_id (pbm opid''') = Some opid'')"
          using atomic_flag_exe1 f12 f13 by auto
        then have "atomic_flag_val (snd (snd x)) = Some opid'' \<or>
                   atomic_flag_val (snd (snd x)) = None"
          using atomic_flag_exe2 atomic_flag_exe3 f13 f12 by auto
        then have "atomic_flag_val (snd (snd x)) \<noteq> Some opid'"
          using f12 by auto        
        then show ?thesis using snoc(3) by auto 
      next        
        assume a4: "atomic_flag_val (snd (snd (last xs))) = None"
        from snoc(3) have f15: "atomic_flag_val (snd (snd x)) = Some opid'"
          by auto
        then have f16: "type_of_mem_op_block (pbm opid''') = ald_block"
          using atomic_flag_exe4[OF f13 a4] by auto
        then have "atomic_flag_val (snd (snd x)) = Some opid'''"
          using atomic_flag_exe_ald[OF f13 a4] by auto
        then have f17: "opid' = opid'''"
          using f15 by auto
        then have f18: "type_of_mem_op_block (pbm opid') = ald_block"
          using f16 by auto
        from f13 f17 have "(fst x) = (fst (last xs))@[opid']"
          using mem_op_exe by auto
        then have "List.member (fst x) opid'"
          using in_set_member by fastforce          
        then show ?thesis using f18 by auto
      qed  
    qed      
  qed    
qed  
    
lemma atom_load_executed_sub2_sub1:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "j < (List.length exe_list - 1)"
  and a3: "(k > j \<and> k < (length exe_list - 1))"
  and a4: "\<forall>k'. (k' > j \<and> k' < (length exe_list - 1)) \<longrightarrow>
                ((fst (List.last exe_list))!k') \<noteq> opid'"
  and a5: "atomic_flag_val (snd (snd (exe_list ! (j + 1)))) \<noteq> Some opid'"
shows "atomic_flag_val (snd (snd (exe_list!(k+1)))) \<noteq> Some opid'"
proof (insert assms, induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  from Suc(4) have "k = j \<or> j < k"
    by auto
  then have f1: "atomic_flag_val (snd (snd (exe_list ! (k + 1)))) \<noteq> Some opid'"
    using Suc by auto
  from Suc(4) have f2: 
    "(po pbm ((fst (List.last exe_list))!(k+1)) \<turnstile>m (fst (exe_list!(k+1))) (snd (snd (exe_list!(k+1)))) \<rightarrow>
      (fst (exe_list!((k+1)+1))) (snd (snd (exe_list!((k+1)+1)))))"
    using valid_exe_op_exe_pos2[OF Suc(2)] by auto
  from a4 have "((fst (List.last exe_list))!(k+1)) \<noteq> opid'"
    using Suc(4) by auto
  then have "atomic_flag_val (snd (snd (exe_list ! ((k+1) + 1)))) \<noteq> Some opid'"      
    using atomic_flag_exe5[OF f2 f1] by auto
  then show ?case by auto 
qed
    
lemma atom_load_executed_sub2:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
  and a3: "type_of_mem_op_block (pbm opid'') = ast_block"
  and a4: "atom_pair_id (pbm opid'') = Some opid'"
  and a5: "(opid' ;po^(proc_of_op opid' pbm) opid'')"
  and f0: "List.member (fst (last exe_list)) opid''"
shows "axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm"    
proof - 
  from a1 a2 have f1: "List.member (fst (last exe_list)) opid' \<and>
       type_of_mem_op_block (pbm opid') = ald_block"  
    using atom_load_executed_sub1 by auto
  then obtain i where f2: "i < (List.length exe_list - 1) \<and> 
    (fst (List.last exe_list))!i = opid'"
    by (metis a1 in_set_conv_nth in_set_member valid_exe_xseq_sublist_length2)
  then have f3: "(po pbm opid' \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
    using valid_exe_op_exe_pos f2 a1 by auto
  from f0 obtain j where f4: "j < (List.length exe_list - 1) \<and> 
    (fst (List.last exe_list))!j = opid''"
    by (metis a1 in_set_conv_nth in_set_member valid_exe_xseq_sublist_length2)
  then have f5: "(po pbm opid'' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
        (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"
    using valid_exe_op_exe_pos f4 a1 by auto
  from a1 have f6: "non_repeat_list (fst (List.last exe_list))"
    using valid_mem_exe_seq_op_unique by auto
  from a1 a5 have f7: "opid' \<noteq> opid''"
    unfolding valid_mem_exe_seq_def using prog_order_op_unique by blast
  then have f8: "i \<noteq> j"
    using f2 f4 f6 unfolding non_repeat_list_def by auto
  then have "i < j \<or> i > j"
    by auto
  then show ?thesis
  proof (rule disjE)
    assume a7: "i > j"
    then have "\<nexists>k. k < length (fst (last exe_list)) \<and>
          fst (last exe_list) ! k = opid' \<and> k < j"
      using f6 f2 f4 unfolding non_repeat_list_def
      using a1 le0 valid_exe_xseq_sublist_length2 
      using nth_eq_iff_index_eq
      by (metis (mono_tags, hide_lams) not_less_iff_gr_or_eq)        
      \<comment>\<open>by auto   \<close>  
    then have "\<nexists>k k'. k < length (fst (last exe_list)) \<and> k' < length (fst (last exe_list)) \<and>
          fst (last exe_list) ! k = opid' \<and> fst (last exe_list) ! k' = opid'' \<and> k < k'"
      using f6 f2 f4 unfolding non_repeat_list_def
      using nth_eq_iff_index_eq by fastforce  
      \<comment>\<open> by auto \<close> 
    then have "\<not> (list_before opid' (fst (last exe_list)) opid'')"
      unfolding list_before_def by blast    
    then have "(opid' m<(fst (last exe_list)) opid'') = Some False"
      unfolding memory_order_before_def using f2 f0 f1 by auto    
    then show ?thesis using f1 a5 unfolding axiom_loadop_violate_def by auto
  next
    assume a6: "i < j"
    have f9: "(snd (snd (exe_list ! (j + 1)))) = 
      mem_commit opid'' (atomic_flag_mod None (proc_exe_to (proc_of_op opid'' pbm) 
      po pbm (non_repeat_list_pos opid'' (po (proc_of_op opid'' pbm)))  
      (snd (snd (exe_list ! j)))))"
      using mem_op_elim_atom_store_op[OF f5 a3] by auto
    then have f10: "atomic_flag_val (snd (snd (exe_list ! (j + 1)))) = None"
      using atomic_flag_mod_none mem_commit_atomic_flag by auto
    have f11: "\<forall>k. (k > j \<and> k < (length exe_list - 1)) \<longrightarrow> 
      ((fst (List.last exe_list))!k) \<noteq> opid'"
      using f6 f2 a6 unfolding non_repeat_list_def
      using a1 not_less_iff_gr_or_eq valid_exe_xseq_sublist_length2
      using nth_eq_iff_index_eq by metis        
      \<comment>\<open>by auto\<close>      
    have f12: "\<forall>(k::nat). (k > j \<and> k < (length exe_list - 1)) \<longrightarrow> 
      atomic_flag_val (snd (snd (exe_list!(k+1)))) \<noteq> Some opid'"
      using atom_load_executed_sub2_sub1[OF a1] f4 f11 f10 by auto
    show ?thesis 
    proof (cases "j = (length exe_list - 1) - 1")
      case True
      then have "atomic_flag_val (snd (snd (exe_list ! (length exe_list - 1)))) = None"
        using f10
        by (metis (no_types, lifting) One_nat_def \<open>\<And>thesis. (\<And>i. i < length exe_list - 1 \<and> fst (last exe_list) ! i = opid' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a1 add.right_neutral add_Suc_right gr_implies_not0 list_exhaust_size_gt0 nth_Cons' nth_Cons_Suc valid_mem_exe_seq_def)
      then show ?thesis using a2
        using a1 last_conv_nth valid_mem_exe_seq_def by fastforce 
    next
      case False
      then have "j < (length exe_list - 1 - 1)"
        using f4 by auto
      then have "atomic_flag_val (snd (snd (exe_list!((length exe_list - 1 - 1)+1)))) \<noteq> Some opid'"
        using f12 by auto
      then have "atomic_flag_val (snd (snd (exe_list!(length exe_list - 1)))) \<noteq> Some opid'"        
        by (metis (no_types, lifting) One_nat_def \<open>\<And>thesis. (\<And>i. i < length exe_list - 1 \<and> fst (last exe_list) ! i = opid' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a1 add.right_neutral add_Suc_right gr_implies_not0 list_exhaust_size_gt0 nth_Cons' nth_Cons_Suc valid_mem_exe_seq_def)
      then show ?thesis using a2 
        using a1 last_conv_nth valid_mem_exe_seq_def by fastforce
    qed
  qed
qed  

lemma atom_load_executed0: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
  and a4: "\<exists>opid''. type_of_mem_op_block (pbm opid') = ald_block \<and>
                type_of_mem_op_block (pbm opid'') = ast_block \<and>
                atom_pair_id (pbm opid'') = Some opid' \<and>
                (opid' ;po^(proc_of_op opid' pbm) opid'') \<and>
                List.member (fst (last exe_list)) opid' \<and>
                (List.member (fst (last exe_list)) opid'')"
shows "\<exists>opid''. axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm"
proof -
  from a4 obtain opid'' where f0: "type_of_mem_op_block (pbm opid') = ald_block \<and>
                type_of_mem_op_block (pbm opid'') = ast_block \<and>
                atom_pair_id (pbm opid'') = Some opid' \<and>
                (opid' ;po^(proc_of_op opid' pbm) opid'') \<and>
                List.member (fst (last exe_list)) opid' \<and>
                (List.member (fst (last exe_list)) opid'')"
    by auto
  then show ?thesis using atom_load_executed_sub2[OF a1 a2]
    by blast   
qed  
  
lemma atom_load_executed: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
  and a3: "\<not>(\<exists>opid''. axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm)"
  shows "\<exists>opid''. type_of_mem_op_block (pbm opid') = ald_block \<and>
                type_of_mem_op_block (pbm opid'') = ast_block \<and>
                atom_pair_id (pbm opid'') = Some opid' \<and>
                (opid' ;po^(proc_of_op opid' pbm) opid'') \<and>
                List.member (fst (last exe_list)) opid' \<and>
                \<not> (List.member (fst (last exe_list)) opid'')"
proof -
  have f0: "\<not>(\<exists>opid''. type_of_mem_op_block (pbm opid') = ald_block \<and>
                type_of_mem_op_block (pbm opid'') = ast_block \<and>
                atom_pair_id (pbm opid'') = Some opid' \<and>
                (opid' ;po^(proc_of_op opid' pbm) opid'') \<and>
                List.member (fst (last exe_list)) opid' \<and>
                (List.member (fst (last exe_list)) opid''))"
    using atom_load_executed0[OF a1 a2] using a3 by auto
  from a1 a2 have f1: "List.member (fst (last exe_list)) opid' \<and>
    type_of_mem_op_block (pbm opid') = ald_block"
    using atom_load_executed_sub1 by auto
  from a1 have f2: "(set (fst (last exe_list))) \<union> (fst (snd (last exe_list))) = 
       (fst (snd (hd exe_list)))"
    using valid_exe_xseq_sublist_last by auto
  then have f3: "opid' \<in> (fst (snd (hd exe_list)))"
    using f1 in_set_member by fastforce 
  then obtain p where f4: "(List.member (po p) opid')"
    using a1 unfolding valid_mem_exe_seq_def by auto
  then obtain opid'' where f5: "(opid' ;po^p opid'') \<and> 
    type_of_mem_op_block (pbm opid'') = ast_block \<and> atom_pair_id (pbm opid'') = Some opid'"
    using a1 f1 unfolding valid_mem_exe_seq_def valid_program_def
    by meson       
  then have f6: "p = proc_of_op opid' pbm"
    using a1 unfolding valid_mem_exe_seq_def valid_program_def
    by blast
  from f5 have f7: "type_of_mem_op_block (pbm opid'') = ast_block"
    by auto
  from f5 have f8: "atom_pair_id (pbm opid'') = Some opid'"
    by simp
  from f5 f6 have f9: "opid' ;po^(proc_of_op opid' pbm) opid''"
    by auto
  have f10: "\<not> (List.member (fst (last exe_list)) opid'')"
    using f1 f7 f8 f9 f0
    by auto 
  show ?thesis using f1 f7 f8 f9 f0 f10
    by auto
qed    
  
lemma store_op_contra_violate_sub2: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
  and a3: "type_of_mem_op_block (pbm opid) = st_block"  
  and a6: "\<not> (List.member (fst (last exe_list)) opid)"
  and a7: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid''. (axiom_atomicity_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
                (axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm)"
proof (cases "(\<exists>opid''. axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm)")
  case True
  then obtain opid'' where f0_0: "axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm"
    by auto
  have f0_1: "valid_program po pbm"
    using a1 unfolding valid_mem_exe_seq_def by auto
  have f0: "non_repeat_list (((fst (last exe_list))@[opid])@remainder)"
    using a7 unfolding op_seq_final_def by auto
  then have f1: "non_repeat_list ((fst (last exe_list))@[opid])"
    using non_repeat_list_sublist by blast  
  show ?thesis 
    using axiom_loadop_violate_persist[OF f0_1 f0_0 f1] 
    by auto
next
  case False
  obtain opid'' where f1: "type_of_mem_op_block (pbm opid') = ald_block \<and>
    type_of_mem_op_block (pbm opid'') = ast_block \<and>
    atom_pair_id (pbm opid'') = Some opid' \<and>
    (opid' ;po^(proc_of_op opid' pbm) opid'') \<and>
    List.member (fst (last exe_list)) opid' \<and>
    \<not>(List.member (fst (last exe_list)) opid'')"
    using atom_load_executed[OF a1 a2 False] by auto
  from a3 f1 have f2: "opid \<noteq> opid'" by auto
  from a3 f1 have f3: "opid \<noteq> opid''" by auto
  from f1 have f4: "List.member ((fst (last exe_list))@[opid]) opid'"
    by (metis UnCI in_set_member set_append)
  from f1 f3 have f5: "\<not>(List.member ((fst (last exe_list))@[opid]) opid'')"
    by (metis in_set_member insert_iff list.simps(15) rotate1.simps(2) set_rotate1)
  have f6: "List.member ((fst (last exe_list))@[opid]) opid"
    using in_set_member by fastforce
  then have f7: "list_before opid' ((fst (last exe_list))@[opid]) opid"  
    using f1 unfolding list_before_def
    by (metis f2 f4 in_set_member length_append_singleton length_pos_if_in_set less_Suc_eq less_imp_le list_mem_range nth_append_length) 
  have f8: "non_repeat_list (fst (last exe_list))" 
    using valid_mem_exe_seq_op_unique a1 by auto
  have f9: "non_repeat_list ((fst (last exe_list))@[opid])"
    using non_repeat_list_extend[OF f8 a6] by auto
  have f10: "\<not>(list_before opid ((fst (last exe_list))@[opid]) opid')"
    using non_repeat_list_before[OF f9 f7] by auto
  then have f11: "(opid m<(fst (last exe_list) @ [opid]) opid') = Some False"
    unfolding memory_order_before_def using f6 f4 by auto
  from f6 f5 have f12: "(opid'' m<(fst (last exe_list) @ [opid]) opid) = Some False"
    unfolding memory_order_before_def by auto
  then show ?thesis unfolding axiom_atomicity_violate_def
    using f1 a3 f6 f3 f11 f12 by auto
qed   

lemma store_op_contra_violate_sub1: 
  assumes a1: "type_of_mem_op_block (pbm opid) = st_block"
  and a2: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m xseq s \<rightarrow> xseq' s'))"
  and a3: "valid_program po pbm"
  and a4: "atomic_flag_val s = None"
shows "\<exists>opid'. (axiom_loadop_violate opid' opid po (xseq@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid po (xseq@[opid]) pbm)"  
proof -
  from a1 a2 have f1: "atomic_flag_val s \<noteq> None \<or> 
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<and>
         \<not> (List.member xseq opid'))"
    using store_op_contra by auto
  then obtain opid' where f2: "(opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<and>
         \<not> (List.member xseq opid')"
    using a4 by auto
  then have f3: "opid \<noteq> opid'"
    using a3 prog_order_op_unique by blast
  then have f4: "\<not> (List.member (xseq@[opid]) opid')"
    using f2
    by (metis in_set_member rotate1.simps(2) set_ConsD set_rotate1)
  have f5: "List.member (xseq@[opid]) opid"
    using in_set_member by force
  then have f6: "(opid' m<(xseq@[opid]) opid) = Some False"    
    using f4 unfolding memory_order_before_def by auto 
  from a3 f2 have f7: "proc_of_op opid pbm = proc_of_op opid' pbm" 
    unfolding valid_program_def by fastforce  
  from f2 have f8: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block} \<or>
          type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
    by auto
  then show ?thesis 
  proof (rule disjE)
    assume a5: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block}"
    then have "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block} \<and>
           (opid' ;po^(proc_of_op opid' pbm) opid) \<and>
           ((opid' m<(xseq @ [opid]) opid) = Some False)"
      using f2 f6 f7 by auto
    then have "\<exists>opid'. (axiom_loadop_violate opid' opid po (xseq@[opid]) pbm)"
      unfolding axiom_loadop_violate_def by auto
    then show ?thesis by auto
  next
    assume a6: "type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
    then have "(type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
      (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
      (opid' ;po^(proc_of_op opid' pbm) opid) \<and>
      (opid' m<(xseq @ [opid]) opid) = Some False"
      using f2 f6 f7 a1 by auto
    then have "\<exists>opid'. (axiom_storestore_violate opid' opid po (xseq@[opid]) pbm)"
      unfolding axiom_storestore_violate_def by auto
    then show ?thesis by auto
  qed  
qed
  
lemma store_op_contra_violate: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = st_block"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"
  and a5: "\<not> (List.member (fst (last exe_list)) opid)"
  and a6: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid' opid''. (axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm)"  
proof -
  from a2 a3 have f1: "atomic_flag_val (snd (snd (last exe_list))) \<noteq> None \<or> 
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
         (type_of_mem_op_block (pbm opid') = ld_block \<or>
          type_of_mem_op_block (pbm opid') = ald_block \<or>
          type_of_mem_op_block (pbm opid') = st_block \<or> 
          type_of_mem_op_block (pbm opid') = ast_block) \<and>
         \<not> (List.member (fst (last exe_list)) opid'))"
    using store_op_contra by auto  
  then show ?thesis 
  proof (cases "atomic_flag_val (snd (snd (last exe_list))) \<noteq> None")
    case True
    then obtain opid' where f2: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
      by auto
    show ?thesis 
      using store_op_contra_violate_sub2[OF a1 f2 a2 a5 a6] by auto
  next
    case False   
    then have f5: "atomic_flag_val (snd (snd (last exe_list))) = None"
      by auto
    from a1 have f4: "valid_program po pbm"
      unfolding valid_mem_exe_seq_def by auto
    show ?thesis using store_op_contra_violate_sub1[OF a2 a3 f4 f5] by auto
  qed
qed  

lemma atom_load_op_contra_violate_sub1: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = ald_block"
  and a3: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
  and a5: "List.member (po (proc_of_op opid pbm)) opid"
  and a6: "\<not> (List.member (fst (last exe_list)) opid)"
  and a7: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid' opid''. (axiom_atomicity_violate opid' opid'' po 
  (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
  (axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm)"
proof (cases "(\<exists>opid''. axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm)")
  case True
  then obtain opid'' where f0_0: "axiom_loadop_violate opid' opid'' po (fst (last exe_list)) pbm"
    by auto
  have f0_1: "valid_program po pbm"
    using a1 unfolding valid_mem_exe_seq_def by auto
  have f0: "non_repeat_list (((fst (last exe_list))@[opid])@remainder)"
    using a7 unfolding op_seq_final_def by auto
  then have f1: "non_repeat_list ((fst (last exe_list))@[opid])"
    using non_repeat_list_sublist by blast  
  show ?thesis 
    using axiom_loadop_violate_persist[OF f0_1 f0_0 f1] 
    by auto
next
  case False
  then obtain opid'_st where f1: "type_of_mem_op_block (pbm opid') = ald_block \<and>
    type_of_mem_op_block (pbm opid'_st) = ast_block \<and>
    atom_pair_id (pbm opid'_st) = Some opid' \<and>
    (opid' ;po^(proc_of_op opid' pbm) opid'_st) \<and>
    List.member (fst (last exe_list)) opid' \<and>
   \<not>(List.member (fst (last exe_list)) opid'_st)" 
    using atom_load_executed[OF a1 a3] by auto
  from a1 a2 a5 obtain opid_st where f2: "(opid ;po^(proc_of_op opid pbm) opid_st) \<and> 
    type_of_mem_op_block (pbm opid_st) = ast_block \<and> atom_pair_id (pbm opid_st) = Some opid"    
    unfolding valid_mem_exe_seq_def valid_program_def by blast
  from a6 f1 have f3: "opid \<noteq> opid'" by auto
  from a2 f1 have f4: "opid \<noteq> opid'_st" by auto
  from f1 f2 have f5: "opid_st \<noteq> opid'" by auto
  from f1 f2 f3 have f6: "opid_st \<noteq> opid'_st" by auto
  from a2 f2 have f7: "opid \<noteq> opid_st" by auto
  have f8: "non_repeat_list (fst (last exe_list))"
    using valid_mem_exe_seq_op_unique[OF a1] by auto
  then have f9: "non_repeat_list ((fst (last exe_list))@[opid])"
    using a6 non_repeat_list_extend by fastforce   
  from f2 have "List.member (po (proc_of_op opid pbm)) opid_st"
    unfolding program_order_before_def list_before_def
    by (meson list_mem_range_rev) 
  then have f91: "List.member (((fst (last exe_list))@[opid])@remainder) opid_st"
    using f2 a7 unfolding op_seq_final_def by auto
  from f1 have "List.member (po (proc_of_op opid' pbm)) opid'_st"
    unfolding program_order_before_def list_before_def
    by (meson list_mem_range_rev)
  then have f92: "List.member (((fst (last exe_list))@[opid])@remainder) opid'_st"
    using f2 a7 unfolding op_seq_final_def by auto
  show ?thesis
  proof (cases "(List.member (fst (last exe_list)) opid_st)")
    case True
    then have f10: "(opid m<(fst (last exe_list)) opid_st) = Some False"
      unfolding memory_order_before_def using a6 by auto
    then have "(atom_pair_id (pbm opid_st) = Some opid) \<and> 
      (type_of_mem_op_block (pbm opid) = ald_block) \<and>
      (type_of_mem_op_block (pbm opid_st) = ast_block) \<and>
      (opid ;po^(proc_of_op opid pbm) opid_st) \<and> 
      ((opid m<(fst (last exe_list)) opid_st) = Some False)"
      using f2 a2 by auto
    then have "axiom_atomicity_violate opid opid_st po (fst (last exe_list)) pbm"
      unfolding axiom_atomicity_violate_def by auto
    then show ?thesis 
      using axiom_atomicity_violate_persist a1 a7 
      unfolding valid_mem_exe_seq_def op_seq_final_def
      by (metis append.assoc)              
  next
    case False
    then have f11: "list_before opid' (((fst (last exe_list))@[opid])@remainder) opid_st"
      using f1 f91 list_before_extend2 by auto
    then have f12: "\<not>(list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid')"
      using a7  unfolding op_seq_final_def  
      by (simp add: non_repeat_list_before)
    from f1 f4 have f13: "\<not> List.member ((fst (last exe_list))@[opid]) opid'_st"
      by (metis in_set_member insert_iff list.simps(15) rotate1.simps(2) set_rotate1)
    have f14: "List.member ((fst (last exe_list))@[opid]) opid"
      using in_set_member by fastforce
    have f15: "list_before opid (((fst (last exe_list))@[opid])@remainder) opid'_st"
      using list_before_extend2[OF f14 f13 f92] by auto
    then have f16: "\<not>(list_before opid'_st (((fst (last exe_list))@[opid])@remainder) opid)"
      using a7  unfolding op_seq_final_def 
      by (simp add: non_repeat_list_before)
    have f16_1: "non_repeat_list (((fst (last exe_list))@[opid])@remainder)"
      using a7 unfolding op_seq_final_def by auto
    have f17: 
      "list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid'_st \<or> 
       list_before opid'_st (((fst (last exe_list))@[opid])@remainder) opid_st"
      using list_elements_before[OF f91 f92 f6] by auto
    then show ?thesis 
    proof (rule disjE)
      assume f18: "list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid'_st"
      have f181: "\<not>(list_before opid'_st (((fst (last exe_list))@[opid])@remainder) opid_st)"
        using non_repeat_list_before[OF f16_1 f18] by auto 
      have f182: "List.member ((fst (last exe_list) @ [opid]) @ remainder) opid'"
        using f1 by (metis UnCI in_set_member set_append) 
      from f91 f182 f12 have f183: "(opid_st m<(((fst (last exe_list))@[opid])@remainder) opid') = 
        Some False"
        unfolding memory_order_before_def by auto
      from f91 f92 f181 have f184: "(opid'_st m<(((fst (last exe_list))@[opid])@remainder) opid_st) = 
        Some False"
        unfolding memory_order_before_def by auto 
      then show ?thesis unfolding axiom_atomicity_violate_def
        using f1 f2 f91 f6 f184 f183 by auto
    next
      assume f19: "list_before opid'_st (((fst (last exe_list))@[opid])@remainder) opid_st"
      have f191: "\<not>(list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid'_st)"
        using non_repeat_list_before[OF f16_1 f19] by auto 
      have f192: "List.member ((fst (last exe_list) @ [opid]) @ remainder) opid"
        using f14 by (metis UnCI in_set_member set_append) 
      from f92 f192 f16 have f193: "(opid'_st m<(((fst (last exe_list))@[opid])@remainder) opid) = 
        Some False"
        unfolding memory_order_before_def by auto
      from f91 f92 f191 have f194: "(opid_st m<(((fst (last exe_list))@[opid])@remainder) opid'_st) = 
        Some False"
        unfolding memory_order_before_def by auto        
      then show ?thesis unfolding axiom_atomicity_violate_def
        using f2 a2 f1 f92 f6 f193 f194 by auto
    qed
  qed
qed  
    
lemma atom_load_op_contra_violate_sub2: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = ald_block"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"
  and a4: "(opid' ;po^(proc_of_op opid pbm) opid) \<and>
      (type_of_mem_op_block (pbm opid') = ld_block \<or>
       type_of_mem_op_block (pbm opid') = ald_block \<or>
       type_of_mem_op_block (pbm opid') = st_block \<or> 
       type_of_mem_op_block (pbm opid') = ast_block) \<and>
      \<not> (List.member (fst (last exe_list)) opid')"
  and a6: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid' opid''. (axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
proof -
  have a5: "List.member (po (proc_of_op opid pbm)) opid"
    using a4 program_order_before_def list_before_def
    by (metis list_mem_range_rev) 
  have f0: "opid \<noteq> opid'"
    using a4 a1 prog_order_op_unique unfolding valid_mem_exe_seq_def by blast
  then have f01: "\<not> (List.member ((fst (last exe_list))@[opid]) opid')"
    using a4
    by (metis in_set_member insert_iff list.simps(15) rotate1.simps(2) set_rotate1) 
  have f02: "List.member ((fst (last exe_list))@[opid]) opid"
    using in_set_member by force  
  then have f03: "(opid' m<((fst (last exe_list))@[opid]) opid) = Some False"    
    using f01 unfolding memory_order_before_def by auto  
  from a1 a4 have f04: "proc_of_op opid pbm = proc_of_op opid' pbm" 
    unfolding valid_mem_exe_seq_def valid_program_def
    by blast  
  from a6 have f05: "non_repeat_list (((fst (last exe_list))@[opid])@remainder)"
    unfolding op_seq_final_def by auto
  from a4 have f1: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block} \<or>
    type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
    by auto
  then show ?thesis 
  proof (rule disjE)
    assume f2: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block}"        
    then show ?thesis unfolding axiom_loadop_violate_def
      using a4 f03 f04 by auto
  next
    assume f3: "type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
    from a1 have f30: "non_repeat_list (po (proc_of_op opid pbm))"
      unfolding valid_mem_exe_seq_def valid_program_def by auto
    from a1 a2 a5 obtain opid_st where f31: "(opid ;po^(proc_of_op opid pbm) opid_st) \<and> 
      type_of_mem_op_block (pbm opid_st) = ast_block \<and> atom_pair_id (pbm opid_st) = Some opid"
      unfolding valid_mem_exe_seq_def valid_program_def by blast     
    then have f32: "opid' ;po^(proc_of_op opid pbm) opid_st"
      using a4 f30 prog_order_before_trans by blast    
    from a1 a4 have f33: "(proc_of_op opid pbm) = (proc_of_op opid' pbm)"
      unfolding valid_mem_exe_seq_def valid_program_def by blast 
    from a4 have f34: "List.member (po (proc_of_op opid pbm)) opid'"
      unfolding program_order_before_def list_before_def
      by (meson list_mem_range_rev) 
    then have f35: "List.member (((fst (last exe_list))@[opid])@remainder) opid'" 
      using a4 a6 unfolding op_seq_final_def by auto        
    from f32 have "List.member (po (proc_of_op opid pbm)) opid_st"
      unfolding program_order_before_def list_before_def
      by (meson list_mem_range_rev) 
    then have f36: "List.member (((fst (last exe_list))@[opid])@remainder) opid_st"
      using a4 a6 unfolding op_seq_final_def by auto
    from f35 obtain i where f37: "i < length (((fst (last exe_list))@[opid])@remainder) \<and>
      ((((fst (last exe_list))@[opid])@remainder)!i) = opid'"
      by (meson in_set_conv_nth in_set_member)
    from f36 obtain j where f38: "j < length (((fst (last exe_list))@[opid])@remainder) \<and>
      ((((fst (last exe_list))@[opid])@remainder)!j) = opid_st"
      by (meson in_set_conv_nth in_set_member)
    from f32 a1 have f39: "opid' \<noteq> opid_st"
      unfolding valid_mem_exe_seq_def
      using prog_order_op_unique by blast 
    then have "i \<noteq> j"
      using f37 f38 by auto
    then have "i < j \<or> i > j"
      by auto
    then show ?thesis 
    proof (rule disjE)
      assume f41: "i < j"
      then have f42: "list_before opid' (((fst (last exe_list))@[opid])@remainder) opid_st"
        using f37 f38 unfolding list_before_def by blast
      have f43: "\<not>(list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid')"
        using non_repeat_list_before[OF f05 f42] by auto
      then have f44: "(opid_st m<(((fst (last exe_list))@[opid])@remainder) opid') = 
        Some False"
        unfolding memory_order_before_def using f35 f36 by auto
      then show ?thesis unfolding axiom_atomicity_violate_def
        using f31 a2 f3 f35 f39 f03
        by (metis f0 f05 mem_order_before_false_persist) 
    next
      assume f51: "i > j"
      then have f52: "list_before opid_st (((fst (last exe_list))@[opid])@remainder) opid'"
        using f37 f38 unfolding list_before_def by blast
      then have f53: "\<not>(list_before opid' (((fst (last exe_list))@[opid])@remainder) opid_st)"
        using non_repeat_list_before[OF f05 f52] by auto
      then have f44: "(opid' m<(((fst (last exe_list))@[opid])@remainder) opid_st) = 
        Some False"
        unfolding memory_order_before_def using f35 f36 by auto         
      then show ?thesis unfolding axiom_storestore_violate_def
        using f31 f3 f32 f33 by auto
    qed
  qed
qed  
  
lemma atom_load_op_contra_violate: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = ald_block"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"  
  and a5: "List.member (po (proc_of_op opid pbm)) opid"
  and a6: "\<not> (List.member (fst (last exe_list)) opid)"
  and a7: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid' opid''. (axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"    
proof -
  from a2 a3 have f1: "atomic_flag_val (snd (snd (last exe_list))) \<noteq> None \<or>
    (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
    (type_of_mem_op_block (pbm opid') = ld_block \<or>
     type_of_mem_op_block (pbm opid') = ald_block \<or>
     type_of_mem_op_block (pbm opid') = st_block \<or> 
     type_of_mem_op_block (pbm opid') = ast_block) \<and>
    \<not> (List.member (fst (last exe_list)) opid'))"
    using atom_load_op_contra by auto
  then show ?thesis 
  proof (rule disjE)
    assume f2: "atomic_flag_val (snd (snd (last exe_list))) \<noteq> None"
    then obtain opid' where f21: "atomic_flag_val (snd (snd (last exe_list))) = Some opid'"
      by auto
    show ?thesis 
      using atom_load_op_contra_violate_sub1[OF a1 a2 f21 a5 a6 a7] by auto
  next
    assume f3: "(\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
      (type_of_mem_op_block (pbm opid') = ld_block \<or>
       type_of_mem_op_block (pbm opid') = ald_block \<or>
       type_of_mem_op_block (pbm opid') = st_block \<or> 
       type_of_mem_op_block (pbm opid') = ast_block) \<and>
      \<not> (List.member (fst (last exe_list)) opid'))"
    then obtain opid' where f31: "(opid' ;po^(proc_of_op opid pbm) opid) \<and>
      (type_of_mem_op_block (pbm opid') = ld_block \<or>
       type_of_mem_op_block (pbm opid') = ald_block \<or>
       type_of_mem_op_block (pbm opid') = st_block \<or> 
       type_of_mem_op_block (pbm opid') = ast_block) \<and>
      \<not> (List.member (fst (last exe_list)) opid')"
      by auto
    show ?thesis 
      using atom_load_op_contra_violate_sub2[OF a1 a2 a3 f31 a7] by auto
  qed
qed  
  
lemma atom_exe_valid_type2: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "i < (List.length exe_list - 1)"
  and a3: "(po pbm opid \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
             (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
  and a5: "(atom_pair_id (pbm opid') = Some opid) \<and> 
           (type_of_mem_op_block (pbm opid) = ald_block) \<and>
           (type_of_mem_op_block (pbm opid') = ast_block)"
  and a6: "(i < j \<and> j < (List.length exe_list - 1) \<and> 
           (po pbm opid'' \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))))"
  and a7: "atomic_flag_val (snd (snd (exe_list!(i+1)))) = Some opid"
  and a8: "opid \<noteq> opid'' \<and> opid'' \<noteq> opid'"
  and a9: "\<not>(List.member (fst (last exe_list)) opid')"
  shows "(type_of_mem_op_block (pbm opid'') = ld_block \<or> 
          type_of_mem_op_block (pbm opid'') = o_block) \<and>
         atomic_flag_val (snd (snd (exe_list!j))) = Some opid"  
proof (insert assms, induction "j - i" arbitrary: opid'' j)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case 
  proof (cases "j - 1 = i")
    case True
    then have "j = i + 1"
      using Suc.prems(5) by linarith
    then have f1: "atomic_flag_val (snd (snd (exe_list!j))) = Some opid"
      using a7 by auto 
    then have f2: "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block \<or>
       (type_of_mem_op_block (pbm opid'') = ast_block \<and>
        atom_pair_id (pbm opid'') = Some opid)"
      using Suc(7) atomic_flag_exe1 by blast
    from a1 Suc(9) Suc(6) have "atom_pair_id (pbm opid'') \<noteq> Some opid"
      using ast_op_unique by auto
    then have "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block"
      using f2 by auto    
    then show ?thesis using f1 by auto
  next
    case False
    then have f3: "j-1 > i"
      using Suc(7) by auto 
    then have f003: "j > 0"
      by auto   
    from Suc(2) have f03: "x = (j-1) - i"  
      by auto
    from Suc(3) Suc(7) have f4: "j-1 < length exe_list - 1"
      by auto
    then obtain opid''' where 
      "(po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! j)) (snd (snd (exe_list ! j))))"          
      using a1 unfolding valid_mem_exe_seq_def mem_state_trans_def
      by (metis (no_types, lifting) add.commute add_diff_inverse_nat f3 gr_implies_not_zero nat_diff_split_asm)
    then have f05: "(po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! ((j-1)+1))) (snd (snd (exe_list ! ((j-1)+1)))))"
      using f003 by auto
    then have f5: "i < j-1 \<and> j-1 < (List.length exe_list - 1) \<and>
      (po pbm opid''' \<turnstile>m (fst (exe_list ! (j-1))) (snd (snd (exe_list ! (j-1)))) \<rightarrow>
                      (fst (exe_list ! ((j-1)+1))) (snd (snd (exe_list ! ((j-1)+1)))))"
      using f3 Suc(7) f003 by auto
    from a1 f4 Suc(4) f5 Suc(5) have f6: "opid''' \<noteq> opid"
      using valid_exe_op_exe_pos_unique False
      by (metis One_nat_def Suc_eq_plus1) 
    from f5 have f5_1: "opid''' = ((fst (List.last exe_list))!(j-1))"      
      using a1 valid_exe_op_exe_pos3 by blast 
    then have f5_2: "List.member (fst (List.last exe_list)) opid'''"
      using f5 a1 in_set_member valid_exe_xseq_sublist_length2 by fastforce 
    then have f7: "opid''' \<noteq> opid'"
      using a9 by auto
    from f6 f7 have f8: "opid \<noteq> opid''' \<and> opid''' \<noteq> opid'"
      by auto
    have f9: "(type_of_mem_op_block (pbm opid''') = ld_block \<or> 
               type_of_mem_op_block (pbm opid''') = o_block) \<and>
              atomic_flag_val (snd (snd (exe_list ! (j-1)))) = Some opid"
      using Suc(1)[OF f03 a1 Suc(4) Suc(5) Suc(6) f5 Suc(8) f8 a9] by auto
    then have "atomic_flag_val (snd (snd (exe_list ! ((j-1)+1)))) = Some opid"
      using atomic_flag_exe2 f05 by auto
    then have f10: "atomic_flag_val (snd (snd (exe_list ! j))) = Some opid"
      using f003 by auto
    from Suc(7) have f11: "po pbm opid'' \<turnstile>m (fst (exe_list ! j)) (snd (snd (exe_list ! j))) \<rightarrow>
                    (fst (exe_list ! (j + 1))) (snd (snd (exe_list ! (j + 1))))"
      by auto
    have f12: "type_of_mem_op_block (pbm opid'') = ld_block \<or> 
       type_of_mem_op_block (pbm opid'') = o_block \<or>
       (type_of_mem_op_block (pbm opid'') = ast_block \<and>
        atom_pair_id (pbm opid'') = Some opid)"
      using atomic_flag_exe1[OF f11 f10] by auto
    have f13: "atom_pair_id (pbm opid'') \<noteq> Some opid"
      using ast_op_unique[OF a1] Suc(9) Suc(6) by auto
    from f12 f13 show ?thesis by (simp add: f10)
  qed
qed  
  
lemma atom_store_op_contra_violate_sub1: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = ast_block"
  and a3: "atom_pair_id (pbm opid) = Some opid_ald"  
  and a4: "List.member (fst (last exe_list)) opid_ald"
  and a5: "\<not>(List.member (fst (last exe_list)) opid)"
  and a6: "List.member (po (proc_of_op opid pbm)) opid"
shows "(atomic_flag_val (snd (snd (last exe_list)))) = atom_pair_id (pbm opid)"
proof -
  from a4 obtain i where f1: "i < length (fst (last exe_list)) \<and> 
    (fst (last exe_list))!i = opid_ald"
    by (meson list_mem_range)
  then have f2: "i < (List.length exe_list) - 1"
    using a1 valid_exe_xseq_sublist_length2 by auto    
  then have f3: "(po pbm opid_ald \<turnstile>m (fst (exe_list!i)) (snd (snd (exe_list!i))) \<rightarrow>
        (fst (exe_list!(i+1))) (snd (snd (exe_list!(i+1)))))"
    using a1 f1 valid_exe_op_exe_pos by auto           
  from a1 a2 a6 have f4: "(\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and> 
    type_of_mem_op_block (pbm opid') = ald_block \<and> atom_pair_id (pbm opid) = Some opid')"
    unfolding valid_mem_exe_seq_def valid_program_def by blast      
  then have f5: "(opid_ald ;po^(proc_of_op opid pbm) opid) \<and> 
    type_of_mem_op_block (pbm opid_ald) = ald_block"
    using a3 by auto
  from a2 a3 f1 f5 have f1_1: "(atom_pair_id (pbm opid) = Some opid_ald) \<and> 
           (type_of_mem_op_block (pbm opid_ald) = ald_block) \<and>
           (type_of_mem_op_block (pbm opid) = ast_block)" 
    by auto
  have f6: "atomic_flag_val (snd (snd (exe_list!i))) = None" 
    using mem_op_elim_atom_load_op[OF f3] f5
    by blast 
  have f7: "atomic_flag_val (snd (snd (exe_list!(i+1)))) = Some opid_ald"
    using atomic_flag_exe_ald[OF f3 f6] f5 by auto  
  show ?thesis 
  proof (cases "i = (List.length exe_list - 2)")
    case True
    then have "atomic_flag_val (snd (snd (exe_list!((List.length exe_list - 2)+1)))) = Some opid_ald"
      using f7 by auto
    then have "atomic_flag_val (snd (snd (exe_list!(List.length exe_list - 1)))) = Some opid_ald"
      by (metis Nat.add_0_right One_nat_def Suc_diff_Suc \<open>\<And>thesis. (\<And>i. i < length (fst (last exe_list)) \<and> fst (last exe_list) ! i = opid_ald \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a1 add_Suc_right gr_implies_not_zero length_0_conv length_greater_0_conv numeral_2_eq_2 valid_exe_xseq_sublist_length2 zero_less_diff)      
    then show ?thesis using a3
      using a1 last_conv_nth valid_mem_exe_seq_def by fastforce 
  next
    case False
    then have f2_0: "i < length exe_list - 2"
      using f2 by auto
    define j where "j \<equiv> length exe_list - 2"
    then have f8: "j < (List.length exe_list - 1)"
      using \<open>i < length exe_list - 2\<close> by linarith   
    then have f8_1: "j < length (fst (last exe_list))"
      using a1 valid_exe_xseq_sublist_length2 by auto
    have f8_2: "j = length (fst (last exe_list)) - 1"
      using j_def valid_exe_xseq_sublist_length2[OF a1] by auto
    have f9: "(po pbm ((fst (List.last exe_list))!j) \<turnstile>m (fst (exe_list!j)) 
      (snd (snd (exe_list!j))) \<rightarrow> (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"
      using valid_exe_op_exe_pos2[OF a1 f8] by auto 
    define opid_j where "opid_j \<equiv> ((fst (List.last exe_list))!j)"
    have f10: "non_repeat_list (fst (List.last exe_list))"
      using valid_mem_exe_seq_op_unique[OF a1] by auto
    then have f11: "opid_ald \<noteq> opid_j" 
      using f1 opid_j_def f8_1 False j_def unfolding non_repeat_list_def
      using nth_eq_iff_index_eq  
      by blast  
    have f12: "List.member (fst (List.last exe_list)) opid_j"
      using opid_j_def j_def
      using f8_1 in_set_member by fastforce 
    then have f13: "opid_j \<noteq> opid" using a5 by auto
    from f2_0 j_def f8 f9 opid_j_def have f13_1: "(i < j \<and> j < (List.length exe_list - 1) \<and> 
           (po pbm opid_j \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1))))))"
      by auto
    from f11 f13 have f13_2: "opid_ald \<noteq> opid_j \<and> opid_j \<noteq> opid"
      by auto
    from f13_1 have f13_3: "(po pbm opid_j \<turnstile>m (fst (exe_list!j)) (snd (snd (exe_list!j))) \<rightarrow>
             (fst (exe_list!(j+1))) (snd (snd (exe_list!(j+1)))))"
      by auto
    have f14: "atomic_flag_val (snd (snd (exe_list!j))) = Some opid_ald"
      using atom_exe_valid_type2[OF a1 f2 f3 f1_1 f13_1 f7 f13_2 a5] by auto
    have f15: "type_of_mem_op_block (pbm opid_j) = ld_block \<or> 
       type_of_mem_op_block (pbm opid_j) = o_block \<or>
       (type_of_mem_op_block (pbm opid_j) = ast_block \<and>
        atom_pair_id (pbm opid_j) = Some opid_ald)"
      using atomic_flag_exe1[OF f13_3 f14] by auto
    from a1 f13 a3 have "(atom_pair_id (pbm opid_j) \<noteq> Some opid_ald)"
      unfolding valid_mem_exe_seq_def valid_program_def by blast
    then have f15_1: "type_of_mem_op_block (pbm opid_j) = ld_block \<or> 
       type_of_mem_op_block (pbm opid_j) = o_block"
      using f15 by auto
    have "atomic_flag_val (snd (snd (exe_list!(j+1)))) = Some opid_ald"
      using atomic_flag_exe2[OF f13_3 f14 f15_1] by auto
    then have "atomic_flag_val (snd (snd (exe_list!(length exe_list - 1)))) = 
      Some opid_ald"
      using j_def
      by (metis One_nat_def Suc_diff_Suc \<open>\<And>thesis. (\<And>i. i < length (fst (last exe_list)) \<and> fst (last exe_list) ! i = opid_ald \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a1 add.right_neutral add_Suc_right f8_2 gr_implies_not0 length_0_conv length_greater_0_conv minus_nat.diff_0 valid_exe_xseq_sublist_length2) 
    then show ?thesis
      by (metis (full_types) a3 f2_0 last_conv_nth list.size(3) not_less_zero zero_diff) 
  qed    
qed  
  
lemma atom_store_op_contra_violate: 
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "type_of_mem_op_block (pbm opid) = ast_block"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"    
  and a5: "List.member (po (proc_of_op opid pbm)) opid"
  and a6: "\<not> (List.member (fst (last exe_list)) opid)"
  and a7: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
shows "\<exists>opid' opid''. (axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"   
proof -
  from a1 have f0: "valid_program po pbm" 
    unfolding valid_mem_exe_seq_def by auto
  from a7 have f0_1: "non_repeat_list (((fst (last exe_list))@[opid])@remainder)"
    unfolding op_seq_final_def by auto
  from a2 a3 have f1: "(atomic_flag_val (snd (snd (last exe_list)))) = None \<or>
       (atomic_flag_val (snd (snd (last exe_list)))) \<noteq> atom_pair_id (pbm opid) \<or>
       (\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<and>
                \<not> (List.member (fst (last exe_list)) opid'))"
    using atom_store_op_contra by auto
  from a1 a2 a5 have f2: "(\<exists>opid'. (opid' ;po^(proc_of_op opid pbm) opid) \<and> 
    type_of_mem_op_block (pbm opid') = ald_block \<and> atom_pair_id (pbm opid) = Some opid')"
    unfolding valid_mem_exe_seq_def valid_program_def by blast
  then obtain opid_ald where f3: "(opid_ald ;po^(proc_of_op opid pbm) opid) \<and> 
    type_of_mem_op_block (pbm opid_ald) = ald_block \<and> atom_pair_id (pbm opid) = Some opid_ald"
    using a3 by auto
  from f3 have f3_0: "(opid_ald ;po^(proc_of_op opid_ald pbm) opid)"
    using a1 unfolding valid_mem_exe_seq_def valid_program_def
    by metis 
  from f3 have f3_1: "atom_pair_id (pbm opid) = Some opid_ald"
    by auto
  have f3_2: "opid_ald \<noteq> opid"
    using f3 a2 by auto
  have f5_2: "List.member ((fst (last exe_list))@[opid]) opid"
      using in_set_member by fastforce
  show ?thesis 
  proof (cases "List.member (fst (last exe_list)) opid_ald")
    case True
    have f4_1: "(atomic_flag_val (snd (snd (last exe_list)))) = atom_pair_id (pbm opid)"
      using atom_store_op_contra_violate_sub1[OF a1 a2 f3_1 True a6 a5] by auto
    then obtain opid' where f1_1: "(opid' ;po^(proc_of_op opid pbm) opid) \<and>
                (type_of_mem_op_block (pbm opid') = ld_block \<or>
                 type_of_mem_op_block (pbm opid') = ald_block \<or>
                 type_of_mem_op_block (pbm opid') = st_block \<or> 
                 type_of_mem_op_block (pbm opid') = ast_block) \<and>
                \<not> (List.member (fst (last exe_list)) opid')"
      using f1 f3 by auto
    then have f1_2: "opid' \<noteq> opid"
      using prog_order_op_unique[OF f0] using f1_1 by auto
    then have f1_3: "\<not> List.member ((fst (last exe_list))@[opid]) opid'"
      using f1_1
      by (metis (mono_tags, hide_lams) in_set_member insert_iff list.simps(15) rotate1.simps(2) set_rotate1) 
    then have f1_4: "(opid' m<((fst (last exe_list))@[opid]) opid) = Some False"
      using f5_2 unfolding memory_order_before_def by auto
    from f1_1 have f1_5: "(opid' ;po^(proc_of_op opid' pbm) opid)"
      using f0 unfolding valid_program_def
      by metis 
    from f1_1 have f1_6: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block} \<or>
      type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
      by auto
    then show ?thesis 
    proof (rule disjE)
      assume a8: "type_of_mem_op_block (pbm opid') \<in> {ld_block, ald_block}"
      then have f8_1: "axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm"
        unfolding axiom_loadop_violate_def using f1_4 f1_5 by auto 
      then show ?thesis by auto
    next
      assume a9: "type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}"
      then have f9_1: "axiom_storestore_violate opid' opid po ((fst (last exe_list))@[opid]) pbm"
        unfolding axiom_storestore_violate_def using f1_4 f1_5 a2 by auto
      then show ?thesis by auto
    qed
  next
    case False
    then have f5_1: "\<not> List.member ((fst (last exe_list))@[opid]) opid_ald"
      using f3_2
      by (metis in_set_member rotate1.simps(2) set_ConsD set_rotate1)     
    from f5_1 f5_2 have f5_3: "(opid_ald m<((fst (last exe_list))@[opid]) opid) = Some False"
      unfolding memory_order_before_def by auto
    then have f5_4: "axiom_atomicity_violate opid_ald opid po ((fst (last exe_list))@[opid]) pbm"
      unfolding axiom_atomicity_violate_def using f3 a2 f3_0 by auto
    show ?thesis 
      using axiom_atomicity_violate_persist[OF f0 f5_4 f0_1] by auto
  qed
qed  
  
text {* The lemma below combines the *_contra_violate lemmas of all above operations. *}  
  
lemma mem_op_contra_violate:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
  and a3: "\<not> (\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> 
                          xseq' s'))"
shows "\<exists>opid' opid''. (axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
       (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
       (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
proof -
  have f0: "valid_program po pbm"
    using a2 unfolding op_seq_final_def by auto 
  have f1: "List.member (((fst (last exe_list))@[opid])@remainder) opid"
    using in_set_member by fastforce
  then have f2: "\<exists>p. List.member (po p) opid"   
    using a2 unfolding op_seq_final_def by auto
  then have f2_1: "List.member (po (proc_of_op opid pbm)) opid"
    using f0 unfolding valid_program_def by blast
  then have f3: "type_of_mem_op_block (pbm opid) \<in> {ld_block, st_block, ald_block, ast_block}"
    using a2 unfolding op_seq_final_def by auto
  have f4: "non_repeat_list ((fst (last exe_list) @ [opid]) @ remainder)"
    using a2 unfolding op_seq_final_def by auto
  then have f4_1: "non_repeat_list (fst (last exe_list) @ [opid])"
    using non_repeat_list_sublist by blast
  have af5_4: "(fst (last exe_list) @ [opid])!(length (fst (last exe_list) @ [opid]) - 1) = opid"
    by simp
  then have af5_5: "(fst (last exe_list) @ [opid])!(length (fst (last exe_list))) = opid"
    by simp    
  have f5: "\<not>(List.member (fst (last exe_list)) opid)"
  proof (rule ccontr)
    assume af5: "\<not>\<not>(List.member (fst (last exe_list)) opid)"
    then have af5_1: "List.member (fst (last exe_list)) opid"
      by auto
    then obtain i where af5_2: "i < length (fst (last exe_list)) \<and> 
      (fst (last exe_list))!i = opid"
      by (meson in_set_conv_nth in_set_member)
    then have af5_3: "i < length (fst (last exe_list)) \<and> 
      (fst (last exe_list) @ [opid])!i = opid"
      by (simp add: nth_append)          
    show False using f4_1 af5_3 af5_5 unfolding non_repeat_list_def
      using nth_eq_iff_index_eq
      by (metis (mono_tags, hide_lams) le0 length_append_singleton less_Suc_eq less_irrefl)      
  qed    
  then show ?thesis
  proof (cases "type_of_mem_op_block (pbm opid)")
    case ld_block
    obtain opid' where f6_1: "axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm"
      using load_op_contra_violate[OF a1 ld_block a3] by auto
    have "axiom_loadop_violate opid' opid po (((fst (last exe_list))@[opid])@remainder) pbm"
      using axiom_loadop_violate_persist[OF f0 f6_1 f4] by auto
    then show ?thesis by auto
  next
    case st_block
    obtain opid' opid'' where f7_1: "(axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_storestore_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm)"
      using store_op_contra_violate[OF a1 st_block a3 f5 a2] by auto
    then have f7_2: "(axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
               (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
               (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
    proof (rule disjE)
      assume af7_1: "axiom_loadop_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm"
      have "axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm"
        using axiom_loadop_violate_persist[OF f0 af7_1 f4] by auto
      then show ?thesis by auto
    next
      assume "axiom_storestore_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm \<or>
        axiom_atomicity_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm"
      then show ?thesis
      proof (rule disjE)
        assume af7_2: "axiom_storestore_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm"
        have "axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm"
          using axiom_storestore_violate_persist[OF f0 af7_2 f4] by auto
        then show ?thesis by auto
      next
        assume af7_3: "axiom_atomicity_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm"
        have "axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm"
          using axiom_atomicity_violate_persist[OF f0 af7_3 f4] by auto
        then show ?thesis by auto
      qed
    qed
    then show ?thesis by auto
  next
    case ald_block
    obtain opid' opid'' where f8_1: "(axiom_loadop_violate opid' opid'' po ((fst (last exe_list))@[opid]) pbm) \<or>
      (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
      (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
      using atom_load_op_contra_violate[OF a1 ald_block a3 f2_1 f5 a2] by auto
    then have f8_2: "(axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
      (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
      (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
    proof (rule disjE)
      assume af8_1: "axiom_loadop_violate opid' opid'' po (fst (last exe_list) @ [opid]) pbm"
      have "axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm"
        using axiom_loadop_violate_persist[OF f0 af8_1 f4] by auto
      then show ?thesis by auto
    next
      assume af8_2: "axiom_storestore_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm \<or>
        axiom_atomicity_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
      then show ?thesis by auto
    qed
    then show ?thesis by auto
  next
    case ast_block
    obtain opid' opid'' where f9_1: "(axiom_loadop_violate opid' opid po ((fst (last exe_list))@[opid]) pbm) \<or>
      (axiom_storestore_violate opid' opid po ((fst (last exe_list))@[opid]) pbm) \<or>
      (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
      using atom_store_op_contra_violate[OF a1 ast_block a3 f2_1 f5 a2] by auto
    then have "(axiom_loadop_violate opid' opid po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
      (axiom_storestore_violate opid' opid po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
      (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
    proof (rule disjE)
      assume af9_1: "axiom_loadop_violate opid' opid po (fst (last exe_list) @ [opid]) pbm"
      have "axiom_loadop_violate opid' opid po (((fst (last exe_list))@[opid])@remainder) pbm"
        using axiom_loadop_violate_persist[OF f0 af9_1 f4] by auto
      then show ?thesis by auto
    next 
      assume "axiom_storestore_violate opid' opid po (fst (last exe_list) @ [opid]) pbm \<or>
        axiom_atomicity_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
      then show ?thesis 
      proof (rule disjE)
        assume af9_2: "axiom_storestore_violate opid' opid po (fst (last exe_list) @ [opid]) pbm"
        have "axiom_storestore_violate opid' opid po (((fst (last exe_list))@[opid])@remainder) pbm"
          using axiom_storestore_violate_persist[OF f0 af9_2 f4] by auto
        then show ?thesis by auto
      next
        assume "axiom_atomicity_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
        then show ?thesis by auto  
      qed
    qed
    then show ?thesis by auto
  next
    case o_block
    then show ?thesis using f3 by auto
  qed
qed
  
lemma mem_op_exists:
  assumes a1: "valid_mem_exe_seq po pbm exe_list"
  and a2: "op_seq_final (((fst (last exe_list))@[opid])@remainder) po pbm"
  and a3: "\<forall>opid' opid''. (axiom_loadop opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<and>
       (axiom_storestore opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<and>
       (axiom_atomicity opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
shows "(\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> xseq' s'))"
proof (rule ccontr)
  assume a4: "\<not>(\<exists>xseq' s'. (po pbm opid \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list))) \<rightarrow> xseq' s'))"
  obtain opid' opid'' where f1: "(axiom_loadop_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
       (axiom_storestore_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm) \<or>
       (axiom_atomicity_violate opid' opid'' po (((fst (last exe_list))@[opid])@remainder) pbm)"
    using mem_op_contra_violate[OF a1 a2 a4] by auto  
  then show False 
  proof (rule disjE)
    assume a5: "axiom_loadop_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
    have f5_1: "\<not>(axiom_loadop opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm)"
      using axiom_loadop_violate_imp[OF a5] by auto
    then show ?thesis using a3 by auto
  next
    assume "axiom_storestore_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm \<or>
      axiom_atomicity_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
    then show ?thesis
    proof (rule disjE)
      assume a6: "axiom_storestore_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
      have f6_1: "\<not>(axiom_storestore opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm)"
        using axiom_storestore_violate_imp[OF a6] by auto
      then show ?thesis using a3 by auto
    next
      assume a7: "axiom_atomicity_violate opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm"
      have f7_1: "\<not>(axiom_atomicity opid' opid'' po ((fst (last exe_list) @ [opid]) @ remainder) pbm)"
        using axiom_atomicity_violate_imp[OF a7] by auto
      then show ?thesis using a3 by auto
    qed
  qed
qed  
  
text {* The definition of a valid initial execution. *}  
 
definition emp_ctl_reg:: "proc \<Rightarrow> control_register" where
"emp_ctl_reg p r \<equiv> 0"
  
definition emp_gen_reg:: "proc \<Rightarrow> general_register" where
"emp_gen_reg p r \<equiv> 0"

definition emp_mem:: "memory" where
"emp_mem addr \<equiv> None"

definition zero_mem:: "memory" where
"zero_mem addr \<equiv> Some 0"

definition emp_mem_ops:: "op_id \<Rightarrow> mem_op_state" where
"emp_mem_ops opid \<equiv> \<lparr>op_addr = None, op_val = None\<rparr>"

definition init_proc_exe_pos:: "proc \<Rightarrow> nat" where
"init_proc_exe_pos p \<equiv> 0"

definition init_proc_var:: "proc \<Rightarrow> sparc_proc_var" where
"init_proc_var p \<equiv> \<lparr>annul = False\<rparr>"

definition init_glob_var:: "global_var" where
"init_glob_var \<equiv> \<lparr>atomic_flag = None, atomic_rd = 0\<rparr>"

definition valid_initial_state:: "sparc_state" where
"valid_initial_state \<equiv> \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg, mem = emp_mem,
  mem_ops = emp_mem_ops, proc_exe_pos = init_proc_exe_pos, proc_var = init_proc_var,
  glob_var = init_glob_var, undef = False\<rparr>"  
  
definition valid_initial_state_zero_mem:: "sparc_state" where
"valid_initial_state_zero_mem \<equiv> \<lparr>ctl_reg = emp_ctl_reg, gen_reg = emp_gen_reg, mem = zero_mem,
  mem_ops = emp_mem_ops, proc_exe_pos = init_proc_exe_pos, proc_var = init_proc_var,
  glob_var = init_glob_var, undef = False\<rparr>"  

definition valid_initial_exe:: "program_order \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state)" where
"valid_initial_exe po \<equiv> ([], {opid. (\<exists>p. List.member (po p) opid)}, valid_initial_state)"
  
definition valid_initial_exe_zero_mem:: "program_order \<Rightarrow> 
  (executed_mem_ops \<times> (op_id set) \<times> sparc_state)" where
"valid_initial_exe_zero_mem po \<equiv> ([], {opid. (\<exists>p. List.member (po p) opid)}, 
  valid_initial_state_zero_mem)"

lemma valid_initial_exe_seq: "valid_program po pbm \<Longrightarrow> 
  valid_mem_exe_seq po pbm [valid_initial_exe po]"
  unfolding valid_mem_exe_seq_def valid_initial_exe_def valid_initial_state_def
    atomic_flag_val_def init_glob_var_def
  by auto

lemma operational_model_complete_sub1: 
  assumes a1: "op_seq_final op_seq po pbm"    
  and a2: "(\<forall>opid opid'. axiom_loadop opid opid' po op_seq pbm)"
  and a3: "(\<forall>opid opid'. axiom_storestore opid opid' po op_seq pbm)"
  and a4: "(\<forall>opid opid'. axiom_atomicity opid opid' po op_seq pbm)"
  and a5: "is_sublist op_sub_seq op_seq"
  and a6: "op_sub_seq \<noteq> []"
shows "(\<exists>exe_list. valid_mem_exe_seq po pbm exe_list \<and> (fst (List.last exe_list)) = op_sub_seq)"   
proof (insert assms, induction op_sub_seq rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have f0: "valid_program po pbm"
    using a1 unfolding op_seq_final_def by auto
  show ?case 
  proof (cases "xs = []")
    case True
    then have f1_1: "x = hd op_seq"
      using snoc(6) unfolding is_sublist_def by auto 
    then obtain remainder where f1_2: "op_seq = [x]@remainder"     
      by (metis True append_self_conv2 is_sublist_def snoc.prems(5))          
    from f0 have f1_3: "valid_mem_exe_seq po pbm [valid_initial_exe po]"
      using valid_initial_exe_seq by auto
    have f1_4: "(fst (last [valid_initial_exe po])) = []"
      unfolding valid_initial_exe_def by auto
    then have f1_4_1: "op_seq = (((fst (last [valid_initial_exe po]))@[x])@remainder)"
      using f1_2 by auto
    have f1_5: "op_seq_final (((fst (last [valid_initial_exe po]))@[x])@remainder) po pbm"
      using a1 f1_4_1 by auto
    have f1_6: "\<forall>opid' opid''.
     axiom_loadop opid' opid'' po ((fst (last [valid_initial_exe po]) @ [x]) @ remainder) pbm \<and>
     axiom_storestore opid' opid'' po ((fst (last [valid_initial_exe po]) @ [x]) @ remainder) pbm \<and>
     axiom_atomicity opid' opid'' po ((fst (last [valid_initial_exe po]) @ [x]) @ remainder) pbm"
      using a2 a3 a4 f1_4_1 by auto
    obtain xseq' s' where f1_7: "(po pbm x \<turnstile>m (fst (last [valid_initial_exe po])) 
      (snd (snd (last [valid_initial_exe po]))) \<rightarrow> xseq' s')"
      using mem_op_exists[OF f1_3 f1_5 f1_6] by auto
    then have f1_8: "(po pbm x \<turnstile>m (fst (valid_initial_exe po)) 
      (snd (snd (last [valid_initial_exe po]))) \<rightarrow> [x] s')"
      using mem_op_exe f1_4 by fastforce
    have f1_9: "(\<exists>p. List.member (po p) x)"
      using op_seq_final_def f1_1
      using in_set_member snoc.prems(1) by fastforce 
    have f1_10: "x \<in> (fst (snd (valid_initial_exe po)))"
      unfolding valid_initial_exe_def using f1_9 by auto
    have f1_11: "po pbm \<turnstile>t (valid_initial_exe po) \<rightarrow> 
      ([x], ((fst (snd (valid_initial_exe po))) - {x}), s')"
      unfolding mem_state_trans_def using f1_8 f1_10 by auto
    have f1_12: "length ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')]) > 0"
      by simp
    have f1_13: "fst (List.hd ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])) = []"
      using f1_4 by auto
    have f1_14: "(\<forall>opid. (\<exists>p. List.member (po p) opid) = 
      (opid \<in> fst (snd (List.hd ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])))))"
      using f1_3 unfolding valid_mem_exe_seq_def by auto
    have f1_15: "(atomic_flag_val (snd (snd (hd ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])))) = None)"
      using f1_3 unfolding valid_mem_exe_seq_def by auto
    have f1_16: "(\<forall>i. i < (List.length ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])) - 1 \<longrightarrow> 
       (po pbm \<turnstile>t (([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])!i) \<rightarrow> (([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])!(i+1))))"
      using f1_11 by auto
    have f1_17: "valid_mem_exe_seq po pbm ([valid_initial_exe po]@
      [([x], ((fst (snd (valid_initial_exe po))) - {x}), s')])"
      using f0 f1_12 f1_13 f1_14 f1_15 f1_16 unfolding valid_mem_exe_seq_def 
      by auto
    then show ?thesis using True by auto      
  next
    case False
    have f2_1: "is_sublist xs op_seq"
      using snoc(6) unfolding is_sublist_def by auto
    obtain exe_list where f2_2: "valid_mem_exe_seq po pbm exe_list \<and> fst (last exe_list) = xs"
      using snoc(1)[OF a1 snoc(3) snoc(4) snoc(5) f2_1 False] by auto
    then have f2_2_1: "valid_mem_exe_seq po pbm exe_list"
      by auto
    obtain remainder where f2_3: "((fst (last exe_list))@[x])@remainder = op_seq"
      using snoc(6) f2_2 unfolding is_sublist_def by auto
    have f2_4: "op_seq_final (((fst (last exe_list))@[x])@remainder) po pbm"
      using a1 f2_3 by auto
    have f2_5: "\<forall>opid' opid''. (axiom_loadop opid' opid'' po (((fst (last exe_list))@[x])@remainder) pbm) \<and>
       (axiom_storestore opid' opid'' po (((fst (last exe_list))@[x])@remainder) pbm) \<and>
       (axiom_atomicity opid' opid'' po (((fst (last exe_list))@[x])@remainder) pbm)"
      using a2 a3 a4 f2_3 by auto
    obtain xseq' s' where f2_6: "po pbm x \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list)))
      \<rightarrow> xseq' s'"
      using mem_op_exists[OF f2_2_1 f2_4 f2_5] by auto
    then have f2_7: "po pbm x \<turnstile>m (fst (last exe_list)) (snd (snd (last exe_list)))
      \<rightarrow> ((fst (last exe_list))@[x]) s'"
      using mem_op_exe by auto
    have f2_8: "(set (fst (last exe_list))) \<union> (fst (snd (last exe_list))) = 
       (fst (snd (hd exe_list)))"
      using valid_exe_xseq_sublist_last[OF f2_2_1] by auto
    have f2_9: "non_repeat_list (((fst (last exe_list))@[x])@remainder)"
      using a1 f2_3 unfolding op_seq_final_def by auto
    then have f2_10: "\<not>(List.member (fst (last exe_list)) x)"
      by (simp add: non_repeat_list_sublist_mem) 
    have f2_11: "(\<exists>p. List.member (po p) x)"
      using op_seq_final_def f2_3 in_set_member snoc.prems(1) by fastforce 
    then have f2_12: "x \<in> fst (snd (List.hd exe_list))"
      using f2_2_1 unfolding valid_mem_exe_seq_def by auto
    then have f2_13: "x \<in> (fst (snd (last exe_list)))"
      using f2_8 f2_10 in_set_member by fastforce 
    then have f2_14: "po pbm \<turnstile>t (last exe_list) \<rightarrow> (((fst (last exe_list))@[x]),
      ((fst (snd (last exe_list))) - {x}), s')"
      unfolding mem_state_trans_def using f2_7 by auto
    define exe_list' where "exe_list' \<equiv> exe_list@[(((fst (last exe_list))@[x]),
      ((fst (snd (last exe_list))) - {x}), s')]"
    have f2_14_1: "po pbm \<turnstile>t (last exe_list) \<rightarrow> (last exe_list')"
      using f2_14 exe_list'_def by auto
    have f2_15: "List.length exe_list' > 0"
      using exe_list'_def by auto
    have f2_16: "fst (List.hd exe_list') = []"
      using exe_list'_def f2_2_1 unfolding valid_mem_exe_seq_def
      by simp
    have f2_17: "(\<forall>opid. (\<exists>p. List.member (po p) opid) = 
      (opid \<in> fst (snd (List.hd exe_list'))))"
      using exe_list'_def f2_2_1 unfolding valid_mem_exe_seq_def
      by simp
    have f2_18: "(atomic_flag_val (snd (snd (hd exe_list'))) = None)"
      using exe_list'_def f2_2_1 unfolding valid_mem_exe_seq_def
      by simp
    have f2_19: "(\<forall>i. i < (List.length exe_list') - 1 \<longrightarrow> 
       (po pbm \<turnstile>t (exe_list'!i) \<rightarrow> (exe_list'!(i+1))))"
    proof -
      {fix i
        have "i < (List.length exe_list') - 1 \<longrightarrow> (po pbm \<turnstile>t (exe_list'!i) \<rightarrow> (exe_list'!(i+1)))"
        proof (cases "i < (List.length exe_list') - 2")
          case True
          then have f2_19_1: "i < (List.length exe_list) - 1"
            unfolding exe_list'_def by auto
          then have f2_19_2: "(po pbm \<turnstile>t (exe_list!i) \<rightarrow> (exe_list!(i+1)))"
            using f2_2_1 unfolding valid_mem_exe_seq_def by auto
          then have f2_19_3: "(po pbm \<turnstile>t (exe_list'!i) \<rightarrow> (exe_list'!(i+1)))"
            using True unfolding exe_list'_def
            by (metis add_lessD1 f2_19_1 less_diff_conv nth_append)          
          then show ?thesis by auto
        next
          case False          
          show ?thesis 
          proof (auto)
            assume f2_19_4: "i < length exe_list' - Suc 0"
            then have f2_19_5: "i = length exe_list' - 2"
              using False by auto            
            show "po pbm \<turnstile>t (exe_list' ! i) \<rightarrow> (exe_list' ! Suc i)" 
              using f2_14_1 f2_19_5 unfolding exe_list'_def
              by (metis (no_types, lifting) Nat.add_0_right One_nat_def Suc_diff_Suc add_Suc_right append_is_Nil_conv butlast_snoc diff_diff_left exe_list'_def f2_19_4 f2_2 last_conv_nth length_butlast length_greater_0_conv nth_append numeral_2_eq_2 valid_mem_exe_seq_def)              
          qed  
        qed
      }
      then show ?thesis by auto
    qed
    have f2_20: "valid_mem_exe_seq po pbm exe_list'"
      using f0 f2_15 f2_16 f2_17 f2_18 f2_19 unfolding valid_mem_exe_seq_def
      by auto
    then show ?thesis unfolding exe_list'_def using f2_2 by auto 
  qed  
qed
  
text {* The theorem below shows the completeness proof. *}
  
theorem operational_model_complete_sub2: 
  "op_seq_final op_seq po pbm \<Longrightarrow> 
   (\<forall>opid opid'. axiom_loadop opid opid' po op_seq pbm) \<Longrightarrow> 
   (\<forall>opid opid'. axiom_storestore opid opid' po op_seq pbm) \<Longrightarrow>
   (\<forall>opid opid'. axiom_atomicity opid opid' po op_seq pbm) \<Longrightarrow> 
   (\<exists>exe_list. valid_mem_exe_seq po pbm exe_list \<and> (fst (List.last exe_list)) = op_seq)"  
proof -
  assume a1: "op_seq_final op_seq po pbm"
  assume a2: "(\<forall>opid opid'. axiom_loadop opid opid' po op_seq pbm)"
  assume a3: "(\<forall>opid opid'. axiom_storestore opid opid' po op_seq pbm)"
  assume a4: "(\<forall>opid opid'. axiom_atomicity opid opid' po op_seq pbm)"  
  have f1: "is_sublist op_seq op_seq"
    unfolding is_sublist_def by auto
  have f2: "op_seq \<noteq> []"
    using a1 unfolding op_seq_final_def by auto
  show ?thesis 
    using operational_model_complete_sub1[OF a1 a2 a3 a4 f1 f2] by auto
qed  
  
theorem operational_model_complete: 
  "op_seq_final op_seq po pbm \<Longrightarrow> 
   (\<forall>opid opid'. axiom_loadop opid opid' po op_seq pbm) \<Longrightarrow> 
   (\<forall>opid opid'. axiom_storestore opid opid' po op_seq pbm) \<Longrightarrow>
   (\<forall>opid opid'. axiom_atomicity opid opid' po op_seq pbm) \<Longrightarrow> 
   (\<exists>exe_list. valid_mem_exe_seq_final po pbm exe_list \<and> (fst (List.last exe_list)) = op_seq)"    
proof -
  assume a1: "op_seq_final op_seq po pbm"
  assume a2: "(\<forall>opid opid'. axiom_loadop opid opid' po op_seq pbm)"
  assume a3: "(\<forall>opid opid'. axiom_storestore opid opid' po op_seq pbm)"
  assume a4: "(\<forall>opid opid'. axiom_atomicity opid opid' po op_seq pbm)"
  then obtain exe_list where f1: "valid_mem_exe_seq po pbm exe_list \<and> 
    (fst (List.last exe_list)) = op_seq"  
    using operational_model_complete_sub2[OF a1 a2 a3 a4] by auto
  then have f1_1: "List.length exe_list > 0"
    unfolding valid_mem_exe_seq_def by auto
  from a1 have f2: "(\<forall>opid. (\<exists>p. List.member (po p) opid) = (List.member op_seq opid))"
    unfolding op_seq_final_def by auto
  from f1 have f3: "(\<forall>opid. (\<exists>p. List.member (po p) opid) = (opid \<in> fst (snd (List.hd exe_list))))"
    unfolding valid_mem_exe_seq_def by auto
  from f2 f3 have f4: "\<forall>opid. (List.member op_seq opid) = (opid \<in> fst (snd (List.hd exe_list)))"
    by auto
  then have f5: "\<forall>opid. (List.member (fst (List.last exe_list)) opid) = 
    (opid \<in> fst (snd (List.hd exe_list)))"
    using f1 by auto
  then have f6: "\<forall>opid. (opid \<in> fst (snd (List.hd exe_list))) =
    (opid \<in> set (fst (List.last exe_list)))"
    by (simp add: in_set_member)    
  then have f7: "fst (snd (List.hd exe_list)) = set (fst (List.last exe_list))"
     by auto
  show ?thesis using f1 f7 unfolding valid_mem_exe_seq_final_def by auto
qed  
  
end  
theory gen_code_model 
imports Main Memory_Model  
begin   

text {* Equality for comprenhensive sets on list elements *}

definition set_list_P::"'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set"
  where
"set_list_P xs P \<equiv> set (filter P xs)"

definition exists_list::"'a list  \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where
"exists_list xs P\<equiv> ((set_list_P xs P) \<noteq> {})"

definition forall_list::"'a list  \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"forall_list xs P \<equiv> (-(set_list_P xs P) = {})"

definition forall_rest_list::"'a list  \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"forall_rest_list xs P Q \<equiv> set_list_P xs P \<subseteq> set_list_P xs Q"

definition THE_list::"'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a"
  where
"THE_list xs P \<equiv> if (card (set_list_P xs P) = 1) then (filter P xs)!0
                 else undefined"


lemma subset_P_xs_eq_set_P_list_P:"{a. P a} \<subseteq> (set xs) \<Longrightarrow> 
       {a. P a} = (set_list_P xs P)"
  unfolding set_list_P_def 
  by auto

lemma exists_list:
  "{a. P a} \<subseteq> (set xs) \<Longrightarrow>
   (\<exists>x. P x) = exists_list xs P"
  using subset_P_xs_eq_set_P_list_P 
  unfolding exists_list_def by fastforce

lemma forall_list:
  "{a. P a } \<subseteq> (set xs) \<Longrightarrow>
   (\<forall>x. P x) = forall_list xs P"
  using subset_P_xs_eq_set_P_list_P unfolding forall_list_def
  by blast
    
lemma forall_rest_list:
  "{a. P a } \<subseteq> (set xs) \<Longrightarrow>   
   (\<forall>x. P x \<longrightarrow> Q x) = (forall_rest_list xs P Q)"
  using subset_P_xs_eq_set_P_list_P unfolding forall_rest_list_def set_list_P_def
  by fastforce

lemma finite_P:
     "P x \<Longrightarrow> \<forall>y y'. P y \<and> P y' \<longrightarrow> y = y' \<Longrightarrow>
      finite {a. P a}"
  using nat_seg_image_imp_finite
  by (metis Collect_mem_eq Collect_mono finite.insertI finite_subset insertCI)


 lemma card_P:
 "P x \<Longrightarrow> \<forall>y y'. P y \<and> P y' \<longrightarrow> y = y' \<Longrightarrow>
  card {a. P a} = Suc 0"
   using is_singleton_altdef
   by (metis (full_types) One_nat_def empty_Collect_eq is_singletonI' mem_Collect_eq)

lemma THE_list:
  "{a. P a} \<subseteq> (set xs) \<Longrightarrow>
   Ex1 P \<Longrightarrow>
   (THE x. P x) = THE_list xs P"
  using  the1_equality[of P]  subset_P_xs_eq_set_P_list_P[of P xs] card_P
  unfolding THE_list_def
  by (metis (mono_tags, lifting) One_nat_def card_length le_numeral_extra(2) mem_Collect_eq neq0_conv nth_mem set_list_P_def)  
  
subsection {* new definitions for code generation *}  
text {* A new version of memory_order_before for code export. *}

definition list_before3:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"list_before3 x l y \<equiv> length (takeWhile (\<lambda>e. e\<noteq>x) l) \<noteq> length l \<and> 
                       List.member (drop ((length (takeWhile (\<lambda>e. e\<noteq>x) l)) + 1) l) y "  
  
definition program_order_before2:: "op_id \<Rightarrow> program_order \<Rightarrow> proc \<Rightarrow> op_id \<Rightarrow> bool" 
 ("_ 2;_^_ _") where
"op1 2;po^p op2 \<equiv> list_before3 op1 (po p) op2" 
  
  
definition memory_order_before2:: "op_id \<Rightarrow> executed_mem_ops \<Rightarrow> op_id \<Rightarrow> 
  bool option" ("_ m<2_ _") where
"op1 m<2xseq op2 \<equiv> 
  if (List.member xseq op1) \<and> (List.member xseq op2) then
    if list_before3 op1 xseq op2 then Some True
    else Some False
  else if List.member xseq op1 then Some True
  else if List.member xseq op2 then Some False
  else None" 

definition axiom_order2:: "op_id \<Rightarrow> op_id \<Rightarrow> executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> bool" where
"axiom_order2 opid opid' xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and> 
   (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
   (opid \<in> (set xseq) \<and> 
    opid' \<in> (set xseq) \<and> opid \<noteq> opid')) \<longrightarrow> 
  ((opid m<2xseq opid') = Some True \<or> (opid' m<2xseq opid) = Some True)"

  
definition axiom_atomicity2:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_atomicity2 opid opid' po xseq pbm \<equiv> 
  ((atom_pair_id (pbm opid') = Some opid) \<and> 
   (type_of_mem_op_block (pbm opid) = ald_block) \<and>
   (type_of_mem_op_block (pbm opid') = ast_block) \<and>
   (opid 2;po^(proc_of_op opid pbm) opid')) \<longrightarrow> 
  (((opid m<2xseq opid') = Some True) \<and> 
  (forall_rest_list xseq 
     (\<lambda>opid''. (type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block}) \<and> 
               List.member xseq opid'' \<and> \<comment>\<open> opid'' \<noteq> opid is true because their types are different. \<close>
              opid'' \<noteq> opid') 
     (\<lambda>opid''. (opid'' m<2xseq opid) = Some True \<or> (opid' m<2xseq opid'') = Some True) ))"  

definition axiom_storestore2:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_storestore2 opid opid' po xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
   (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
   (opid 2;po^(proc_of_op opid pbm) opid')) \<longrightarrow>
  (opid m<2xseq opid') = Some True"

  
definition axiom_termination2:: "op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_termination2 opid po xseq pbm \<equiv> 
 ( exists_list [0..<(Suc max_proc)]  (\<lambda>p . List.member (po  p) opid \<and> p<(Suc max_proc)) \<and>
  (type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block})) \<longrightarrow>
  List.member xseq opid"  

definition max_mem_order1:: "op_id set \<Rightarrow> op_id set \<Rightarrow> proc \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  op_id option" where
"max_mem_order1 opids1 opids2 p po xseq \<equiv> 
let max_po = (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid)))) in
  let max_m = (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True))) in
  if opids1 \<noteq> {} \<or> opids2 \<noteq>{}  then
    if opids1 = {} then  Some max_po
    else if opids2 = {} then Some max_m 
         else (if max_po \<in> opids1 then Some max_m 
               else Some max_po)
  else None"  

definition max_mem_order2:: "op_id set \<Rightarrow> op_id set \<Rightarrow> proc \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  op_id option" where
"max_mem_order2 opids1 opids2 p po xseq \<equiv> 
let max_po = THE_list (po p) 
                   (\<lambda>opid. opid\<in> opids2 \<and> 
                   forall_rest_list (po p)  (\<lambda>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'.(opid' 2;po^p opid))) in
  let max_m = THE_list xseq 
                   (\<lambda>opid. opid\<in> opids1 \<and> 
                   forall_rest_list xseq  (\<lambda>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'. (opid' m<2xseq opid) = Some True)) in
  if opids1 \<noteq> {} \<or> opids2 \<noteq>{}  then
    if opids1 = {} then  Some max_po
    else if opids2 = {} then Some max_m 
         else (if max_po \<in> opids1 then Some max_m 
               else Some max_po)
  else None"  

definition axiom_value_sub1 
  where
 "axiom_value_sub1 opid pbm addr state xseq \<equiv> 
      (\<lambda>opid'. (opid' m<2xseq opid) = Some True \<and> 
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state))"

definition axiom_value2_sub1 
  where
"axiom_value2_sub1 opid pbm addr state xseq \<equiv> 
   set_list_P xseq (axiom_value_sub1 opid pbm addr state xseq)"

definition axiom_value_sub2
  where
 "axiom_value_sub2 opid pbm addr state po p \<equiv> 
      (\<lambda>opid'. (opid' 2;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state))"    

definition axiom_value2_sub2 
  where
"axiom_value2_sub2 opid pbm addr state po p \<equiv> 
   set_list_P (po p) (axiom_value_sub2 opid pbm addr state po p)"  

definition axiom_value2:: "proc \<Rightarrow> op_id \<Rightarrow> virtual_address \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> 
  sparc_state \<Rightarrow> memory_value option" where
"axiom_value2 p opid addr po xseq pbm state \<equiv> 
  case (max_mem_order2 (axiom_value2_sub1 opid pbm addr state xseq)  
                        (axiom_value2_sub2 opid pbm addr state po p) p po xseq) of
  Some opid''' \<Rightarrow> op_val (get_mem_op_state opid''' state)
  |None \<Rightarrow> None"  

definition axiom_loadop2:: "op_id \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> 
  program_block_map \<Rightarrow> bool" where
"axiom_loadop2 opid opid' po xseq pbm \<equiv> 
  ((type_of_mem_op_block (pbm opid) \<in> {ld_block, ald_block}) \<and>
   (opid 2;po^(proc_of_op opid pbm) opid')) \<longrightarrow> 
             (opid m<2xseq opid') = Some True"


definition load_value2:: "proc \<Rightarrow> virtual_address \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> 
  executed_mem_ops \<Rightarrow> program_block_map \<Rightarrow> sparc_state \<Rightarrow> memory_value option" where  
"load_value2 p addr opid po xseq pbm state \<equiv> 
  case ((mem_most_recent_store addr xseq pbm state),(proc_most_recent_store p addr opid po pbm state)) of 
  (Some s1, Some s2) \<Rightarrow> (case (s1 m<2xseq s2) of 
    Some True \<Rightarrow> op_val (get_mem_op_state s2 state)
    |Some False \<Rightarrow> op_val (get_mem_op_state s1 state)
    |None \<Rightarrow> None)
  |(None, Some s2) \<Rightarrow> op_val (get_mem_op_state s2 state)
  |(Some s1, None) \<Rightarrow> op_val (get_mem_op_state s1 state)
  |(None, None) \<Rightarrow> None"  

    
definition non_repeat_list_pos2 ::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"non_repeat_list_pos2 x l \<equiv> if distinct l \<and> x\<in> set l then 
                              (length l) - length (dropWhile (\<lambda>a. a\<noteq>x) l)
                             else undefined" 

lemma non_repeat_list_pos2_x:"distinct l \<Longrightarrow>
       x\<in>set l \<Longrightarrow>
       l!((length l) - length (dropWhile (\<lambda>a. a\<noteq>x) l)) = x"
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l) 
  {assume asm:"a = x" 
    then have ?case using Cons by auto}
  moreover{assume "a\<noteq>x" then have ?case using Cons
    proof -
      have f1: "dropWhile (\<lambda>a. a \<noteq> x) (a # l) = dropWhile (\<lambda>a. a \<noteq> x) l"
        using \<open>a \<noteq> x\<close> by auto
      have f2: "x \<in> set l"
        using \<open>a \<noteq> x\<close> \<open>x \<in> set (a # l)\<close> by auto
      have "length (a # l) - length (dropWhile (\<lambda>a. a \<noteq> x) (a # l)) \<noteq> 0"
        using f1 by (metis (no_types) diff_add_inverse diff_add_inverse2 length_Cons length_append lessI minus_eq not_add_less2 takeWhile_dropWhile_id)
      then show ?thesis
        using f2 Cons.hyps \<open>distinct (a # l)\<close> by auto
    qed
  }     
  ultimately show ?case by auto
qed
  
lemma non_repeat_pos_less_lenl:"x\<in>set l \<Longrightarrow> ((length l) - length (dropWhile (\<lambda>a. a\<noteq>x) l)) < length l"
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    using length_pos_if_in_set by auto 
qed

lemma non_repeat_list_code_equal: "distinct l \<Longrightarrow>
      x\<in>set l \<Longrightarrow>                 
       non_repeat_list_pos x l = non_repeat_list_pos2 x l" 
  unfolding non_repeat_list_pos2_def non_repeat_list_pos_def non_repeat_list_def    
proof-
  assume a0: "distinct l"  and
    a1:"x\<in>set l"
  then have "\<exists>!n. distinct l \<and> n < length l \<and> l ! n = x"
    unfolding Ex1_def by (metis  distinct_Ex1 ) 
  then show  "(THE n. distinct l \<and> n < length l \<and> l ! n = x) =
    (if distinct l \<and> x \<in> set l then length l - length (dropWhile (\<lambda>a. a \<noteq> x) l)
     else undefined)" 
        using non_repeat_list_pos2_x[OF a0 a1] 
             non_repeat_pos_less_lenl[OF a1] a0 a1 by auto
qed

subsection {*equality between definitions *}

subsubsection {*equality list_before *}  
  
lemma list_before_code1: 
  assumes a0:"length (takeWhile (\<lambda>e. e \<noteq> x) l) \<noteq> length l" and
         a1: "List.member (drop (Suc (length (takeWhile (\<lambda>e. e \<noteq> x) l))) l) y" 
  shows "\<exists>i<length l. \<exists>j<length l. l ! i = x \<and> l ! j = y \<and> i < j"
proof-
  have len_take_while:"length (takeWhile (\<lambda>e. e \<noteq> x) l) < length l"
    using a0
    by (simp add: le_neq_implies_less length_takeWhile_le)
  then have "l!(length (takeWhile (\<lambda>e. e \<noteq> x) l)) = x"
    using nth_length_takeWhile by auto  
  moreover obtain j where j:"l!j = y \<and> j< length l \<and> length (takeWhile (\<lambda>e. e \<noteq> x) l)< j "
    using a1 len_take_while calculation
    by (smt Suc_leI le_add_diff_inverse length_drop lessI less_imp_le_nat list_mem_range 
            nat_add_left_cancel_less nth_drop trans_less_add1)
   ultimately show ?thesis  using len_take_while by fastforce
qed
    
lemma list_before_code2:"j < length l \<Longrightarrow>
       x = l ! i \<Longrightarrow> i < j \<Longrightarrow> y = l ! j \<Longrightarrow> 
       length (takeWhile (\<lambda>e. e \<noteq> l ! i) l) = length l \<Longrightarrow> False"
  by (metis (full_types) dual_order.strict_trans nth_equalityI 
        nth_mem takeWhile_eq_all_conv takeWhile_nth)     

lemma list_before_code3:
 assumes a0:"j < length l" and
    a1:"x = l ! i" and
    a2:"i < j" and a3:"y = l ! j" 
   shows "List.member (drop (Suc (length (takeWhile (\<lambda>e. e \<noteq> l ! i) l))) l) (l ! j)"
proof-
  have f1:"Suc (length (takeWhile (\<lambda>e. e \<noteq> l ! i) l))\<le>j" 
    using suc_length_take_while_less_j[OF a0 a1 a2 a3] by auto
  thus ?thesis using a0 all_drop_eq[OF f1 a0]
    by (metis diff_less_mono length_drop member_def nth_mem)
qed   
  
lemma list_before_code_equal: "list_before3 x l y = list_before x l y"
  unfolding list_before3_def list_before_def
  by (auto elim: list_before_code1 list_before_code2 list_before_code3 )
 
subsubsection {*equality program_order_before *}      
    
lemma program_order_before_code_equal: "(op1 2;po^p op2) = (op1 ;po^p op2)"
  unfolding     program_order_before2_def program_order_before_def 
  using list_before_code_equal by fastforce
    
subsubsection {*equality memory_order_before *}
    
lemma memory_order_before_code_equal: "(op1 m<2xseq op2) = (op1 m<xseq op2)"
using list_before_code_equal unfolding memory_order_before2_def memory_order_before_def by fastforce

subsubsection {*equality axiom_order *}  
lemma axiom_order_code_export: "axiom_order2 opid opid' xseq pbm = axiom_order opid opid' xseq pbm"
  using memory_order_before_code_equal unfolding axiom_order_def axiom_order2_def by auto  
  

subsubsection {*equality axiom_atomicity *}
  
lemma members_in_set:"{a. (\<lambda>opid''.
          type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and>
          List.member xseq opid'' \<and> opid'' \<noteq> opid') a} \<subseteq> (set xseq)"
  using in_set_member by fastforce 

lemma in_set_member_eq_filter_list:"{a. (\<lambda>opid''.
            type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and>
            List.member xseq opid'' \<and> opid'' \<noteq> opid') a} = 
          set_list_P xseq (\<lambda>a. a\<in>{a. (\<lambda>opid''.
          type_of_mem_op_block (pbm opid'') \<in> {st_block, ast_block} \<and>
           opid'' \<noteq> opid') a})"
  unfolding set_list_P_def
  by (auto simp add: in_set_member)
 

lemma axiom_atomicity_code_equal: "axiom_atomicity2 opid opid' po xseq pbm =
  axiom_atomicity opid opid' po xseq pbm"
  unfolding axiom_atomicity_def axiom_atomicity2_def 
  by (simp only: memory_order_before_code_equal program_order_before_code_equal
      forall_rest_list[OF members_in_set])

subsubsection {*equality axiom_storestore *}      
lemma axiom_storestore_code_equal: "axiom_storestore2 opid opid' po xseq pbm =
  axiom_storestore opid opid' po xseq pbm"
  unfolding axiom_storestore2_def axiom_storestore_def
   using program_order_before_code_equal memory_order_before_code_equal
   by auto      
     
 subsubsection {*equality axiom_storestore *}     
lemma eq_axiom_termination: "axiom_termination opid po xseq pbm = axiom_termination2 opid po xseq pbm" 
  unfolding axiom_termination_def axiom_termination2_def 
  using exists_list[of "\<lambda>p. List.member (po  p) opid \<and> p<(Suc max_proc)" "[0..<(Suc max_proc)]"]
  by fastforce   
    

subsubsection {*equality axiom_max_mem_order *}   
lemma xseq_po:
  assumes a0:"distinct (po p)" and
 a0':"distinct (xseq) " and
 a1:"List.member (po p) opid" and
 a2:"List.member (po p) opid'" and
 a3:"(opid m<xseq opid') = Some True" and
 a4:"(type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
      (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block})" and        
 a5:" (\<forall>opid opid'. 
         ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
          (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
          ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True)" 
shows "( opid  ;po^p opid')"
proof-
  have "opid\<noteq>opid'" 
    using a0' a3 mem_order_not_sym by blast
  then have "(opid  ;po^p opid') \<or> (opid'  ;po^p opid)"
    using a1 a2
    by (simp add: list_elements_before program_order_before_def) 
  moreover have "\<not> ((opid' m<xseq opid) = Some True)" 
    using mem_order_not_sym[OF a0' a3] by auto 
  ultimately show ?thesis using a4 a5
    by blast 
qed


lemma unique_value_no_opids1: 
  assumes 
  a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a4:"opids1 = {}" and
  a5:"opids2\<noteq>{}" and
  a7:"distinct (po p) \<and> distinct (xseq)" and
  a8: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and
   x:"x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"   
 shows
   "\<forall>x''. x''\<in>opids \<and> 
     (\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))) \<longrightarrow>
       x''= x"
proof-
{fix x''
  assume b0:"x''\<in>opids" and
         b1:"\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))"      
  {assume assm:"x'' \<noteq> x"
    then have "\<not>(x ;po^p  x'')" 
      using x a0 a4 b0 a7 unfolding program_order_before_def
      by (metis list_before_not_sym sup_bot.left_neutral)
    moreover have  "\<not>(x m<xseq x'') = Some True"
    proof-
      have  "type_of_mem_op_block (pbm x) \<in> {st_block, ast_block}"
        using x a2
        by fastforce
      moreover have "type_of_mem_op_block (pbm x'') \<in> {st_block, ast_block}"
        using a0 b0  a1 a2
        by fastforce
      moreover have  "x'' ;po^p  x"
        using  x a0 a4 b0 assm by blast
      ultimately have " (x'' m<xseq x) = Some True"
        using a8  by auto
      then show ?thesis using  a7
        using mem_order_not_sym by blast            
    qed            
    ultimately have "x''=x" using b1 b0 a0 a4
      using x by auto
   }
   moreover {assume "x'' = x" }
   ultimately have "x=x''" by auto
} thus ?thesis by auto
qed

lemma  noxseq_max_max_po:  assumes
  a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"res = max_mem_order opids p po xseq" and
  a4:"opids1 = {}" and
  a5:"opids2\<noteq>{}" and
  a6:"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a7:"distinct (po p) \<and> distinct (xseq)" and
  a8: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True"
shows "res = max_po"
proof-
  have "opids2 \<subseteq> {x. list_before x (po p) opid}" 
    using a2 unfolding program_order_before_def by auto
  then have Ex:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"
    using exists_unique_list_before_lb[of "po p"] a7 a5 unfolding program_order_before_def 
    by auto  
  moreover obtain x where x:" x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))" 
    using calculation by auto
  ultimately have max_po:"max_po=Some x" using a6  
     the1_equality[OF Ex x] by meson
  have  x_ex:"x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow>  ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"
    using x a0 a4 by auto
  then have Ex':"\<exists>!x. x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow> ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"
    using unique_value_no_opids1[OF a0 a1 a2 a4 a5 a7 a8 x] unfolding Ex1_def
    by auto
  then have "max_mem_order opids p po xseq = 
              Some (THE opid. (opid \<in> opids \<and>  
                    (\<forall>opid'. ((opid' \<in> opids \<and> opid' \<noteq> opid) \<longrightarrow>
                             ((opid' m<xseq opid) = Some True \<or> 
                              (opid' ;po^p opid))))))"
    using a0 a5 a3 unfolding max_mem_order_def by auto
  then have "max_mem_order opids p po xseq = Some x"
    using  the1_equality[OF Ex' x_ex]   
    apply auto
    by meson    
  then show ?thesis using max_po a3  by auto    
qed



lemma ld_not_xseq_after_not_xseq:  
  assumes   
  a0:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> 
                 (opid m<xseq opid') = Some True" and
  a1:"\<not> (List.member xseq opid)"
shows  "\<forall>opid'. (opid ;po^p opid') \<longrightarrow> \<not> (List.member xseq opid')"
proof-
  show ?thesis using a0 a1 
    using mem_order_true_cond_equiv by auto
qed


lemma po_after_load_not_opids1:  
  assumes 
  a0:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and    
  a1:"distinct (xseq)" and
  a2:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" 
shows  "\<forall>opid'. (opid ;po^p opid') \<longrightarrow> 
         opid' \<notin> opids1"
  using  a0 a1 a2 mem_order_not_sym by blast

lemma po_after_load_not_opids:  
  assumes 
  a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and     
  a3:"distinct (xseq)" and a4: "distinct (po p)" and
  a5:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" 
shows  "\<forall>opid'. (opid ;po^p opid') \<longrightarrow> opid' \<notin> opids"
proof-
  have "\<forall>opid'. (opid ;po^p opid') \<longrightarrow> opid' \<notin> opids1" 
    using po_after_load_not_opids1[OF a1 a3 a5] by auto
  moreover have "\<forall>opid'. (opid ;po^p opid') \<longrightarrow> opid' \<notin> opids2"
    using a2 a3 unfolding program_order_before_def
    by (metis (no_types, lifting) a4 list_before_not_sym mem_Collect_eq) 
  ultimately show ?thesis using a0 by auto
qed


lemma unique_value_all_opids2_in_opid1: 
  assumes 
  a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a4:"distinct (po p) \<and> distinct (xseq)" and  
  a5: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and
  a6:"x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)" and   
  a3:"\<forall>xid2\<in>opids2. xid2\<in>opids1"  
   
 shows
   "\<forall>x''. x''\<in>opids \<and> 
     (\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))) \<longrightarrow>
       x''= x"
proof-
{fix x''
  assume b0:"x''\<in>opids" and
         b1:"\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))"  
  { assume assm0:"x'' \<noteq> x"    
     then have h:"(x m<xseq x'') = Some False" using a6 a3 a0 
       by (metis Un_iff a4 b0 mem_order_not_sym memory_order_before_def) 
     moreover have "\<not>(x ;po^p  x'')"
     proof-
       {assume "(x ;po^p  x'')"
        then have "(x m<xseq x'') = Some True" using a5 b0 a0 a1 a2 a6
          by blast
        then have False using h by auto} thus ?thesis by auto
     qed  
    ultimately have "x'' = x" using b0 b1 assm0 a6 a0 by fastforce      
  }       
  moreover {assume "x'' = x" }    
  ultimately have "x=x''" by auto      
} thus ?thesis by auto
qed

lemma nopo_max_xseq:  
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"res = max_mem_order opids p po xseq" and
  a4:"opids1\<noteq> {}" and
  a5:"opids2 = {}" and
  a6:"max_xseq = Some (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)))" and
  a7:"distinct (po p) \<and> distinct (xseq)" and
  a8: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a9:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" 
shows  "res = max_xseq"
proof-
  have "opids1 \<subseteq> {x. List.member xseq x}" 
    using a1 mem_order_true_cond by auto 
  then have Ex:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)"
    using exists_unique_mem_order_list a7 a4  
    by auto
  moreover obtain x where x:" x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)" 
    using calculation by auto
  ultimately have max_po:"max_xseq=Some x" using a6  
     the1_equality[OF Ex x] by meson
  have  x_ex:"x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow>  ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"
    using x a0 a5 by auto  
  have Ex':"\<exists>!x. x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow> ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"
    using unique_value_all_opids2_in_opid1[OF a0 a1 a2 a7 a8 x] using a5  x_ex 
    unfolding Ex1_def
    by auto
  then have "max_mem_order opids p po xseq = 
              Some (THE opid. (opid \<in> opids \<and>  
                    (\<forall>opid'. ((opid' \<in> opids \<and> opid' \<noteq> opid) \<longrightarrow>
                             ((opid' m<xseq opid) = Some True \<or> 
                              (opid' ;po^p opid))))))"
    using a0 a5 a3 unfolding max_mem_order_def by auto
  then have "max_mem_order opids p po xseq = Some x"
    using  the1_equality[OF Ex' x_ex]   
    apply auto
    by meson    
  then show ?thesis using max_po a3  by auto 
qed


lemma all_opids2_in_opid1:
assumes  
  a0:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a1:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and  
  a2:"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a3:"distinct (po p) \<and> distinct (xseq)" and
  a4: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a5:"the max_po \<in> opids1" and  
  a6:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"
  shows "\<forall>xid2\<in>opids2. xid2\<in>opids1"
proof-
  {fix xid2'
    assume ass0:"xid2'\<in>opids2"
   obtain xid2 where xid2:" xid2\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>xid2 \<longrightarrow>  (x' ;po^p  xid2))" 
    using a6 by auto
   then have max_po:"max_po=Some xid2" using a2  
     the1_equality[OF a6 xid2] by meson
   then have xid2_opids1:"xid2\<in>opids1" using a5 by auto
   moreover {assume "xid2'\<noteq>xid2"
     then have "(xid2' ;po^p  xid2)" using ass0 xid2 by auto
     then have xid2'_l_xid2:"(xid2' m<xseq xid2) = Some True" using a4 ass0 xid2 a1
       by blast
     then have "(xid2' m<xseq opid) = Some True" 
       using xid2_opids1 a0 memory_order_before_tran a3 by blast         
     then have " xid2'\<in>opids1" using ass0 a1 a0 by auto
   } 
   ultimately have "xid2'\<in>opids1" by auto
  } thus ?thesis by auto  
qed

lemma max_mem_in_opids:  
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and    
  a3:"max_xseq = Some (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)))" and
  a4:"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a5:"distinct (po p) \<and> distinct (xseq)" and
  a6: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and
  a7:"the max_po \<in> opids1" and
  a8:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)" and
  a9:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"
shows "(the max_xseq)\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>(the max_xseq) \<longrightarrow>  (x' m<xseq (the max_xseq)) = Some True)"
proof-
  obtain xid1 where xid1:" xid1\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>xid1 \<longrightarrow>  (x' m<xseq xid1) = Some True)" 
    using a8 by auto
  then have max_xseq:"max_xseq=Some xid1" using a3  
     the1_equality[OF a8 xid1] by meson
  then have "(the max_xseq)\<in>opids" using xid1 a0 by auto
  obtain xid2 where xid2:" xid2\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>xid2 \<longrightarrow>  (x' ;po^p  xid2))" 
    using a9 by auto
  then have max_po:"max_po=Some xid2" using a4  
     the1_equality[OF a9 xid2] by meson
  then have "xid2\<in>opids1" using a7 by auto
  then have opid2_in_opid1:"\<forall>xid2'\<in>opids2. xid2'\<in>opids1" 
    using all_opids2_in_opid1[OF a1 a2 a4 a5 a6 a7 a9] by auto
  have "xid1\<in>opids" using a0 xid1 by auto
  moreover have "(\<forall>x'\<in>opids. x'\<noteq>xid1 \<longrightarrow>  (x' m<xseq xid1) = Some True)"
    using opid2_in_opid1 a0 xid1 by blast 
  ultimately show ?thesis using max_xseq by auto
qed


lemma max_nopo_in_opids:  
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"res = max_mem_order opids p po xseq" and
  a4:"opids1\<noteq> {}" and
  a5:"opids2 \<noteq> {}" and
  a6:"max_xseq = Some (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)))" and
  a6':"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a7:"distinct (po p) \<and> distinct (xseq)" and
  a8: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a9:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" and 
  a12:"the max_po \<in> opids1"   
shows  "res = max_xseq"
proof-
  have "opids1 \<subseteq> {x. List.member xseq x}" 
    using a1 mem_order_true_cond by auto 
  then have Ex:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)"
    using exists_unique_mem_order_list a7 a4  
    by auto
  moreover obtain xid1 where x1:" xid1\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>xid1 \<longrightarrow>  (x' m<xseq xid1) = Some True)" 
    using calculation by auto
  ultimately have max_xseq:"max_xseq=Some xid1" using a6  
     the1_equality[OF Ex x1] by meson 
  have opids2_subset:"opids2 \<subseteq> {x. (x ;po^p opid)}" using a2 by auto 
  then have Ex2:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"  
    using a7 a5 exists_unique_list_before_lb[of "po p"]  unfolding program_order_before_def
      by auto      
  note l1 =  max_mem_in_opids[OF a0 a1 a2 a6 a6' a7 a8 a12 Ex Ex2] 
  then have h:"the max_xseq \<in> opids \<and> 
              (\<forall>x'\<in>opids. x' \<noteq> the max_xseq \<longrightarrow> (x' m<xseq (the max_xseq)) = Some True \<or> (x' ;po^p (the max_xseq)) )"
    by auto
  moreover have "\<forall>xid2\<in>opids2. xid2 \<in> opids1" using all_opids2_in_opid1[OF a1 a2 a6' a7 a8]
    using a12 Ex2 by blast 
  then have "\<forall>x''. x''\<in>opids \<and> 
     (\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))) \<longrightarrow>
       x''=the max_xseq" using unique_value_all_opids2_in_opid1[OF a0 a1 a2  a7 a8 x1] max_xseq
    by auto
  ultimately have Ex':"\<exists>!x. x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow> ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"    
    unfolding Ex1_def by auto
  then have "max_mem_order opids p po xseq = 
              Some (THE opid. (opid \<in> opids \<and>  
                    (\<forall>opid'. ((opid' \<in> opids \<and> opid' \<noteq> opid) \<longrightarrow>
                             ((opid' m<xseq opid) = Some True \<or> 
                              (opid' ;po^p opid))))))"
    using a0 a5 a3 unfolding max_mem_order_def by auto
  then have "max_mem_order opids p po xseq = Some xid1"
    using  the1_equality[OF Ex' h] max_xseq  
    apply auto
    by metis    
  then show ?thesis using max_xseq a3 by auto
qed
  
lemma max_op_in_opids:  
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and    
  a3:"max_xseq = Some (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)))" and
  a4:"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a5:"distinct (po p) \<and> distinct (xseq)" and
  a6: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and
  a7:"the max_po \<notin> opids1" and
  a8:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)" and
  a9:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"
shows "(the max_po)\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>(the max_po) \<longrightarrow> (x' m<xseq (the max_po)) = Some True \<or> (x' ;po^p (the max_po)))"
proof-
  obtain xid1 where xid1:" xid1\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>xid1 \<longrightarrow>  (x' m<xseq xid1) = Some True)" 
    using a8 by auto
  then have max_xseq:"max_xseq=Some xid1" using a3  
     the1_equality[OF a8 xid1] by meson
  obtain xid2 where xid2:" xid2\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>xid2 \<longrightarrow>  (x' ;po^p  xid2))" 
    using a9 by auto
  then have max_po:"max_po=Some xid2" using a4  
     the1_equality[OF a9 xid2] by meson
  then have "(the max_po)\<in>opids" using xid2 a0 by auto
  moreover have "(\<forall>x'\<in>opids. x'\<noteq>xid2 \<longrightarrow> (x' m<xseq xid2) = Some True \<or>  (x' ;po^p  xid2))"
  proof-
  {fix x'
    assume assm:"x' \<in> opids" and not_xid2:"x'\<noteq>xid2"
    {assume "x'\<notin>opids2"
      then have x'_opids1:"x'\<in>opids1" using a0 assm by auto
      then have x'_xseq:"List.member xseq x'" 
        using a1 mem_order_true_cond_equiv by auto 
      {assume "\<not> List.member xseq xid2" 
        then have "(x' m<xseq xid2) = Some True" 
          using x'_xseq unfolding memory_order_before_def  by auto
      }
      moreover {assume "List.member xseq xid2" 
       then have "(x' m<xseq xid2) = Some True \<or> (xid2 m<xseq x') = Some True" 
         using x'_xseq
         by (meson list_elements_before mem_order_true_cond_rev not_xid2)
       moreover {
         assume "(xid2 m<xseq x') = Some True"
         then have "(xid2 m<xseq opid) = Some True" 
           using memory_order_before_tran a5 a1 x'_opids1 by blast
         then have "(x' m<xseq xid2) = Some True" 
           using a7 max_po xid2 a2 
           by (simp add: a1)
       } 
       ultimately have "(x' m<xseq xid2) = Some True" by auto
      }
     ultimately have "(x' m<xseq xid2) = Some True" by auto
    }
    moreover {assume "x'\<in>opids2"
     then have "(x' ;po^p  xid2)" using xid2 not_xid2  by fastforce
    }    
    ultimately have "(x' m<xseq xid2) = Some True \<or> (x' ;po^p  xid2)" by auto  
  }thus ?thesis by auto
  qed
  ultimately show ?thesis using max_po by auto
qed  

lemma x_not_opid:
assumes a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"distinct (po p) \<and> distinct (xseq)" and
  a4:"x\<in>opids"
shows " x\<noteq>opid"
proof-  
  {assume "x\<in>opids1" 
    then have ?thesis using a1 a3 mem_order_not_sym by blast 
  }
  moreover{assume "x\<in>opids2"
    then have ?thesis using a2 a3 unfolding program_order_before_def
      using list_before_not_sym by fastforce  
  }
  ultimately show ?thesis using a4 a0 by auto
qed


lemma x_not_in_opids1:
assumes a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a4:"distinct (po p) \<and> distinct (xseq)" and  
  a7:"x\<notin>opids1" and
  a9:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" and
  a8:"x\<in>opids"
shows "\<not> (List.member xseq x) \<or> (opid m<xseq x) = Some True"
proof-
  have "\<not>(x m<xseq opid) = Some True" using a0 a1 a2 a8 a7 by blast   
  then have "\<not> (List.member xseq x) \<or> (List.member xseq x \<and> List.member xseq opid \<and> \<not> list_before x xseq opid)"
    unfolding memory_order_before_def by presburger  
  moreover {assume "(List.member xseq x \<and> List.member xseq opid \<and> \<not> list_before x xseq opid)"

    then have "List.member xseq x \<and> List.member xseq opid \<and> list_before opid xseq x"
      using x_not_opid[OF a0 a1 a2 a4 a8] not_list_before_members_eq_or_inv
      by fastforce
    then have "(opid m<xseq x) = Some True" unfolding memory_order_before_def by auto
  } 
  ultimately show ?thesis by blast
qed
  
  
lemma unique_value_x_in_opdi1_opdi2: 
  assumes 
  a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a4:"distinct (po p) \<and> distinct (xseq)" and  
  a5: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and
  a6:"x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True \<or> (x'  ;po^p x))" and
  a6':"x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))" and
  a7:"x\<notin>opids1" and
  a9:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" 
 shows
   "\<forall>x''. x''\<in>opids \<and> 
     (\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))) \<longrightarrow>
       x''= x"
proof-
{fix x''
  assume b0:"x''\<in>opids" and
         b1:"\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))"  
  { assume assm0:"x'' \<noteq> x"
    have x:"\<not> (List.member xseq x) \<or> (opid m<xseq x) = Some True"
      using x_not_in_opids1[OF a0 a1 a2 a4 a7 a9] a6 by auto
    {assume assm1:"x''\<in>opids2"
      then have "\<not> (x ;po^p  x'')" using a6' a7 a0 a1
        by (metis a4 list_before_not_sym program_order_before_def)
      moreover have "(x m<xseq x'') = Some False"
        using a6' a5 assm1  a4 mem_order_not_sym
        by (metis (no_types, lifting) a2 a6 assm0 b1 mem_Collect_eq)
      ultimately have "x=x''" using b1 a0 a6 by auto
    }
    moreover {assume assm1:"x''\<notin>opids2"
      then have x''_in_opdis1: "x'' \<in> opids1" using a0 b0 by auto
      then have h:"(x m<xseq x'') = Some False" 
      proof-
      {          
        {assume "\<not> (List.member xseq x)"
          then have ?thesis using a4 a6 assm0 b0 b1 list_before_not_sym mem_order_true_cond_equiv
          by (metis memory_order_before_def program_order_before_def) 
        }
        moreover {assume "(opid m<xseq x) = Some True"     
          moreover have "(x'' m<xseq opid)= Some True" using x''_in_opdis1 a1 by auto
          ultimately have "(x'' m<xseq x)= Some True" using a4 memory_order_before_tran by blast
          then have ?thesis using a4 mem_order_not_sym[]
            by (metis mem_order_true_cond_rev memory_order_before_def) 
        }         
        ultimately have "(x m<xseq x'') = Some False" using x by auto 
      }thus ?thesis by auto        
      qed        
      moreover have "\<not>(x ;po^p  x'')"
      proof-
       {assume "(x ;po^p  x'')"
        then have "(x m<xseq x'') = Some True" using a5 b0 a0 a1 a2 a6
          by blast
        then have False using h by auto} thus ?thesis by auto
      qed  
      ultimately have "x'' = x" using b0 b1 assm0 a6 a0 by fastforce      
    } ultimately   have "x'' = x" by auto
  }
  moreover {assume "x'' = x" }    
  ultimately have "x=x''" by auto      
} thus ?thesis by auto
qed  
  
lemma max_nopo_not_in_opids:  
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"res = max_mem_order opids p po xseq" and
  a4:"opids1\<noteq> {}" and
  a5:"opids2 \<noteq> {}" and
  a6:"max_xseq = Some (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids1 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)))" and
  a6':"max_po = Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))" and
  a7:"distinct (po p) \<and> distinct (xseq)" and
  a8: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a9:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True" and 
  a12:"the max_po \<notin> opids1"   
shows  "res = max_po"
proof-
  have "opids1 \<subseteq> {x. List.member xseq x}" 
    using a1 mem_order_true_cond by auto 
  then have Ex:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'\<in>opids1. x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)"
    using exists_unique_mem_order_list a7 a4  
    by auto
  have opids2_subset:"opids2 \<subseteq> {x. (x ;po^p opid)}" using a2 by auto 
  then have Ex2:"\<exists>!x. x\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>x \<longrightarrow>  (x' ;po^p  x))"  
    using a7 a5 exists_unique_list_before_lb[of "po p"]  unfolding program_order_before_def
    by auto   
  moreover obtain xid2 where x2:" xid2\<in>opids2 \<and> (\<forall>x'\<in>opids2. x'\<noteq>xid2 \<longrightarrow>  (x' ;po^p  xid2))"
    using calculation by auto
  ultimately have max_po:"max_po=Some xid2" using a6'
     the1_equality[OF Ex2 x2] by meson
  note l1 =  max_op_in_opids[OF a0 a1 a2 a6 a6' a7 a8 a12 Ex Ex2]     
  then have h:"\<forall>x''. x''\<in>opids \<and> 
     (\<forall>x'\<in>opids. x'\<noteq>x'' \<longrightarrow>  ((x' m<xseq x'') = Some True \<or> (x' ;po^p  x''))) \<longrightarrow>
       x''=the max_po" 
    using unique_value_x_in_opdi1_opdi2[OF a0 a1 a2 a7 a8 l1 _ a12 a9] max_po x2
    by (metis option.sel)
  then have Ex':"\<exists>!x. x\<in>opids \<and> (\<forall>x'\<in>opids. x'\<noteq>x \<longrightarrow> ((x' m<xseq x) = Some True \<or> (x' ;po^p  x)))"    
    using l1 unfolding Ex1_def by auto
  then have "max_mem_order opids p po xseq = 
              Some (THE opid. (opid \<in> opids \<and>  
                    (\<forall>opid'. ((opid' \<in> opids \<and> opid' \<noteq> opid) \<longrightarrow>
                             ((opid' m<xseq opid) = Some True \<or> 
                              (opid' ;po^p opid))))))"
    using a0 a5 a3 unfolding max_mem_order_def by auto
  then have "max_mem_order opids p po xseq = Some xid2"
    using  the1_equality[OF Ex' l1] max_po 
    apply auto
    by metis    
  then show ?thesis using max_po a3 by auto
qed

lemma eq_max_mem_order_1: 
  assumes
 a0:"opids = opids1 \<union> opids2" and
  a1:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a3:"distinct (po p) \<and> distinct (xseq)" and
  a4: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a5:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True"
shows "max_mem_order opids p po xseq = max_mem_order1 opids1 opids2 p po xseq"
proof-
  {assume "opids1 = {}" and "opids2 ={}"
    then have ?thesis unfolding max_mem_order_def max_mem_order1_def using a0 by auto
  }
  moreover {assume opids1:"opids1 \<noteq> {}" and opids2:"opids2 = {}"    
    then have ?thesis        
      using nopo_max_xseq[OF a0 a1 a2 _ _ _ _ a3 a4 a5 ] a0 
      unfolding max_mem_order_def  max_mem_order1_def Let_def by auto
  }
  moreover {assume opids1:"opids1 = {}" and opids2:"opids2 \<noteq> {}"    
    then have ?thesis        
      using noxseq_max_max_po[OF a0 a1 a2 _ _ _ _ a3 a4 ] a0 
      unfolding max_mem_order_def  max_mem_order1_def Let_def by auto
  }
  moreover {assume opids1:"opids1 \<noteq> {}" and opids2:"opids2 \<noteq> {}"    
    {assume "the (Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))) \<in> opids1"
     then have ?thesis        
      using max_nopo_in_opids[OF a0 a1 a2 _ _ _ _ _ a3 a4 a5] a0 opids1 opids2 
      unfolding max_mem_order_def  max_mem_order1_def Let_def by auto
    }
    moreover {assume "the (Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))) \<notin> opids1"
     then have ?thesis        
      using max_nopo_not_in_opids[OF a0 a1 a2 _ _ _ _ _ a3 a4 a5] a0 opids1 opids2 
      unfolding max_mem_order_def  max_mem_order1_def Let_def by auto
    }ultimately have ?thesis by auto  
  }
  ultimately show ?thesis by auto
qed

lemma eq_max_mem_order_2:
assumes a0:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a1:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"distinct (po p)" and a3:"distinct xseq"
shows "max_mem_order1 opids1 opids2 p po xseq = max_mem_order2 opids1 opids2 p po xseq"
proof-
  
  have subset_pop:"{opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid)))} \<subseteq>
        set (po p)"
    using a1 unfolding program_order_before_def list_before_def 
    by auto  
  have subset_xseq:"{opid. opid\<in> opids1 \<and> 
           (\<forall>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid \<longrightarrow> 
                    (opid' m<xseq opid) = Some True))} \<subseteq> set xseq"
    using a0 mem_order_true_cond unfolding List.member_def by auto    
  
  have forall_opids1:"\<forall>opid. (\<forall>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)) = 
                forall_rest_list xseq  (\<lambda>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'. (opid' m<2xseq opid) = Some True)"
  proof-
    {fix opid
    have P_set:"{opid'. opid' \<in> opids1 \<and> opid'\<noteq>opid} \<subseteq> set (xseq)"
      using a0 mem_order_true_cond unfolding List.member_def by auto    
    have "(\<forall>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid \<longrightarrow> 
                             (opid' m<xseq opid) = Some True)) = 
                forall_rest_list xseq  (\<lambda>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'. (opid' m<2xseq opid) = Some True)" 
      using forall_rest_list[OF P_set] memory_order_before_code_equal by auto}
    thus ?thesis by auto
  qed  
    
  have forall_opids2:"\<forall>opid. (\<forall>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid \<longrightarrow> 
                             (opid' ;po^p opid))) = 
                forall_rest_list (po p)  (\<lambda>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'. (opid' 2;po^p opid))"
  proof-
    {fix opid
    have P_set:"{opid'. opid' \<in> opids2 \<and> opid'\<noteq>opid} \<subseteq> set (po p)"
      using a1 list_before_in_list 
      unfolding program_order_before_def List.member_def by auto   
    have "(\<forall>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid \<longrightarrow> 
                             (opid' ;po^p opid))) = 
                forall_rest_list (po p)  (\<lambda>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'.(opid' 2;po^p opid))" 
      using forall_rest_list[OF P_set] program_order_before_code_equal by auto}
    thus ?thesis by auto
  qed    
 
  have THE_opids2:"opids2 \<noteq>{} \<Longrightarrow>
        (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid)))) = 
        THE_list (po p) 
                   (\<lambda>opid. opid\<in> opids2 \<and> 
                   forall_rest_list (po p)  (\<lambda>opid'. (opid' \<in> opids2 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'.(opid' 2;po^p opid)))"
  proof-
    assume assm:"opids2\<noteq>{}"
    have h1:"opids2 \<subseteq> {x. list_before x (po p) opid}" 
       using a1 unfolding program_order_before_def by blast
    have ex:"\<exists>!opid.
     opid \<in> opids2 \<and> (\<forall>opid'. opid' \<in> opids2 \<and> opid' \<noteq> opid \<longrightarrow> (opid' ;po^p opid))"
      using exists_unique_list_before_lb[OF a2 h1 assm] a1
      unfolding program_order_before_def by blast      
    show ?thesis using THE_list[OF subset_pop ] ex forall_opids2 by auto
  qed
    
  have THE_opids1:"opids1 \<noteq>{} \<Longrightarrow>
        (THE opid. opid\<in> opids1 \<and> 
                   (\<forall>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid \<longrightarrow> 
                             (opid' m<xseq opid) = Some True))) = 
        THE_list xseq 
                   (\<lambda>opid. opid\<in> opids1 \<and> 
                   forall_rest_list xseq  (\<lambda>opid'. (opid' \<in> opids1 \<and> opid' \<noteq> opid))
                                 (\<lambda>opid'. (opid' m<2xseq opid) = Some True))"
  proof-
    assume assm:"opids1\<noteq>{}"
    have h1:"opids1 \<subseteq> {x. List.member xseq x}" 
      using a0 mem_order_true_cond by auto
    then have ex:"\<exists>!x. x\<in>opids1 \<and> (\<forall>x'. x' \<in>opids1 \<and> x'\<noteq>x \<longrightarrow>  (x' m<xseq x) = Some True)"
      using exists_unique_mem_order_list[OF a3 _ assm]  
       by blast
    then show ?thesis using THE_list[OF subset_xseq ex] forall_opids1 by auto
  qed                                     
    

  {assume "opids1 = {}" and "opids2 ={}"
    then have ?thesis unfolding max_mem_order1_def max_mem_order2_def  by auto
  }
  moreover {assume opids1:"opids1 \<noteq> {}" and opids2:"opids2 = {}"        
    then have ?thesis using THE_opids1[OF opids1]   
      unfolding max_mem_order1_def max_mem_order2_def Let_def by auto        
      
  }
  moreover {assume opids1:"opids1 = {}" and opids2:"opids2 \<noteq> {}"    
    then have ?thesis using THE_opids2[OF opids2]   
      unfolding max_mem_order1_def max_mem_order2_def Let_def by auto  
  }
  moreover {assume opids1:"opids1 \<noteq> {}" and opids2:"opids2 \<noteq> {}"    
    {assume "the (Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))) \<in> opids1"
     then have ?thesis        
      using THE_opids1[OF opids1]   
      unfolding max_mem_order1_def max_mem_order2_def Let_def
      by (simp add: THE_opids2)
    }
    moreover {assume "the (Some (THE opid. opid\<in> opids2 \<and> 
                   (\<forall>opid'. ((opid' \<in> opids2 \<and> opid' \<noteq> opid) \<longrightarrow> 
                             (opid' ;po^p opid))))) \<notin> opids1"
     then have ?thesis        
      using THE_opids1[OF opids1]   
      unfolding max_mem_order1_def max_mem_order2_def Let_def
      by (simp add: THE_opids2)
    }ultimately have ?thesis by auto  
  }
  ultimately show ?thesis by auto
qed

lemma max_mem_order_code_equal:
assumes a0:"opids1 = {opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)}" and
  a1:"opids2 = {opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)}" and
  a2:"distinct (po p)" and a3:"distinct xseq" and 
  a4: "\<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True" and 
  a5:"\<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True"
shows "max_mem_order (opids1 \<union> opids2) p po xseq = max_mem_order2 opids1 opids2 p po xseq"
  using  eq_max_mem_order_1[OF _ a0 a1 conjI[OF a2 a3] a4 a5] 
         eq_max_mem_order_2[OF a0 a1 a2 a3] by auto
        
lemma axiom_value_sub1_pred:
   "{opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)} = 
        {a. axiom_value_sub1 opid pbm addr state xseq a}"
  unfolding axiom_value_sub1_def using memory_order_before_code_equal by fastforce

lemma axiom_value_sub1_member:"{a. axiom_value_sub1 opid pbm addr state xseq a} \<subseteq> set xseq"
  unfolding axiom_value_sub1_def memory_order_before2_def member_def
    using memory_order_before_code_equal
  by auto    
    


 

  
lemma axiom_value2_sub1_eq:
    "{opid'. (opid' m<xseq opid) = Some True \<and> 
           (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
           Some addr = op_addr (get_mem_op_state opid' state)} =
       axiom_value2_sub1  opid pbm addr state xseq"  
  unfolding axiom_value2_sub1_def 
  using axiom_value_sub1_member subset_P_xs_eq_set_P_list_P axiom_value_sub1_pred
  by metis
    
  
lemma axiom_value_sub2_pred:
   "{opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)} = 
        {a. axiom_value_sub2 opid pbm addr state po p a}"
  unfolding axiom_value_sub2_def using program_order_before_code_equal
  by auto
    
lemma axiom_value_sub2_member:"{a. axiom_value_sub2 opid pbm addr state po p a} \<subseteq> set (po p)"
  unfolding axiom_value_sub2_def  member_def 
    using program_order_before_code_equal unfolding program_order_before_def list_before_def
  by auto

  

lemma axiom_value2_sub2_eq:
    "{opid'. (opid' ;po^p opid) \<and>
               (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
               Some addr = op_addr (get_mem_op_state opid' state)} =
       axiom_value2_sub2  opid pbm addr state po p"  
  unfolding axiom_value2_sub2_def 
  using axiom_value_sub2_member subset_P_xs_eq_set_P_list_P axiom_value_sub2_pred
  by metis
    
text {* A new version of axiom_value for code export. *}
    

lemma finite_axiom_value2_sub1:
  "finite (axiom_value2_sub1  opid pbm addr state xseq)"
 unfolding axiom_value2_sub1_def set_list_P_def by auto
 
lemma finite_axiom_value2_sub2:
  "finite (axiom_value2_sub2  opid pbm addr state po p)"
 unfolding axiom_value2_sub2_def set_list_P_def by auto
  
 

lemma axiom_value_code_export: 
"distinct (po p) \<Longrightarrow> distinct xseq \<Longrightarrow>
 \<forall>opid opid'. 
       ((type_of_mem_op_block (pbm opid) \<in> {st_block, ast_block}) \<and>
       (type_of_mem_op_block (pbm opid') \<in> {st_block, ast_block}) \<and> 
       ( opid  ;po^p opid')) \<longrightarrow>
       (opid m<xseq opid') = Some True \<Longrightarrow>
  \<forall>opid'. (opid ;po^p opid') \<longrightarrow> (opid m<xseq opid') = Some True \<Longrightarrow>
  axiom_value2 p opid addr po xseq pbm state =
  axiom_value p opid addr po xseq pbm state"
  using axiom_value2_sub2_eq axiom_value2_sub1_eq max_mem_order_code_equal
        finite_axiom_value2_sub2 finite_axiom_value2_sub1
  unfolding axiom_value2_def axiom_value_def
  by auto    
    
subsubsection {*equality axiom_loadop *}
  
lemma axiom_loadop2_code_equal: "axiom_loadop2 opid opid' po xseq pbm = 
  axiom_loadop opid opid' po xseq pbm"
  unfolding axiom_loadop2_def axiom_loadop_def
  using program_order_before_code_equal memory_order_before_code_equal
  by auto

lemma load_value_code_equal: "load_value2 p addr opid po xseq pbm state =
  load_value p addr opid po xseq pbm state"
  unfolding load_value2_def load_value_def
    using memory_order_before_code_equal
    by (simp add: option.case_eq_if) 
end
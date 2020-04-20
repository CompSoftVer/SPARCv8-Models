(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

text {* Miscellaneous definitions. *}
theory Misc
  imports Main 
begin
  
text {* Some utility functions and lemmas. *}
lemma set_eq: "(\<forall>x. (x \<in> s1) = (x \<in> s2)) \<Longrightarrow> s1 = s2"
  by blast  
  
lemma list_mem_range: "List.member l e \<Longrightarrow> \<exists>i. (0 \<le> i \<and> i < List.length l \<and> (l!i) = e)"
  by (meson in_set_conv_nth in_set_member not_le not_less0)  

lemma list_mem_range_rev: "\<exists>i. (0 \<le> i \<and> i < List.length l \<and> (l!i) = e) \<Longrightarrow> 
  List.member l e"
  by (meson List.member_def nth_mem)    
  
text {* Test if x is before y in the list l. *}  
  
definition list_before:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"list_before x l y \<equiv> \<exists>i j. 0 \<le> i \<and> i < length l \<and> 0 \<le> j \<and> j < length l \<and> 
  (l!i) = x \<and> (l!j) = y \<and> i < j"  

value "{1::nat,2,3,4}"

text {* A  version of list_before for code export. *}

text {* Given a list l and a member e, return the sublist l' of l
after the first occurrence of e. *}     

primrec sublist_after:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sublist_after e [] = []"
|"sublist_after e (x#t) = (if e = x then t else sublist_after e t)"
  
definition list_before2:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"list_before2 x l y \<equiv> List.member (sublist_after x l) y"  


lemma all_drop_eq:
assumes a0:"n\<le>j" and
        a1:"j<length l"
      shows "l!j = (drop n l)!(j-n)"
  using a0 a1 by (simp add: less_or_eq_imp_le)
  
lemma length_take_while:"i<length l \<Longrightarrow>       
       Suc (length (takeWhile (\<lambda>e. e \<noteq> l ! i) l)) \<le> (i + 1)"
  by (metis (full_types) Suc_eq_plus1_left add.commute nat_add_left_cancel_less not_le_imp_less 
            nth_mem set_takeWhileD takeWhile_nth)
 
lemma suc_length_take_while_less_j:
 assumes a0: "j < length l" and
     a1:"x = l ! i" and
     a2:"i < j" and a3:"y = l ! j"
   shows "Suc (length (takeWhile (\<lambda>e. e \<noteq> l ! i) l))\<le>j"  
proof-
  have i_l:"i< length l" using a0 a2 by auto  
  thus ?thesis using a2 length_take_while[OF i_l] by auto
qed



      

    

(*
lemma sublist_after_emp: "\<not> (List.member l x) \<Longrightarrow> sublist_after x l = []"
proof (induction l)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a l)
  then show ?case 
    proof (cases "x = a")
      case True
      then have "List.member (a#l) x"
        by (simp add: member_rec(1))        
      then show ?thesis 
        using Cons by auto
    next
      case False
      then have "sublist_after x (a # l) = sublist_after x l"
        by simp        
      then show ?thesis 
        using Cons
        by (simp add: member_rec(1)) 
    qed
  qed
    
lemma sublist_after_mem: "List.member l x \<Longrightarrow> sublist_after x (l@l') = (sublist_after x l)@l'"
proof (induction l)
  case Nil
  then show ?case
    by (simp add: member_rec(2))     
next
  case (Cons a l)
  then show ?case 
  proof (cases "a = x")
    case True
    then have "sublist_after x ((a # l) @ l') = l@l'"
      by simp    
    from True have "sublist_after x (a # l) @ l' = l@l'"
      by simp
    then show ?thesis 
      using Cons
      using \<open>sublist_after x ((a # l) @ l') = l @ l'\<close> by auto         
  next
    case False
    then have f1: "sublist_after x ((a # l) @ l') = sublist_after x (l @ l')"
      by auto
    from False have f2: "sublist_after x (a # l) @ l' = sublist_after x l @ l'"
      by auto
    from Cons(2) False have f3: "List.member l x"
      by (simp add: member_rec(1))      
    from Cons f1 f2 f3 show ?thesis 
      by auto
  qed        
qed    
  
lemma sublist_after_extend: "List.member (sublist_after x l) y \<Longrightarrow> 
  List.member (sublist_after x l@l') y"
proof (induction l' rule: rev_induct)
  case Nil
  then show ?case
    by simp     
next
  case (snoc w ws)
  then have f1: "List.member (sublist_after x l @ ws) y"
    by auto
  then have f1_1: "List.member ((sublist_after x l @ ws)@[w]) y"
    by (metis UnCI in_set_member set_append)    
  from snoc(2) have f2: "List.member l x"
    using member_rec(2) sublist_after_emp by fastforce    
  from f1_1 f2 show ?case 
    using sublist_after_mem by auto
qed
  
lemma sublist_after_extend2: "List.member (sublist_after x l) y \<Longrightarrow> 
  List.member (sublist_after x (l@l')) y"
proof (induction l' rule: rev_induct)
  case Nil
  then show ?case
    by simp     
next
  case (snoc w ws)
  then have f1: "List.member (sublist_after x (l @ ws)) y"
    by auto
  then have f1_1: "List.member ((sublist_after x (l @ ws))@[w]) y"
    by (metis UnCI in_set_member set_append)    
  from snoc(2) have f2: "List.member l x"
    using member_rec(2) sublist_after_emp by fastforce    
  from f1_1 f2 show ?case 
    by (simp add: sublist_after_mem)       
qed  

lemma list_before2_extend: "list_before2 e1 l e2 \<Longrightarrow> list_before2 e1 (l@l') e2"
  unfolding list_before2_def
  by (simp add: sublist_after_extend2)    
*)  
  

lemma list_before_extend: "list_before e1 l e2 \<Longrightarrow> list_before e1 (l@l') e2"  
proof -
  assume a1: "list_before e1 l e2"
  obtain nn :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat" and nna :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat" where
    "\<forall>x0 x1 x2. (\<exists>v3 v4. 0 \<le> v3 \<and> v3 < length x1 \<and> 0 \<le> v4 \<and> v4 < length x1 \<and> x1 ! v3 = x2 \<and> x1 ! v4 = x0 \<and> v3 < v4) = (0 \<le> nn x0 x1 x2 \<and> nn x0 x1 x2 < length x1 \<and> 0 \<le> nna x0 x1 x2 \<and> nna x0 x1 x2 < length x1 \<and> x1 ! nn x0 x1 x2 = x2 \<and> x1 ! nna x0 x1 x2 = x0 \<and> nn x0 x1 x2 < nna x0 x1 x2)"
  by moura
  then have f2: "\<forall>a as aa. (\<not> list_before a as aa \<or> 0 \<le> nn aa as a \<and> nn aa as a < length as \<and> 0 \<le> nna aa as a \<and> nna aa as a < length as \<and> as ! nn aa as a = a \<and> as ! nna aa as a = aa \<and> nn aa as a < nna aa as a) \<and> (list_before a as aa \<or> (\<forall>n na. \<not> 0 \<le> n \<or> \<not> n < length as \<or> \<not> 0 \<le> na \<or> \<not> na < length as \<or> as ! n \<noteq> a \<or> as ! na \<noteq> aa \<or> \<not> n < na))"    
    by (meson list_before_def)
  then have f3: "0 \<le> nn e2 l e1 \<and> nn e2 l e1 < length l \<and> 0 \<le> nna e2 l e1 \<and> nna e2 l e1 < length l \<and> l ! nn e2 l e1 = e1 \<and> l ! nna e2 l e1 = e2 \<and> nn e2 l e1 < nna e2 l e1"
    using a1 by presburger
  then have f4: "nn e2 l e1 < length (l @ l')"
    by simp
    have f5: "nna e2 l e1 < length (l @ l')"
      using f3 by simp
    have f6: "(l @ l') ! nn e2 l e1 = e1"
      using f3 by (simp add: nth_append)
    have "(l @ l') ! nna e2 l e1 = e2"
      using f3 by (metis nth_append)
  then show ?thesis
    using f6 f5 f4 f3 f2 by meson
qed     

lemma list_before_extend2: 
  assumes a1: "List.member l e1"
  and a2: "\<not>(List.member l e2)"
  and a3: "List.member (l@l') e2" 
shows "list_before e1 (l@l') e2"
proof -
  from a1 obtain i where f1: "i < length l \<and> (l!i) = e1"
    by (meson list_mem_range)
  from a2 have f2: "\<not>(\<exists>k. k < length l \<and> (l!k) = e2)"
    by (meson in_set_member nth_mem)
  then have f3: "\<not>(\<exists>k. k < length l \<and> ((l@l')!k) = e2)"
    by (metis nth_append)    
  from a3 obtain j where f4: "j < length (l@l') \<and> ((l@l')!j) = e2"
    by (meson list_mem_range)
  from f3 f4 have f5: "j \<ge> length l"
    using not_le by blast
  from f1 have f6: "i < length l \<and> ((l@l')!i) = e1"
    by (simp add: nth_append)
  show ?thesis unfolding list_before_def using f4 f5 f6
    by (metis (no_types, lifting) dual_order.strict_trans le0 less_le_trans)    
qed  

lemma list_before_extend2': 
  assumes a1: "List.member l e1"
  and a2: "List.member l' e2" 
shows "list_before e1 (l@l') e2"  
proof -  
  from a1 obtain i where  f0:"i < length l \<and> (l!i) = e1"
    by (meson list_mem_range)
  then have f1:"i<length l + length l' \<and> (l @ l') ! i = e1"
    by (meson nth_append trans_less_add1 list_mem_range)    
  from a2 obtain j where f2: "j < length l' \<and> (l'!j) = e2"
    by (meson list_mem_range)  
  then have "j+length l < length l + length l'" by auto
  moreover have "(l @ l') ! (j+length l) = e2" using f2
    by (metis add.commute nth_append_length_plus)
  moreover have "i<(j+length l)" using f1
    by (simp add: f0 trans_less_add2)       
  ultimately show ?thesis using f1 unfolding list_before_def
    by (metis length_append less_eq_nat.simps(1))      
qed    
  
lemma list_elements_before: "List.member l e1 \<Longrightarrow> List.member l e2 \<Longrightarrow>  e1 \<noteq> e2 \<Longrightarrow> 
  list_before e1 l e2 \<or> list_before e2 l e1"
  apply auto
  unfolding list_before_def apply simp
  using list_mem_range
  by (metis linorder_neqE_nat)     

lemma dist_elem_not_before: "List.member l e1 \<Longrightarrow> List.member l e2 \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> \<not> (list_before e1 l e2) \<Longrightarrow> list_before e2 l e1"   
  using list_elements_before by fastforce     

text {* Define a list without repeating members. *}

(*
definition non_repeat_list:: "'a list \<Rightarrow> bool" where
"non_repeat_list l \<equiv> 
  \<forall>i j. (0 \<le> i \<and> i < List.length l \<and> 0 \<le> j \<and> j < List.length l \<and> i \<noteq> j) \<longrightarrow> 
        (l!i \<noteq> l!j)"  
*)

definition non_repeat_list:: "'a list \<Rightarrow> bool" where
"non_repeat_list l \<equiv> distinct l" 

text {* Get the position of a member in a non-repeating list. *}

definition non_repeat_list_pos:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"non_repeat_list_pos x l \<equiv> THE n. non_repeat_list l \<and> n < length l \<and> (l!n) = x"  

text {* A new version of non_repeat_list_post that is used to code export. *}

primrec non_repeat_list_pos2:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where  
"non_repeat_list_pos2 x [] = 0"  
|"non_repeat_list_pos2 x (a#al) = (if x = a then 0 else 1 + (non_repeat_list_pos2 x al))" 
  
(* Zhe: non_repeat_list_pos2 and non_repeat_list_pos are actually different when
x is not in l! I'm not sure what value would non_repeat_list_pos return when
x is not in l. *)  
lemma non_repeat_list_code_equal: "non_repeat_list_pos2 x l = non_repeat_list_pos x l"
sorry   
  

lemma non_repeat_list_emp: "non_repeat_list []"
  unfolding non_repeat_list_def
  by auto

lemma non_repeat_list_pos_rel: "non_repeat_list l \<Longrightarrow> List.member l x \<Longrightarrow> List.member l y \<Longrightarrow>
 x \<noteq> y \<Longrightarrow> list_before x l y \<or> list_before y l x"  
  unfolding non_repeat_list_def list_before_def
  by (metis le_neq_implies_less list_mem_range not_le)
    
(*    
  apply auto
  by (metis in_set_conv_nth member_def nat_neq_iff)
*)
 
lemma non_repeat_list_extend: "non_repeat_list l \<Longrightarrow> \<not> (List.member l x) \<Longrightarrow> 
 non_repeat_list (l@[x])"    
  using non_repeat_list_def 
  by (simp add: member_def non_repeat_list_def) 

(*  
proof (auto simp add: non_repeat_list_def)
  fix i :: nat and j :: nat
  assume a1: "\<not> List.member l x"
  assume a2: "i \<noteq> j"
  assume a3: "i < Suc (length l)"
  assume a4: "j < Suc (length l)"
  assume a5: "(l @ [x]) ! i = (l @ [x]) ! j"
  assume a6: "\<forall>i j. i < length l \<and> j < length l \<and> i \<noteq> j \<longrightarrow> l ! i \<noteq> l ! j"
  have f7: "\<And>n as. \<not> n < length as \<or> List.member as (as ! n::'a)"
    by (metis in_set_member nth_mem)
  then have "length l = i"
    using a6 a5 a4 a3 a2 a1 by (metis (no_types) less_Suc_eq nth_append nth_append_length)
  then show False
    using f7 a5 a4 a2 a1 by (metis (no_types) less_Suc_eq nth_append nth_append_length)
qed      
*)
  
lemma non_repeat_list_sublist_mem: "non_repeat_list (l1@[x]@l2) \<Longrightarrow> \<not> (List.member l1 x)"
  unfolding non_repeat_list_def
  by (simp add: in_set_member non_repeat_list_def)  
(*    
proof -
  assume "\<forall>i j. 0 \<le> i \<and> i < length (l1 @ [x] @ l2) \<and> 0 \<le> j \<and> j < length (l1 @ [x] @ l2) \<and> i \<noteq> j \<longrightarrow> (l1 @ [x] @ l2) ! i \<noteq> (l1 @ [x] @ l2) ! j"
  then have "distinct (l1 @ [x] @ l2)"
    by (meson distinct_conv_nth less_eq_nat.simps(1))
  then show ?thesis
  by (simp add: in_set_member)
qed
*)
  
lemma non_repeat_list_pos_unique: "non_repeat_list l \<Longrightarrow> 
0 \<le> i \<and> i < length l \<Longrightarrow> 0 \<le> j \<and> j < length l \<Longrightarrow> l!i = l!j \<Longrightarrow> i = j"  
  unfolding non_repeat_list_def
  by (simp add: nth_eq_iff_index_eq)
(*    
  by auto
*)
    
lemma non_repeat_list_sublist: "non_repeat_list l \<Longrightarrow> l1@l2 = l \<Longrightarrow> non_repeat_list l1"
  unfolding non_repeat_list_def
  using distinct_append by blast
    
(*  by (metis length_append nth_append trans_less_add1) *)
    
lemma non_repeat_list_before: "non_repeat_list l \<Longrightarrow> list_before e1 l e2 \<Longrightarrow>
  \<not>(list_before e2 l e1)"
  unfolding non_repeat_list_def list_before_def
  using nth_eq_iff_index_eq by fastforce          
(*    
  apply auto
  by (metis less_asym' less_trans) *)
    
text {* l1 is a sublist of l2. *}  
  
definition is_sublist:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sublist l1 l2 \<equiv> \<exists>l. l1@l = l2"  
  
text {* A new version of is_sublist for code export. *}
  
definition is_sublist2:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sublist2 l1 l2 \<equiv> take (length l1) l2 = l1"  
  
lemma is_sublist_code_equal: "is_sublist2 l1 l2 = is_sublist l1 l2"
  unfolding is_sublist2_def is_sublist_def
  by (metis append_eq_conv_conj append_take_drop_id)
    
lemma is_sublist_id: "is_sublist l l"
  unfolding is_sublist_def
  by auto

lemma sublist_element: "is_sublist l1 l2 \<Longrightarrow> i < List.length l1 \<Longrightarrow> l1!i = l2!i"
  unfolding is_sublist_def
  by (metis nth_append)

lemma sublist_member: 
  assumes a1: "is_sublist l1 l2"
  and a2: " List.member l1 e" 
shows "List.member l2 e"
proof -
  from a2 obtain i where f1: "i < List.length l1 \<and> l1!i = e"
    by (meson list_mem_range)
  then have f2: "l2!i = e"
    using a1 sublist_element by fastforce
  from f1 a1 have "i < List.length l2"
    unfolding is_sublist_def
    by auto
  then have "i < List.length l2 \<and> l2!i = e"
    using f2 by auto    
  then show ?thesis
    by (meson member_def nth_mem)     
qed  

lemma sublist_repeat: "is_sublist l1 l2 \<Longrightarrow> \<not> (non_repeat_list l1) \<Longrightarrow> \<not> (non_repeat_list l2)"
  unfolding is_sublist_def non_repeat_list_def
  apply auto
  done  
(*  by (metis nth_append trans_less_add1)    *)
    
text {* Given an item and a list, return the sub-list that
is before the item in the list. 
If the item in not in the list, return []. *}

primrec find_sub_list_before:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"find_sub_list_before e [] acc = []"
|"find_sub_list_before e (x#xs) acc = (if e = x then acc else find_sub_list_before e xs (acc@[x]))"

definition sub_list_before:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sub_list_before e l = find_sub_list_before e l []"     

lemma list_before_tran:
"distinct l \<Longrightarrow>
 list_before x1 l x2 \<Longrightarrow>
 list_before x2 l x3 \<Longrightarrow>
 list_before x1 l x3"
  unfolding list_before_def
  by (metis (no_types, lifting) dual_order.strict_trans nth_eq_iff_index_eq)



lemma list_before_not_sym:                 
"distinct l \<Longrightarrow>
 list_before x l y \<Longrightarrow> \<not> list_before y l x"
  unfolding list_before_def
  using nth_eq_iff_index_eq by fastforce

lemma list_before_in_list:
"x\<in>{x. list_before x l y} \<Longrightarrow>
 List.member l x"
  unfolding list_before_def
  apply auto
  by (meson dual_order.strict_trans in_set_member nth_mem)

lemma not_list_before_members_eq_or_inv:"List.member l x \<Longrightarrow> List.member l y \<Longrightarrow> \<not> list_before x l y \<Longrightarrow>
      x=y \<or> list_before y l x"
  unfolding list_before_def
  by (metis le_neq_implies_less list_mem_range not_le) 

lemma exists_unique_list_member:
      "finite z \<Longrightarrow>
       z\<noteq>{} \<Longrightarrow>
       distinct l \<Longrightarrow>
       z\<subseteq>{x. List.member l x} \<Longrightarrow>      
       \<exists>x. x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> list_before x' l x)"
proof(induction rule: Finite_Set.finite_ne_induct)
case (singleton x)
  then show ?case
    by blast 
next
  case (insert x F)
  then obtain x1 where hp:"x1\<in>F \<and> (\<forall>x'\<in>F. x' \<noteq> x1 \<longrightarrow> list_before x' l x1)"
     by auto
  then have neq:"x\<noteq>x1" using insert by auto
  { assume "list_before x l x1"
    then have ?case using hp neq by fastforce
  }note l1 =this
  {
    assume assm:"list_before x1 l x"
    then have ?case using hp neq list_before_tran[OF insert(5) _ assm] 
      by fast
  }note l2 = this
  show ?case
    by (metis hp insert.prems(2) insert_subset l1 l2 list_elements_before mem_Collect_eq 
       neq set_rev_mp)  
qed


lemma unique_max_list_before:
  assumes
        a2:"distinct l" and       
       a4:"x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> list_before x' l x)"
     shows "\<forall>x'. x'\<in>z \<and> (\<forall>x''\<in>z. x''\<noteq>x' \<longrightarrow> list_before x'' l x') \<longrightarrow> x' = x "
  using list_before_not_sym[OF a2] a4 by metis

lemma finite_subset_list:"z\<subseteq>{x. List.member l x} \<Longrightarrow> finite z"  
  unfolding member_def 
  by (simp add: finite_subset)

lemma exists_unique_list_before_list:"distinct l \<Longrightarrow>
       z\<subseteq>{x. List.member l x} \<Longrightarrow>
       z\<noteq>{} \<Longrightarrow>
       \<exists>!x. x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> list_before x' l x)"        
  apply (frule exists_unique_list_member[OF finite_subset_list],assumption+)  
  apply clarsimp 
  by (frule unique_max_list_before, auto simp add: Ex1_def)

lemma exists_unique_list_before_lb:
  assumes a0:"distinct l" and
       a1:"z\<subseteq>{x. list_before x l y}" and
      a2:"z\<noteq>{}"
    shows "\<exists>!x. x\<in>z \<and> (\<forall>x'\<in>z. x'\<noteq>x \<longrightarrow> list_before x' l x)"        
proof-
  have "z\<subseteq>{x. List.member l x}"
    using a1 unfolding list_before_def member_def by auto
  then show ?thesis using exists_unique_list_before_list[OF a0 _ a2]
    by auto
qed
  
    

end
  
    


  
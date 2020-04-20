text {* Temporary code. *}
  
theory Tmp
  imports Main
begin
  
text {* An input for the execution is the sequence of instructions ordered by 
how the processor issues the instructions. This is also the order of the instructions
in the program control-flow at the software level. *}

type_synonym proc_instr_order = "(proc \<times> (instruction list))"
  
text {* In our memory model, we separate the instructions SWAP and CASA to two parts.
Their atomicity is handled by the memory model. 
We need to pre-process the sequence of instructions and separate them before execution. *}

primrec pre_proc_instr:: "instruction list \<Rightarrow> instruction list" where
"pre_proc_instr [] = []"
|"pre_proc_instr (x#xs) = (case (fst x) of 
  load_store_type SWAP \<Rightarrow> [(load_store_type SWAP_L, snd x)]@[(load_store_type SWAP_S, snd x)]@
                          (pre_proc_instr xs)
 |load_store_type CASA \<Rightarrow> [(load_store_type CASA_L, snd x)]@[(load_store_type CASA_S, snd x)]@
                          (pre_proc_instr xs)
 |_ \<Rightarrow> x#(pre_proc_instr xs))"

text {* Get the last instruction of the mem_op_block. *} 
  
definition last_op_of_mem_op_block:: "mem_op_block \<Rightarrow> instruction option" where
"last_op_of_mem_op_block b \<equiv> if inst b = [] then None else Some (List.last (inst b))"  

text {* Get the processor of the mem_op_block. *}

definition proc_of_mem_op_block:: "mem_op_block \<Rightarrow> proc" where
"proc_of_mem_op_block b \<equiv> pr b"    
  
text {* Add an instruction in a block. *}  
  
definition block_add:: "instruction \<Rightarrow> mem_op_block \<Rightarrow> mem_op_block" where
"block_add instr b \<equiv> b\<lparr>inst := (inst b)@[instr]\<rparr>"    
  
text {* The function below converts a list of instructions in an execution 
instance into a list of mem_op_block, where each mem_op_block contains at most
one memory access instructions which must be the last instruction of the block. 
We also add a unique number to identify each block. *}    
    
primrec blockify :: "instruction list \<Rightarrow> nat \<Rightarrow> mem_op_block list \<Rightarrow> (nat \<times> mem_op_block list)" where
"blockify [] n acc = (if inst (List.last acc) = [] then ((Suc n), List.butlast acc) 
  else ((Suc n),acc))"
|"blockify (x#xs) n acc = (case (fst x) of 
  load_store_type lsi \<Rightarrow> blockify xs (Suc n) ((List.butlast acc)@
    [block_add x (List.last acc)]@[emp_mem_op_block\<lparr>id := (Suc n)\<rparr>\<lparr>pr := (pr (List.last acc))\<rparr>])
 |_ \<Rightarrow> blockify xs n ((List.butlast acc)@[block_add x (List.last acc)]))"  

text {* A wrapper for executing a mem_op_block. *}

definition execute_block:: "proc \<Rightarrow> mem_op_block \<Rightarrow> virtual_address option \<Rightarrow> memory_value option \<Rightarrow>
 sparc_state \<Rightarrow> (sparc_state \<times> virtual_address option \<times> memory_value option)" where
"execute_block p b a v s \<equiv> sequential_execution p (inst b) a v s"    
  
text {* Given a list of proc_instr_order (one list per processor), 
return all the program orders (one list per processor). *}  
  
primrec get_program_order_list :: "proc_instr_order list \<Rightarrow> nat \<Rightarrow> program_order \<Rightarrow> 
  program_order" where
"get_program_order_list [] n po = po"
|"get_program_order_list (x#xs) n po = (
  let (nn,nb) = blockify (snd x) n [emp_mem_op_block\<lparr>id := n, pr := (fst x)\<rparr>] in
  get_program_order_list xs nn (po((fst x) := nb)))" 
 

text {* Given the list of instruction sequences of all processors, return
the list of all program orders for all processors. *}
  
definition get_program_order:: "proc_instr_order list \<Rightarrow> program_order" where
"get_program_order instr_list \<equiv> get_program_order_list instr_list 0 emp_program_order"

text {* Given a sequence of mem_op_block, and a sequence of executed mem_op_block. 
Check if all loads in the former list are already executed. *}  
  
primrec all_loads_executed:: "mem_op_block list \<Rightarrow> mem_op_block list \<Rightarrow> bool" where 
"all_loads_executed [] xseq = True"    
|"all_loads_executed (x#xs) xseq = (case last_op_of_mem_op_block x of 
  Some ((load_store_type LD),_) \<Rightarrow> if List.member xseq x then all_loads_executed xs xseq else False
  |Some ((load_store_type SWAP_L),_) \<Rightarrow> if List.member xseq x then all_loads_executed xs xseq else False
  |Some ((load_store_type CASA_L),_) \<Rightarrow> if List.member xseq x then all_loads_executed xs xseq else False
  |_ \<Rightarrow> all_loads_executed xs xseq)"

text {* Given a mem_op_block b, all the program orders, a sequence of executed mem_op_block, 
check if all load ops issued by the same processor before b are executed. *}  
  
definition all_loads_before_executed:: "mem_op_block \<Rightarrow> program_order \<Rightarrow> mem_op_block list \<Rightarrow>
  bool" where
"all_loads_before_executed b po xseq \<equiv> 
  all_loads_executed (sub_list_before b (po (proc_of_mem_op_block b))) xseq"  
  
text {* Given a sequence of mem_op_block, and a sequence of executed mem_op_block. 
Check if all stores in the former list are already executed. *}  
  
primrec all_stores_executed:: "mem_op_block list \<Rightarrow> mem_op_block list \<Rightarrow> bool" where 
"all_stores_executed [] xseq = True"    
|"all_stores_executed (x#xs) xseq = (case last_op_of_mem_op_block x of 
  Some ((load_store_type ST),_) \<Rightarrow> if List.member xseq x then all_stores_executed xs xseq else False
  |Some ((load_store_type SWAP_S),_) \<Rightarrow> if List.member xseq x then all_stores_executed xs xseq else False
  |Some ((load_store_type CASA_S),_) \<Rightarrow> if List.member xseq x then all_stores_executed xs xseq else False
  |_ \<Rightarrow> all_stores_executed xs xseq)"

text {* Given a mem_op_block b, all the program orders, a sequence of executed mem_op_block, 
check if all store ops issued by the same processor before b are executed. *}  
  
definition all_stores_before_executed:: "mem_op_block \<Rightarrow> program_order \<Rightarrow> mem_op_block list \<Rightarrow>
  bool" where
"all_stores_before_executed b po xseq \<equiv> 
  all_stores_executed (sub_list_before b (po (proc_of_mem_op_block b))) xseq" 

section {* This section defines an operational TSO memory model. *}  
  
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
    if list_pos op1 xseq < list_pos op2 xseq then Some True
    else Some False
  else if List.member xseq op1 then Some True
  else if List.member xseq op2 then Some False
  else None"  

text {* Given an address and the executed sequence of mem_op_block ids, return 
the id of the first store in the executed sequence at the same address. 
If there are none, return None. 
N.B. We could formulate the below functions more mathematically (i.e., using sets
and first-order logic), but we choose the define it in a more operational way
for performance reasons. *}

primrec get_first_store:: "virtual_address \<Rightarrow> op_id list \<Rightarrow> sparc_state \<Rightarrow> op_id option" where
"get_first_store addr [] state = None"
|"get_first_store addr (x#xs) state = (
  if Some addr = (op_addr (mem_op_val x state)) \<and>
     type_of_mem_op_block (mem_op_val x state) \<in> {st_block, ast_block} 
  then
    Some x
  else get_first_store addr xs state)"
  
definition mem_most_recent_store:: "virtual_address \<Rightarrow> executed_mem_ops \<Rightarrow> sparc_state \<Rightarrow> 
  op_id option" where
"mem_most_recent_store addr xseq state \<equiv> get_first_store addr (List.rev xseq) state"  

text {* Given a load operation id and the program order, return the id of most recent
store at the same address in the program order that is before the load.
If there are none, return None. *}
  
definition proc_most_recent_store:: "proc \<Rightarrow> virtual_address \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> 
  sparc_state \<Rightarrow> op_id option" where
"proc_most_recent_store p addr opid po state \<equiv> 
  get_first_store addr (List.rev (sub_list_before opid (po p))) state"  

text {* The value of the load operation based on the axiom value. *}

definition load_value:: "proc \<Rightarrow> virtual_address \<Rightarrow> op_id \<Rightarrow> program_order \<Rightarrow> executed_mem_ops \<Rightarrow> sparc_state \<Rightarrow>
  memory_value option" where  
"load_value p addr opid po xseq state \<equiv> 
  case ((mem_most_recent_store addr xseq state),(proc_most_recent_store p addr opid po state)) of 
  (Some s1, Some s2) \<Rightarrow> (case (s1 m<xseq s2) of 
    Some True \<Rightarrow> op_val (mem_op_val s2 state)
    |Some False \<Rightarrow> op_val (mem_op_val s1 state)
    |None \<Rightarrow> None)
  |(None, Some s2) \<Rightarrow> op_val (mem_op_val s2 state)
  |(Some s1, None) \<Rightarrow> op_val (mem_op_val s1 state)
  |(None, None) \<Rightarrow> None"  

text {* Given (1) the program order, (2) a list of executed mem_op_block ids, 
(3) a list of remaining (not executed) mem_op_block.
Return a list of all possible (under TSO) new list of executed mem_op_block, each item 
in the resultant list is an extension of (2), 
and the corresponding remaining mem_op_block,
and the corresponding states. *}

primrec tso_exe_step:: "program_order \<Rightarrow> executed_mem_ops \<Rightarrow> op_id list \<Rightarrow>
  sparc_state \<Rightarrow> (executed_mem_ops \<times> (op_id list) \<times> sparc_state) list" where
"tso_exe_step po xseq [] state = []" 
|"tso_exe_step po xseq (x#xs) state = (
  let p = proc_of_op x state in
  case type_of_mem_op_block (mem_op_val x state) of
  ld_block \<Rightarrow>     
    if \<forall>opid. (((opid ;po^p x) \<and> 
                (type_of_mem_op_block (mem_op_val opid state) \<in> {ld_block, ald_block})) \<longrightarrow> 
               (List.member xseq opid)) 
    then (* x can be executed. *) 
      let addr = load_addr p (List.last (insts (mem_op_val x state))) state;
          vop = load_value p addr x po xseq state
      in
      [(xseq@[x], xs, (proc_exe_to p po (nat (list_pos x (po p))) vop (Some addr) state))]@
      (tso_exe_step po xseq xs state) 
    else tso_exe_step po xseq xs state (* x can't be executed. *)
  |st_block \<Rightarrow> 
    if (atomic_flag_val state) = False \<and>
       (\<forall>opid. (((opid ;po^p x) \<and> 
                (type_of_mem_op_block (mem_op_val opid state) \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
               (List.member xseq opid)))
    then (* x can be executed. *)
      [(xseq@[x], xs, (proc_exe_to p po (nat (list_pos x (po p))) None None state))]@
      (tso_exe_step po xseq xs state)
    else tso_exe_step po xseq xs state (* x can't be executed. *)
  |ald_block \<Rightarrow> 
    if (atomic_flag_val state) = False \<and> 
       (\<forall>opid. (((opid ;po^p x) \<and> 
                (type_of_mem_op_block (mem_op_val opid state) \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
               (List.member xseq opid))) 
    then (* x can be executed. *) 
      let addr = atomic_load_addr p (List.last (insts (mem_op_val x state))) state;
          vop = load_value p addr x po xseq state;
          state1 = atomic_flag_mod True state
      in
      [(xseq@[x], xs, (proc_exe_to p po (nat (list_pos x (po p))) vop (Some addr) state1))]@
      (tso_exe_step po xseq xs state1) 
    else tso_exe_step po xseq xs state (* x can't be executed. *)
  |ast_block \<Rightarrow> 
    if (atomic_flag_val state) = True \<and>
       (\<forall>opid. (((opid ;po^p x) \<and> 
                (type_of_mem_op_block (mem_op_val opid state) \<in> {ld_block, ald_block, st_block, ast_block})) \<longrightarrow> 
               (List.member xseq opid)))
    then (* x can be executed. *)
      let state1 = atomic_flag_mod False state in
      [(xseq@[x], xs, (proc_exe_to p po (nat (list_pos x (po p))) None None state1))]@
      (tso_exe_step po xseq xs state1)
    else tso_exe_step po xseq xs state (* x can't be executed. *)
  |o_block \<Rightarrow> 
    [(xseq@[x], xs, (proc_exe_to p po (nat (list_pos x (po p))) None None state))]@
    (tso_exe_step po xseq xs state))"

primrec tso_exe_1round:: "program_order \<Rightarrow> (executed_mem_ops \<times> (op_id list) \<times> sparc_state) list \<Rightarrow> 
  (executed_mem_ops \<times> (op_id list) \<times> sparc_state) list" where
"tso_exe_1round po [] = []"
|"tso_exe_1round po (x#xs) = 
  (tso_exe_step po (fst x) (fst (snd x)) (snd (snd x)))@(tso_exe_1round po xs)"
  
definition "tso_exe_all = undefined (* Executed tso_exe_1round until each item in the list has its
executed_mem_ops containing all ops in program_order. *)"  

text {* Given an element, find it's position in the list. Return -1 
if it's not in the list. *}

primrec find_elem_list:: "'a \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> int" where
"find_elem_list e [] i = -1"
|"find_elem_list e (x#xs) i = (if e = x then i else find_elem_list e xs (i+1))"

definition list_pos:: "'a \<Rightarrow> 'a list \<Rightarrow> int" where
"list_pos e l \<equiv> find_elem_list e l 0"

lemma pos_range: "List.member l x \<Longrightarrow> 0 \<le> list_pos x l \<and> nat (list_pos x l) < List.length l"
proof (induction l arbitrary: x)
  case Nil
  then show ?case 
    using member_rec(2) by fastforce
next
  case (Cons a l)
  then show ?case 
  proof (cases "List.member l x")
    case True
    then have "0 \<le> list_pos x l \<and> nat (list_pos x l) < length l"
      using Cons by auto
    then show ?thesis 
      
  next
    case False
    then show ?thesis sorry
  qed
qed

lemma pos_unique: "non_repeat_list l \<Longrightarrow> List.member l x \<Longrightarrow> List.member l x' \<Longrightarrow>
  x \<noteq> x' \<Longrightarrow> list_pos x l \<noteq> list_pos x' l"
proof (induction l arbitrary: x x')
  case Nil
  then show ?case 
    using member_rec(2) by fastforce
next
  case (Cons a l)
  then show ?case sorry
qed
  
end
  
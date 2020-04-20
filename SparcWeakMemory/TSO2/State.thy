\<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 \<close>

text {* SPARC V8 state model*}
theory State
imports Main Types  
begin                
  
section {* The definition of the machine state. *}

text{* The state @{term sparc_state} is defined as a record of @{term cpu_context}, 
@{term user_context}, @{term mem_context}, etc. 
Each processor has its own control registers, general registers, and state variables.
All processors share the memory. 
*}

record (overloaded) sparc_state =
ctl_reg:: "proc \<Rightarrow> control_register" \<comment>\<open> Control registers for each processor. \<close>
gen_reg:: "proc \<Rightarrow> general_register" \<comment>\<open> General registers for each processor. \<close>
mem:: memory \<comment>\<open> Memory. N.B. We do not need memory for execution since we get the load_value using program_order and memory_order. But we need memory to print the final state. \<close>
mem_ops:: "op_id \<Rightarrow> mem_op_state" \<comment>\<open> The memory operation blocks in the concurrent program.  \<close> 
proc_exe_pos:: "proc \<Rightarrow> nat" \<comment>\<open> The position of the next mem_op_block that is going to be executed by the processor in the program order. \<close>
proc_var:: "proc \<Rightarrow> sparc_proc_var" \<comment>\<open> State variables for each processor. \<close>
glob_var:: global_var \<comment>\<open> Global state variables. \<close>
undef:: bool \<comment>\<open> Whether the state is defined or not. \<close>

section{* functions for state member access *}

text {* Obtain the value of the control register. *}  
  
definition ctl_reg_val:: "proc \<Rightarrow> control_register_type \<Rightarrow> sparc_state \<Rightarrow> register_value" where
"ctl_reg_val p reg state \<equiv> (ctl_reg state) p reg"

text {* Modify the value of the control register. *}

definition ctl_reg_mod :: "proc \<Rightarrow> register_value \<Rightarrow> control_register_type \<Rightarrow> 
sparc_state \<Rightarrow> sparc_state" where "ctl_reg_mod p val reg state \<equiv> 
  state\<lparr>ctl_reg := ((ctl_reg state)(p := ((ctl_reg state p)(reg := val))))\<rparr>"

text {* Obtain the value of a given register.
We drop the SPARCv8 requirement that r[0] = 0 for generality. *}
  
definition gen_reg_val:: "proc \<Rightarrow> register \<Rightarrow> sparc_state \<Rightarrow> register_value" where
"gen_reg_val p reg state \<equiv> (gen_reg state) p reg"

text {* Modify the value of the general register. *}

definition gen_reg_mod:: "proc \<Rightarrow> register_value \<Rightarrow> register \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"gen_reg_mod p val reg state \<equiv> 
state\<lparr>gen_reg := ((gen_reg state)(p := (gen_reg state p)(reg := val)))\<rparr>"  
  
text {* Obtain the value of a given memory address. *}

definition mem_val:: "virtual_address \<Rightarrow> sparc_state \<Rightarrow> memory_value option" where
"mem_val addr state \<equiv> mem state addr"

text {* Modify the value at a memory address. *}

definition mem_mod:: "memory_value \<Rightarrow> virtual_address \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"mem_mod val addr state \<equiv> state\<lparr>mem := (mem state)(addr := Some val)\<rparr>"

text {* Obtain the mem_op_block. *}
 
definition get_mem_op_state:: "op_id \<Rightarrow> sparc_state \<Rightarrow> mem_op_state" where
"get_mem_op_state opid state \<equiv> (mem_ops state) opid"  

text {* Change the op_addr field of mem_op_block of op_id. *}

definition mem_op_addr_mod:: "virtual_address \<Rightarrow> op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"mem_op_addr_mod addr opid state \<equiv> 
  state\<lparr>mem_ops := ((mem_ops state)(opid := ((mem_ops state opid)\<lparr>op_addr := Some addr\<rparr>)))\<rparr>"  
  
text {* Change the op_val field of mem_op_block of op_id. *}

definition mem_op_val_mod:: "memory_value \<Rightarrow> op_id \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"mem_op_val_mod val opid state \<equiv> 
  state\<lparr>mem_ops := ((mem_ops state)(opid := ((mem_ops state opid)\<lparr>op_val := Some val\<rparr>)))\<rparr>"  
  
text {* Obtain the next mem_op_block by its position in the program order
(position in a list). *}

definition next_proc_op_pos:: "proc \<Rightarrow> sparc_state \<Rightarrow> nat" where
"next_proc_op_pos p state \<equiv> proc_exe_pos state p"  

text {* Change the position of the next mem_op_block for proc in its 
program order (a list). *}

definition next_proc_op_pos_mod:: "proc \<Rightarrow> nat \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"next_proc_op_pos_mod p pos state \<equiv> state\<lparr>proc_exe_pos := ((proc_exe_pos state)(p := pos))\<rparr>"  

text {* Obtain the value of the annul flag. *}

definition annul_val :: "proc \<Rightarrow> sparc_state \<Rightarrow> bool" where 
"annul_val p state \<equiv> annul (proc_var state p)"

text {* Modify the value of the annul flag. *}

definition annul_mod :: "proc \<Rightarrow> bool \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where 
"annul_mod p b s \<equiv> s\<lparr>proc_var := ((proc_var s)(p := (proc_var s p)\<lparr>annul := b\<rparr>))\<rparr>"

text {*Obtain the value of the atomic flag. *}

definition atomic_flag_val :: "sparc_state \<Rightarrow> op_id option" where
"atomic_flag_val state \<equiv> atomic_flag (glob_var state)"  

text {* Modify the value of the atomic flag. *}
  
definition atomic_flag_mod :: "op_id option \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"atomic_flag_mod opidop s \<equiv> s\<lparr>glob_var := ((glob_var s)\<lparr>atomic_flag := opidop\<rparr>)\<rparr>"  

text {*Obtain the value of the original rd value in atomic load-store instructions. *}

definition atomic_rd_val :: "sparc_state \<Rightarrow> register_value" where
"atomic_rd_val state \<equiv> atomic_rd (glob_var state)"  

text {* Modify the value of the original rd value in atomic load-store instructions. *}
  
definition atomic_rd_mod :: "register_value \<Rightarrow> sparc_state \<Rightarrow> sparc_state" where
"atomic_rd_mod v s \<equiv> s\<lparr>glob_var := ((glob_var s)\<lparr>atomic_rd := v\<rparr>)\<rparr>"  

text {* Check if the state is undefined. *}  
  
definition state_undef:: "sparc_state \<Rightarrow> bool" where 
"state_undef state \<equiv> (undef state)"

end


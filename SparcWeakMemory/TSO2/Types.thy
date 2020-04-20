\<comment>\<open>
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou. 
 \<close>

text {* Types for big-step semantics for SPARC TSO and instructions. *}
theory Types    
imports Main "WordDecl" 
begin

text {* General registers are defined with the type @{term reg_addr} 
represented by a 32 bits word. *}

type_synonym register = word32  
  
text {* The data stored in a register is defined as a 32 bits word @{term reg_val}. *}
  
type_synonym register_value = word32  

text {* Finally the general register is defined by another total function from 
@{term gen_reg} to @{term reg_val}. *}
  
type_synonym general_register = "register \<Rightarrow> register_value"

text {* We do not consider MMU here, so we directly use 32-bit virtual address in 
the memory model. The TSO memory model only concerns data memory, so we assume
that memory operations involved are of ASI = 10/11 in the SPARC architecture. 
We strip the concept of ASI from our model to make the model more general. *}  
  
type_synonym virtual_address = word32

text {* For simplicity we assume that each memory operation accesses 32 bits data. 
This is the same as the x86-TSO model, and we follow it because load/store on 32 bits data
are the most frequent instructions in programs. 
This is NOT the same as the assumption in SPARCv8's TSO model, which defines 
that each memory operation accesses a doubleword (64 bits).
As a result, we only consider the following load/store instructions in our model:
LD, ST, SWAP, CAS, where the load and store in SWAP and CAS are atomic. 

We do not concern whether the memory address is aligned 
(i.e., the last 2 bits of the address are 0s). We assume that this should
be handled correctly by compiler and we ignore errors caused by this. 

In general, we only concern the correctness of concurrent execution here,
not the format of instructions etc. 

*}  

type_synonym memory_value = word32   

text {* The memory is defined as a partial function from addresses to values. *}

type_synonym memory = "virtual_address \<Rightarrow> memory_value option"

text {* We only consider the control registers PSR, Y, PC, and nPC. *}
  
datatype control_register_type = 
   PSR   \<comment> \<open>"Processor State Register"\<close>
 | Y      \<comment> \<open>"Multiply/Divide Register"\<close>
 | PC     \<comment> \<open>"Program Counter"\<close>
 | nPC    \<comment> \<open>"next Program Counter"\<close>

type_synonym control_register = "control_register_type \<Rightarrow> register_value"   
   
definition get_CWP :: "word32 \<Rightarrow> word5" where
"get_CWP psr \<equiv> ucast (bitAND psr 0b00000000000000000000000000011111)"

definition get_ET :: "word32 \<Rightarrow> word1" where
"get_ET psr \<equiv> ucast ((bitAND psr 0b00000000000000000000000000100000) >> 5)"

definition get_PIL :: "word32 \<Rightarrow> word4" where
"get_PIL psr \<equiv> ucast ((bitAND psr 0b00000000000000000000111100000000) >> 8)"

definition get_PS :: "word32 \<Rightarrow> word1" where
"get_PS psr \<equiv> ucast ((bitAND psr 0b00000000000000000000000001000000) >> 6)"

definition get_S :: "word32 \<Rightarrow> word1" where
"get_S psr \<equiv> ucast ((bitAND psr 0b00000000000000000000000010000000) >> 7)"

definition get_icc_N :: "word32 \<Rightarrow> word1" where
"get_icc_N psr \<equiv> ucast ((bitAND psr 0b00000000100000000000000000000000) >> 23)"

definition get_icc_Z :: "word32 \<Rightarrow> word1" where
"get_icc_Z psr \<equiv> ucast ((bitAND psr 0b00000000010000000000000000000000) >> 22)"

definition get_icc_V :: "word32 \<Rightarrow> word1" where
"get_icc_V psr \<equiv> ucast ((bitAND psr 0b00000000001000000000000000000000) >> 21)"

definition get_icc_C :: "word32 \<Rightarrow> word1" where
"get_icc_C psr \<equiv> ucast ((bitAND psr 0b00000000000100000000000000000000) >> 20)"

definition update_S :: "word1 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_S s_val psr_val \<equiv> bitOR (bitAND psr_val 0b11111111111111111111111101111111) 
                                (((ucast s_val)::word32) << 7)"

text {* Update the CWP field of PSR. Return the new value of PSR. *}
  
definition update_CWP :: "word5 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_CWP cwp_val psr_val \<equiv>
  let tmp0 = bitAND psr_val (0b11111111111111111111111111100000::word32) in
  if (get_S psr_val) = 0 then  
    bitAND (bitOR tmp0 ((ucast cwp_val)::word32)) (0b11111111111111111111111101111111::word32)
  else
    bitOR (bitOR tmp0 ((ucast cwp_val)::word32)) (0b00000000000000000000000010000000::word32)"

text {* Update the the ET, CWP, and S fields of PSR. Return the new value of PSR. *}
  
definition update_PSR_rett :: "word5 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_PSR_rett cwp_val et_val s_val psr_val \<equiv>
  let tmp0 = bitAND psr_val 0b11111111111111111111111101000000;
      tmp1 = bitOR tmp0 ((ucast cwp_val)::word32);
      tmp2 = bitOR tmp1 (((ucast et_val)::word32) << 5); 
      tmp3 = bitOR tmp2 (((ucast s_val)::word32) << 7)
  in  
  tmp3"

definition update_PSR_exe_trap :: "word5 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_PSR_exe_trap cwp_val et_val ps_val psr_val \<equiv>
  let tmp0 = bitAND psr_val 0b11111111111111111111111110000000;
      tmp1 = bitOR tmp0 ((ucast cwp_val)::word32);
      tmp2 = bitOR tmp1 (((ucast et_val)::word32) << 5); 
      tmp3 = bitOR tmp2 (((ucast ps_val)::word32) << 6)
  in  
  tmp3"

text {* Update the N, Z, V, C fields of PSR. Return the new value of PSR. *}
  
definition update_PSR_icc :: "word1 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word1 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_PSR_icc n_val z_val v_val c_val psr_val \<equiv>
  let
      n_val_32 = if n_val = 0 then 0 
                 else       (0b00000000100000000000000000000000::word32); 
      z_val_32 = if z_val = 0 then 0 
                 else       (0b00000000010000000000000000000000::word32); 
      v_val_32 = if v_val = 0 then 0 
                 else       (0b00000000001000000000000000000000::word32);
      c_val_32 = if c_val = 0 then 0 
                 else       (0b00000000000100000000000000000000::word32);
      tmp0 = bitAND psr_val (0b11111111000011111111111111111111::word32);
      tmp1 = bitOR tmp0 n_val_32;
      tmp2 = bitOR tmp1 z_val_32;
      tmp3 = bitOR tmp2 v_val_32;
      tmp4 = bitOR tmp3 c_val_32
  in
  tmp4"

text {* Update the ET, PIL fields of PSR. Return the new value of PSR. *}
  
definition update_PSR_et_pil :: "word1 \<Rightarrow> word4 \<Rightarrow> word32 \<Rightarrow> word32" where
"update_PSR_et_pil et pil psr_val \<equiv>
  let tmp0 = bitAND psr_val 0b111111111111111111111000011011111;
      tmp1 = bitOR tmp0 (((ucast et)::word32) << 5);
      tmp2 = bitOR tmp1 (((ucast pil)::word32) << 8)
  in
  tmp2"   
   
text {* annul is a flag set by branching instructions. If it's true, 
then the next instruction is skipped. *}   

record sparc_proc_var =
annul:: bool

text {* We assume that each memory operation block (a list of instructions) is 
identified by a unique number. *}

type_synonym op_id = nat   

text {* The atomic flag for memory access. This flag is global for all processors. 
If the execution is "locked" by an atomic load/store, 
the atomic_flag gives the op_id of the load part that locks the execution.
Otherwise (the execution is not "locked" by atomic load/store), it is none. *}

record global_var =   
atomic_flag:: "op_id option" 
atomic_rd:: "register_value"

text {* Given a word7 value, find the highest bit,
        and fill the left bits to be the highest bit. *}
definition sign_ext7::"word7 \<Rightarrow> word32"
where
"sign_ext7 w \<equiv> 
  let highest_bit = (bitAND w 0b1000000) >> 6 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111111111111111111110000000
"

definition zero_ext8 :: "word8 \<Rightarrow> word32"
where
"zero_ext8 w \<equiv> (ucast w)::word32
"

text {* Given a word8 value, find the highest bit,
        and fill the left bits to be the highest bit. *}
definition sign_ext8::"word8 \<Rightarrow> word32"
where
"sign_ext8 w \<equiv> 
  let highest_bit = (bitAND w 0b10000000) >> 7 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111111111111111111100000000
"

text {* Given a word13 value, find the highest bit,
        and fill the left bits to be the highest bit. *}
definition sign_ext13::"word13 \<Rightarrow> word32"
where
"sign_ext13 w \<equiv> 
  let highest_bit = (bitAND w 0b1000000000000) >> 12 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111111111111110000000000000
"

definition zero_ext16 :: "word16 \<Rightarrow> word32"
where
"zero_ext16 w \<equiv> (ucast w)::word32
"

text {* Given a word16 value, find the highest bit,
        and fill the left bits to be the highest bit. *}
definition sign_ext16::"word16 \<Rightarrow> word32"
where
"sign_ext16 w \<equiv> 
  let highest_bit = (bitAND w 0b1000000000000000) >> 15 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111111111110000000000000000
"

text {* Given a word22 value, find the highest bit,
        and fill the left bits to tbe the highest bit. *}
definition sign_ext22::"word22 \<Rightarrow> word32"
where
"sign_ext22 w \<equiv>
  let highest_bit = (bitAND w 0b1000000000000000000000) >> 21 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111110000000000000000000000
"

text {* Given a word24 value, find the highest bit,
        and fill the left bits to tbe the highest bit. *}
definition sign_ext24::"word24 \<Rightarrow> word32"
where
"sign_ext24 w \<equiv>
  let highest_bit = (bitAND w 0b100000000000000000000000) >> 23 in
  if highest_bit = 0 then
    (ucast w)::word32
  else bitOR ((ucast w)::word32) 0b11111111000000000000000000000000
"

text {* Below are legacy definitions of the types of instructions defined 
in the SPARCv8 ISA formal model. We will only use a subset of these instructions
in this model. *}

text {* The CALL instruction. *}
datatype call_type = CALL  \<comment> \<open>"Call and Link"\<close>

text {* The SETHI instruction. *}
datatype sethi_type = SETHI     \<comment> \<open>"Set High 22 bits of r Register"\<close>

text {* The NOP instruction. *}
datatype nop_type = NOP       \<comment> \<open>"No Operation"\<close>

text {* The Branch on integer condition codes instructions. *} 
datatype bicc_type = 
  BE        \<comment> \<open>"Branch on Equal"\<close>
 | BNE       \<comment> \<open>"Branch on Not Equal"\<close>
 | BGU       \<comment> \<open>"Branch on Greater Unsigned"\<close>
 | BLE       \<comment> \<open>"Branch on Less or Equal"\<close>
 | BL        \<comment> \<open>"Branch on Less"\<close>
 | BGE       \<comment> \<open>"Branch on Greater or Equal"\<close>
 | BNEG      \<comment> \<open>"Branch on Negative"\<close>
 | BG        \<comment> \<open>"Branch on Greater"\<close>
 | BCS       \<comment> \<open>"Branch on Carry Set (Less than, Unsigned)"\<close>
 | BLEU      \<comment> \<open>"Branch on Less or Equal Unsigned"\<close>
 | BCC       \<comment> \<open>"Branch on Carry Clear (Greater than or Equal, Unsigned)"\<close>
 | BA        \<comment> \<open>"Branch Always"\<close>
 | BN        \<comment> \<open>"Branch Never"\<close> \<comment>\<open> Added for unconditional branches \<close>
 | BPOS      \<comment> \<open>"Branch on Positive"\<close>
 | BVC       \<comment> \<open>"Branch on Overflow Clear"\<close>
 | BVS       \<comment> \<open>"Branch on Overflow Set"\<close>

text {* Memory instructions. That is, load and store. *}
datatype load_store_type =
  LDSB      \<comment> \<open>"Load Signed Byte"\<close>
 | LDUB      \<comment> \<open>"Load Unsigned Byte"\<close>
 | LDUBA     \<comment> \<open>"Load Unsigned Byte from Alternate space"\<close>
 | LDUH      \<comment> \<open>"Load Unsigned Halfword"\<close>
 | LD        \<comment> \<open>"Load Word"\<close>
 | LDA       \<comment> \<open>"Load Word from Alternate space"\<close>
 | LDD       \<comment> \<open>"Load Doubleword"\<close>
 | STB       \<comment> \<open>"Store Byte"\<close>
 | STH       \<comment> \<open>"Store Halfword"\<close>
 | ST        \<comment> \<open>"Store Word"\<close>
 | STA       \<comment> \<open>"Store Word into Alternate space"\<close>
 | STD       \<comment> \<open>"Store Doubleword"\<close>
 | LDSBA     \<comment> \<open>"Load Signed Byte from Alternate space"\<close>
 | LDSH      \<comment> \<open>"Load Signed Halfword"\<close>
 | LDSHA     \<comment> \<open>"Load Signed Halfword from Alternate space"\<close>
 | LDUHA     \<comment> \<open>"Load Unsigned Halfword from Alternate space"\<close>
 | LDDA      \<comment> \<open>"Load Doubleword from Alternate space"\<close>
 | STBA      \<comment> \<open>"Store Byte into Alternate space"\<close>
 | STHA      \<comment> \<open>"Store Halfword into Alternate space"\<close>
 | STDA      \<comment> \<open>"Store Doubleword into Alternate space"\<close>
 | LDSTUB    \<comment> \<open>"Atomic Load Store Unsigned Byte"\<close>
 | LDSTUBA   \<comment> \<open>"Atomic Load Store Unsinged Byte in Alternate space"\<close>
 | SWAP      \<comment> \<open>"Swap r Register with Mmemory"\<close>
 | SWAPA     \<comment> \<open>"Swap r Register with Mmemory in Alternate space"\<close>
 | SWAP_LD    \<comment> \<open>"The load part of SWAP"\<close>
 | SWAP_ST    \<comment> \<open>"The store part of SWAP"\<close>
 | FLUSH     \<comment> \<open>"Flush Instruction Memory"\<close>
 | STBAR     \<comment> \<open>"Store Barrier"\<close>
 | CASA      \<comment> \<open>"Compare and Swap Word from Alternate space"\<close>
 | CASXA     \<comment> \<open>"Compare and Swap Extended from Alternate space"\<close>
 | CASA_LD    \<comment> \<open>"The load part of CASA"\<close>
 | CASA_ST    \<comment> \<open>"The store part of CASA"\<close>

text {* Arithmetic instructions. *}
datatype arith_type =
  ADD       \<comment> \<open>"Add"\<close>
 | ADDcc     \<comment> \<open>"Add and modify icc"\<close>
 | ADDX      \<comment> \<open>"Add with Carry"\<close>
 | SUB       \<comment> \<open>"Subtract"\<close>
 | SUBcc     \<comment> \<open>"Subtract and modify icc"\<close>
 | SUBX      \<comment> \<open>"Subtract with Carry"\<close>
 | UMUL      \<comment> \<open>"Unsigned Integer Multiply"\<close>
 | SMUL      \<comment> \<open>"Signed Integer Multiply"\<close>
 | SMULcc    \<comment> \<open>"Signed Integer Multiply and modify icc"\<close>
 | UDIV      \<comment> \<open>"Unsigned Integer Divide"\<close>
 | UDIVcc    \<comment> \<open>"Unsigned Integer Divide and modify icc"\<close>
 | SDIV      \<comment> \<open>"Signed Integer Divide"\<close>
 | ADDXcc    \<comment> \<open>"Add with Carry and modify icc"\<close>
 | TADDcc    \<comment> \<open>"Tagged Add and modify icc"\<close>
 | TADDccTV  \<comment> \<open>"Tagged Add and modify icc and Trap on overflow"\<close>
 | SUBXcc    \<comment> \<open>"Subtract with Carry and modify icc"\<close>
 | TSUBcc    \<comment> \<open>"Tagged Subtract and modify icc"\<close>
 | TSUBccTV  \<comment> \<open>"Tagged Subtract and modify icc and Trap on overflow"\<close>
 | MULScc    \<comment> \<open>"Multiply Step and modify icc"\<close>
 | UMULcc    \<comment> \<open>"Unsigned Integer Multiply and modify icc"\<close>
 | SDIVcc    \<comment> \<open>"Signed Integer Divide and modify icc"\<close>

text {* Logical instructions. *}
datatype logic_type =
  ANDs       \<comment> \<open>"And"\<close>
 | ANDcc     \<comment> \<open>"And and modify icc"\<close>
 | ANDN      \<comment> \<open>"And Not"\<close>
 | ANDNcc    \<comment> \<open>"And Not and modify icc"\<close>
 | ORs        \<comment> \<open>"Inclusive-Or"\<close>
 | ORcc      \<comment> \<open>"Inclusive-Or and modify icc"\<close>
 | ORN       \<comment> \<open>"Inclusive Or Not"\<close>
 | XORs       \<comment> \<open>"Exclusive-Or"\<close>
 | XNOR      \<comment> \<open>"Exclusive-Nor"\<close>
 | ORNcc     \<comment> \<open>"Inclusive-Or Not and modify icc"\<close>
 | XORcc     \<comment> \<open>"Exclusive-Or and modify icc"\<close>
 | XNORcc    \<comment> \<open>"Exclusive-Nor and modify icc"\<close>
 
text {* Shift instructions.*}
datatype shift_type =
  SLL       \<comment> \<open>"Shift Left Logical"\<close>
 | SRL       \<comment> \<open>"Shift Right Logical"\<close>
 | SRA       \<comment> \<open>"Shift Right Arithmetic"\<close> 

text {* Other Control-transfer instructions. *}
datatype ctrl_type = 
  JMPL      \<comment> \<open>"Jump and Link"\<close>
 | RETT      \<comment> \<open>"Return from Trap"\<close>
 | SAVE      \<comment> \<open>"Save caller's window"\<close>
 | RESTORE   \<comment> \<open>"Restore caller's window"\<close> 

text {* Access state registers instructions. *}
datatype sreg_type =
  RDASR     \<comment> \<open>"Read Ancillary State Register"\<close>
 | RDY       \<comment> \<open>"Read Y Register"\<close>
 | RDPSR     \<comment> \<open>"Read Processor State Register"\<close>
 | RDWIM     \<comment> \<open>"Read Window Invalid Mask Register"\<close>
 | RDTBR     \<comment> \<open>"Read Trap Base Regiser"\<close>
 | WRASR     \<comment> \<open>"Write Ancillary State Register"\<close>
 | WRY       \<comment> \<open>"Write Y Register"\<close>
 | WRPSR     \<comment> \<open>"Write Processor State Register"\<close>
 | WRWIM     \<comment> \<open>"Write Window Invalid Mask Register"\<close>
 | WRTBR     \<comment> \<open>"Write Trap Base Register"\<close> 

text {* Unimplemented instruction. *}
datatype uimp_type = UNIMP     \<comment> \<open>"Unimplemented"\<close>

text {* Trap on integer condition code instructions. *}
datatype ticc_type =
 TA        \<comment> \<open>"Trap Always"\<close>
 | TN        \<comment> \<open>"Trap Never"\<close>
 | TNE       \<comment> \<open>"Trap on Not Equal"\<close>
 | TE        \<comment> \<open>"Trap on Equal"\<close>
 | TG        \<comment> \<open>"Trap on Greater"\<close>
 | TLE       \<comment> \<open>"Trap on Less or Equal"\<close>
 | TGE       \<comment> \<open>"Trap on Greater or Equal"\<close>
 | TL        \<comment> \<open>"Trap on Less"\<close>
 | TGU       \<comment> \<open>"Trap on Greater Unsigned"\<close>
 | TLEU      \<comment> \<open>"Trap on Less or Equal Unsigned"\<close>
 | TCC       \<comment> \<open>"Trap on Carry Clear (Greater than or Equal, Unsigned)"\<close>
 | TCS       \<comment> \<open>"Trap on Carry Set (Less Than, Unsigned)"\<close>
 | TPOS      \<comment> \<open>"Trap on Postive"\<close>
 | TNEG      \<comment> \<open>"Trap on Negative"\<close>
 | TVC       \<comment> \<open>"Trap on Overflow Clear"\<close>
 | TVS       \<comment> \<open>"Trap on Overflow Set"\<close>

datatype sparc_operation =
  call_type call_type
 | sethi_type sethi_type
 | nop_type nop_type
 | bicc_type bicc_type
 | load_store_type load_store_type
 | arith_type arith_type
 | logic_type logic_type
 | shift_type shift_type
 | ctrl_type ctrl_type
 | sreg_type sreg_type
 | uimp_type uimp_type
 | ticc_type ticc_type

text {* An instruction is defined as a tuple composed of a @{term sparc_operation} element,
defining the operation the instruction carries out, and a list of operands 
@{term inst_operand}. *}
  
datatype inst_operand = 
W5 word5
|W30 word30
|W22 word22
|Cond  word4
|Flag word1
|Simm13 word13 
|Opf word9
|Imm7 word7
|Asi word8     
   
type_synonym instruction = "(sparc_operation \<times> inst_operand list)"   
   
text {* The types of memory operation block. *}   
   
datatype mem_op_block_type =
ld_block     \<comment> \<open>"A block of instructions that ends with a LD"\<close>
|st_block    \<comment> \<open>"A block of instructions that ends with a ST"\<close>
|ald_block   \<comment> \<open>"A block of instructions that ends with the load part of SWAP or CASA"\<close>
|ast_block   \<comment> \<open>"A block of instructions that ends with the store part of SWAP or CASA"\<close>
|o_block     \<comment> \<open>"A block of instructions that ends with other instructions"\<close>
 
text {* proc can be seen as a processor or a software process in multi-processor machines. *}

type_synonym proc = nat 

consts max_proc :: nat 
  
text {* The execution semantics in our memory model is memory operation oriented. 
Given a sequence of instructions in an execution instance, we divide the sequence
into "memory operation blocks". Each "memory operation block" has at most one 
memory access instruction, which must be the last instruction in the block. 
N.B. Given a sequence of instructions in an execution, all mem_op_blocks 
should have 1 memory access instruction, except for the last block. 
We also give each block a unique number as an identifier. 
The fields op_addr and op_val are None in initialisation. They are added when the 
corresponding memory access instruction is executed by the processor. *}

overloading max_proc \<equiv> max_proc
begin
definition "max_proc = 5"
end 

record mem_op_state =
op_addr:: "virtual_address option"
op_val:: "memory_value option"  

record program_block =   
insts:: "instruction list"
op_proc:: proc
atom_pair_id:: "op_id option"
  
definition "emp_prog_block \<equiv> \<lparr>insts = [], op_proc = 0, atom_pair_id = None\<rparr>"

definition emp_mem_op_state:: "mem_op_state" where 
"emp_mem_op_state \<equiv> \<lparr>op_addr = None, op_val = None\<rparr>"

text {* Get the type of the mem_op_block. *}

definition type_of_mem_op_block:: "program_block \<Rightarrow> mem_op_block_type" where  
"type_of_mem_op_block b \<equiv> 
  if insts b = [] then o_block
  else 
    case fst (List.last (insts b)) of 
    load_store_type LD \<Rightarrow> ld_block
    |load_store_type ST \<Rightarrow> st_block
    |load_store_type SWAP_LD \<Rightarrow> ald_block
    |load_store_type CASA_LD \<Rightarrow> ald_block
    |load_store_type SWAP_ST \<Rightarrow> ast_block
    |load_store_type CASA_ST \<Rightarrow> ast_block
    |_ \<Rightarrow> o_block"    
  
end

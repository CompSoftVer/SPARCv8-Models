\<comment>\<open>  Title:     State.thy
    Author:    David Sanán, Trinity College Dublin, 2012
\<close>

text {* "Word Declarations" *}

theory WordDecl
imports Main "HOL-Word.Word"
begin

text {*
This theory provides @{text "len0"} and @{text "len"} instantiations 
for the most common used word sizes in the model (1,2,4,5,6,8,12,16,18,20,24,32,36).
The @{text "len0"} class defines lengths that range from 0 upwards,
whilst the @{text "len"} class caters for non-zero lengths.
Bit-operators like @{text "<<"}, @{text ">>"}, @{text "and"}, or @{text "or"} 
require @{text "a'::len"} word instances,
while other word operations such @{term "ucast"} 
(gets an integer from a word) 
can be defined for @{text "len0"} words. 
\par
For each length @{term "N"}, we:
\begin{enumerate}
  \item declare a type @{text "word-lengthN"};
  \item make it an instance of both length classes;
 \item and introduce a short type synonym @{text "wordN"}, and a suitable translation.
\end{enumerate}
In essence, this theory is just a lot of boilerplate.
\newpage
*}

section "Words of length 1"

\<comment>\<open> typedecl word_length1
instantiation word_length1 :: len0
begin
definition
  len1 [simp]: "len_of (x::word_length1 itself) \<equiv> 1"
instance .. 
end
instantiation word_length1 :: len
begin
instance by intro_classes simp
end\<close>
type_synonym word1 = "1 word"
\<comment>\<open> translations (type) "word1" <= (type) "word_length1 word" \<close>

subsection "Words of length 1's constants"

definition ONE::"word1"
where
"ONE \<equiv> 1"

definition ZERO::"word1"
where
"ZERO \<equiv> 0"

section "Words of length 2"

\<comment>\<open> typedecl word_length2
instantiation word_length2 :: len0
begin
definition
  len2 [simp]: "len_of (x::word_length2 itself) \<equiv> 2"
instance .. 
end
instantiation word_length2 :: len
begin
instance by intro_classes simp
end\<close>
type_synonym word2 = "2 word"
\<comment>\<open> translations (type) "word2" <= (type) "word_length2 word" \<close>

section "Words of length 3"

\<comment>\<open> typedecl word_length3
instantiation word_length3 :: len0
begin
definition
  len3 [simp]: "len_of (x::word_length3 itself) \<equiv> 3"
instance .. 
end
instantiation word_length3 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word3 = "3 word"
\<comment>\<open> translations (type) "word3" <= (type) "word_length3 word" \<close>

section "Words of length 4"

\<comment>\<open> typedecl word_length4
instantiation word_length4 :: len0
begin
definition
  len4 [simp]: "len_of (x::word_length4 itself) \<equiv> 4"
instance .. 
end
instantiation word_length4 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word4 = "4 word"
\<comment>\<open> translations (type) "word4" <= (type) "word_length4 word" \<close>

section "Words of length 5"

\<comment>\<open> typedecl word_length5
instantiation word_length5 :: len0
begin
definition
  len5 [simp]: "len_of (x::word_length5 itself) \<equiv> 5"
instance .. 
end
instantiation word_length5 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word5 = "5 word"
\<comment>\<open> translations (type) "word5" <= (type) "word_length5 word" \<close>

section "Words of length 6"

\<comment>\<open> typedecl word_length6
instantiation word_length6 :: len0
begin
definition
  len6 [simp]: "len_of (x::word_length6 itself) \<equiv> 6"
instance .. 
end
instantiation word_length6 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word6 = "6 word" 
\<comment>\<open> translations (type) "word6" <= (type) "word_length6 word" \<close>

section "Words of length 6"

\<comment>\<open> typedecl word_length7
instantiation word_length7 :: len0
begin
definition
  len7 [simp]: "len_of (x::word_length7 itself) \<equiv> 7"
instance .. 
end
instantiation word_length7 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word7 = "7 word"
\<comment>\<open> translations (type) "word7" <= (type) "word_length7 word" \<close>

section "Words of length 8"

\<comment>\<open> typedecl word_length8
instantiation word_length8 :: len0
begin
definition
  len8 [simp]: "len_of (x::word_length8 itself) \<equiv> 8"
instance .. 
end
instantiation word_length8 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word8 = "8 word"
\<comment>\<open> translations (type) "word8" <= (type) "word_length8 word" \<close>

section "Words of length 9"

\<comment>\<open> typedecl word_length9
instantiation word_length9 :: len0
begin
definition
  len9 [simp]: "len_of (x::word_length9 itself) \<equiv> 9"
instance .. 
end
instantiation word_length9 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word9 = "9 word"
\<comment>\<open> translations (type) "word9" <= (type) "word_length9 word" \<close>

section "Words of length 10"

typedecl word_length10
\<comment>\<open> instantiation word_length10 :: len0
begin
definition
  len10 [simp]: "len_of (x::word_length10 itself) \<equiv> 10"
instance .. 
end
instantiation word_length10 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word10 = "10 word"
\<comment>\<open> translations (type) "word10" <= (type) "word_length10 word" \<close>

section "Words of length 12"

\<comment>\<open> typedecl word_length12
instantiation word_length12 :: len0
begin
definition
  len12 [simp]: "len_of (x::word_length12 itself) \<equiv> 12"
instance .. 
end
instantiation word_length12 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word12 = "12 word"
\<comment>\<open> translations (type) "word12" <= (type) "word_length12 word" \<close>

section "Words of length 13"

\<comment>\<open> typedecl word_length13
instantiation word_length13 :: len0
begin
definition
  len13 [simp]: "len_of (x::word_length13 itself) \<equiv> 13"
instance .. 
end
instantiation word_length13 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word13 = "13 word"
\<comment>\<open> translations (type) "word13" <= (type) "word_length13 word" \<close>

section "Words of length 16"

\<comment>\<open> typedecl word_length16
instantiation word_length16 :: len0
begin
definition
  len16 [simp]: "len_of (x::word_length16 itself) \<equiv> 16"
instance .. 
end
instantiation word_length16 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word16 = "16 word"
\<comment>\<open> translations (type) "word16" <= (type) "word_length16 word" \<close>

section "Words of length 18"

\<comment>\<open> typedecl word_length18
instantiation word_length18 :: len0
begin
definition
  len18 [simp]: "len_of (x::word_length18 itself) \<equiv> 18"
instance .. 
end
instantiation word_length18 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word18 = "18 word"
\<comment>\<open> translations (type) "word18" <= (type) "word_length18 word" \<close>

section "Words of length 20"

\<comment>\<open> typedecl word_length20
instantiation word_length20 :: len0
begin
definition
  len20 [simp]: "len_of (x::word_length20 itself) \<equiv> 20"
instance .. 
end
instantiation word_length20 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word20 = "20 word"
\<comment>\<open> translations (type) "word20" <= (type) "word_length20 word" \<close>

section "Words of length 22"

\<comment>\<open> typedecl word_length22
instantiation word_length22 :: len0
begin
definition
  len22 [simp]: "len_of (x::word_length22 itself) \<equiv> 22"
instance .. 
end
instantiation word_length22 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word22 = "22 word"
\<comment>\<open> translations (type) "word22" <= (type) "word_length22 word" \<close>

section "Words of length 24"

\<comment>\<open> typedecl word_length24
instantiation word_length24 :: len0
begin
definition
  len24 [simp]: "len_of (x::word_length24 itself) \<equiv> 24"
instance .. 
end
instantiation word_length24 :: len
begin 
instance by intro_classes simp 
end \<close>
type_synonym word24 = "24 word"
\<comment>\<open> translations (type) "word24" <= (type) "word_length24 word" \<close>

section "Words of length 30"

\<comment>\<open> typedecl word_length30
instantiation word_length30 :: len0
begin
definition
  len30 [simp]: "len_of (x::word_length30 itself) \<equiv> 30"
instance .. 
end
instantiation word_length30 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word30 = "30 word"
\<comment>\<open> translations (type) "word30" <= (type) "word_length30 word" \<close>

section "Words of length 31"

\<comment>\<open> typedecl word_length31
instantiation word_length31 :: len0
begin
definition
  len31 [simp]: "len_of (x::word_length31 itself) \<equiv> 31"
instance .. 
end
instantiation word_length31 :: len
begin
instance by intro_classes simp
end \<close>
type_synonym word31 = "32 word"
\<comment>\<open> translations (type) "word31" <= (type) "word_length31 word" \<close>

section "Words of length 32"

\<comment>\<open> typedecl word_length32
instantiation word_length32 :: len0
begin
definition
  len32 [simp]: "len_of (x::word_length32 itself) \<equiv> 32"
instance .. 
end
instantiation word_length32 :: len
begin                            
instance by intro_classes simp
end \<close>
type_synonym word32 = "32 word"
\<comment>\<open> translations (type) "word32" <= (type) "word_length32 word" \<close>

section "Words of length 33"

\<comment>\<open> typedecl word_length33
instantiation word_length33 :: len0
begin
definition
  len33 [simp]: "len_of (x::word_length33 itself) \<equiv> 33"
instance .. 
end
instantiation word_length33 :: len
begin                            
instance by intro_classes simp
end \<close>
type_synonym word33 = "33 word"
\<comment>\<open> translations (type) "word33" <= (type) "word_length33 word" \<close>

section "Words of length 36"

\<comment>\<open> typedecl word_length36
instantiation word_length36 :: len0
begin
definition
  len36 [simp]: "len_of (x::word_length36 itself) \<equiv> 36"
instance ..
end
instantiation word_length36 :: len
begin
  instance by intro_classes simp
end \<close>
type_synonym word36 = "36 word"
\<comment>\<open> translations (type) "word36" <= (type) "word_length36 word" \<close>

section "Words of length 64"

\<comment>\<open> typedecl word_length64
instantiation word_length64 :: len0
begin
definition
  len64 [simp]: "len_of (x::word_length64 itself) \<equiv> 64"
instance ..
end
instantiation word_length64 :: len
begin
  instance by intro_classes simp
end\<close>
type_synonym word64 = "64 word"
\<comment>\<open> translations (type) "word64" <= (type) "word_length64 word" \<close>

end




theory word1 
  imports "Word_Lib.Word_Lib"
begin
thm word_leI word_and_le2
value "(1::5 word)!!0"

lemma b:assumes a0:"(v <  2^(((size v) - 1)))" 
        shows"\<not> ((v::('a::len) word)!! ((size v) - 1))"
proof-
  {assume a00: "((v::('a::len) word)!! ((size v) - 1))"
    have "v\<ge>  2^(((size v) - 1))" using a00
      using bang_is_le by blast
    then have  ?thesis using a0 by auto
  } thus ?thesis by auto 
qed


lemma a1:assumes a0:"\<not> ((v::('a::len) word)!! ((size v) - 1))" 
  shows "v \<le>  2^((size v) - 1) - 1"
proof -  
  have f2: "size v = Suc (size v - 1)"  
    by (meson Suc_pred' word_size_gt_0)
  moreover have f3: "size (mask (size v - 1)::'a word) = size v"
    by (simp add: word_size)
  moreover have  f4: "set_bit v (size v - 1) False = v"
    by (metis (full_types) a0 word_set_nth)
  ultimately show ?thesis
    using mask_2pm1 nat_neq_iff nth_mask test_bit_set_gen
    by (metis less_SucE word_leI)  
qed

lemma  a:assumes a0:"\<not> ((v::('a::len) word)!! ((size v) - 1))" 
  shows "(v <  2^(((size v) - 1)))"
using  a1[OF a0] by (simp add: le_less_trans power_2_ge_iff wsst_TYs(3))

  
lemma c:"\<not> ((v::('a::len) word)!! ((size v) - 1)) = (v <  2^(((size v) - 1)))"
  using a b by auto


end
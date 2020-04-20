theory word_aux
imports Word_Lib.Word_Lemmas_32 Word_Lib.WordSetup
begin
lemma unat_of_int_32[simp]: "0 \<le> i \<Longrightarrow> i \<le> 2 ^ 32 - 1 \<Longrightarrow> unat ((of_int i)::32 word) = nat i"
  unfolding unat_def
  apply (subst eq_nat_nat_iff, clarsimp+)
  apply (subst word_of_int)
  apply (subst uint_word_of_int)
  by simp

lemma takeWhile_take: "length (takeWhile P xs) \<le> n \<Longrightarrow> takeWhile P (take n xs) = takeWhile P xs"
proof (induction xs arbitrary:n rule:rev_induct)
  case (snoc x xs)
  show ?case
    apply (cases "n \<ge> length (xs @ [x])")
    apply (auto simp: not_le)
    apply (cases "list_all P xs")
    subgoal
      apply (auto simp: list_all_iff)
      using snoc(2)
      by auto
    subgoal
      using snoc takeWhile_append1
      by (metis list.pred_set)
    done
qed auto

lemma takeWhile_all: "length (takeWhile P xs) = length xs \<Longrightarrow> list_all P xs"
  by (simp add: list_all_length takeWhile_take_has_property_nth)

lemma word_is_zero: "word_of_int i = (0::'a::len0 word) \<Longrightarrow> i mod (2 ^ len_of TYPE('a)) = 0"
  by (metis uint_eq_0 word_uint.eq_norm)

lemma clz_shift_32_step':
  assumes "i > 0" "i \<le> 2 ^ 32 - 1"
  shows "word_clz (((of_int i)::32 word) >> 1) = word_clz ((of_int i)::32 word) + 1"
  unfolding word_clz_def
  apply (subst bl_shiftr)
  apply (auto simp: word_size)
using assms proof -
  assume "i > 0" "i \<le> 2 ^ 32 - 1"
  let ?r = "length (takeWhile Not (to_bl ((of_int i)::32 word)))" and
      ?l = "length (takeWhile Not (take 31 (to_bl ((of_int i)::32 word))))" and
      ?bl = "to_bl((of_int i)::32 word)"
  have "?r \<le> 32"
    using List.length_takeWhile_le[where xs = ?bl, unfolded word_size_bl[symmetric]]
    by (simp add: word_size)
  moreover have "?r \<noteq> 32"
  proof (rule ccontr, simp)
    assume "?r = 32"
    also have "length ?bl = 32"
      by (simp add: word_size)
    finally have "list_all Not ?bl"
      using takeWhile_all by metis
    then have "True \<notin> set ?bl"
      by (metis Ball_set_list_all)
    then have "((of_int i)::32 word) = 0"
      using eq_zero_set_bl by blast
    with \<open>i > 0\<close> \<open>i \<le> _\<close> show False
      apply -
      apply (subst (asm) word_of_int)
      apply (drule word_is_zero)
      by auto
  qed
  ultimately have "?r \<le> 31"
    by simp
  from takeWhile_take[OF this]
  show "?l = ?r"
    by simp
qed

lemma clz_shift_32_step: 
  assumes "i > 0" "i \<le> 2 ^ 32 - 1" (* i \<le> 2 ^ 32 - 1 is necessary *)
  shows "word_clz ((of_int (i div 2))::32 word) = word_clz ((of_int i)::32 word) + 1"
  using clz_shift_32_step'[OF assms]
  apply -
  apply (subst (asm) shiftr1_is_div_2[of "(of_int i)::32 word"])
  unfolding word_div_def
  apply (subst (asm) word_of_int)
  apply (subst (asm) uint_word_of_int)
  apply (subst word_of_int)
  unfolding word_of_int_def
  using assms 
  by auto

lemma int_le_trans: "i \<le> (j::int) \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k" (* could be removed *)
  by simp

lemma div_mult2_eq': "b \<ge> 0 \<Longrightarrow> a div (b * c) = (a div c) div (b::int)"
  by (smt zdiv_zmult2_eq mult.commute)

lemma zdiv_le_dividend': "m \<ge> 0 \<Longrightarrow> m div n \<le> (m::int)"
  by (smt nonneg1_imp_zdiv_pos_iff zdiv_le_dividend)  

lemma clz_shift_32: "i \<ge> 2 ^ n \<Longrightarrow> i \<le> 2 ^ 32 - 1 \<Longrightarrow> word_clz ((of_int i)::32 word) = word_clz ((of_int (i div 2 ^ n))::32 word) - n"
proof (induction n) 
  fix n
  assume IH: "(2::int) ^ (n::nat) \<le> i \<Longrightarrow> i \<le> 2 ^ 32 - 1 \<Longrightarrow> word_clz ((of_int i)::32 word) = word_clz ((of_int (i div (2::int) ^ n))::32 word) - n"
     and prem: "(2::int) ^ Suc n \<le> i" "i \<le> 2 ^ 32 - 1"
  from prem have "i > 0"
    using less_le_trans zless2p by blast
  have "word_clz ((of_int i)::32 word) = word_clz ((of_int (i div (2::int) ^ n))::32 word) - n"
    apply (rule IH)
    apply (rule int_le_trans)
    defer
    apply (rule prem)+
    by simp
  also have "... = word_clz ((of_int (i div (2::int) ^ Suc n))::32 word) - Suc n"
    apply simp
    apply (subst div_mult2_eq', simp)
    apply (subst clz_shift_32_step)
    using \<open>i > 0\<close> pos_imp_zdiv_pos_iff prem
    apply auto
    using zdiv_le_dividend'[of i]
    by smt
  finally show "word_clz ((of_int i)::32 word) = word_clz ((of_int (i div (2::int) ^ Suc n))::32 word) - Suc n"
    by auto
qed auto

thm word_eq_iff word_ops_nth_size
thm bin_nth_ops
thm word_eqI
thm uminus_word.abs_eq
thm unat_of_nat
thm bintrunc_mod2p

thm bin_add_not
thm bin_induct

lemma of_int_sign: "(of_int i::'a::len word) !! n = (of_int i::'a signed word) !! n"
proof (induction i arbitrary:n rule: bin_induct)
  case (3 bin bit)
  then show ?case
    apply -
    unfolding test_bit_wi word_of_int
    by (cases bit, auto)
qed auto

lemma uint_of_nat:
	"uint (of_nat x :: 'a::len word) = (int x) mod 2^ len_of TYPE('a)"
	apply (clarsimp simp only: uint_nat unat_of_nat)
  apply (metis of_nat_numeral semiring_1_class.of_nat_power zmod_int)
  done

definition ls_bit :: "'a :: len  word \<Rightarrow> nat option" where
"ls_bit w = (if w = 0 then None else 
            (Some (THE n. test_bit w n \<and> (\<forall>i < n. \<not>test_bit w i))))"

lemma ls_bit_1: "ls_bit 1 = Some 0"
  unfolding ls_bit_def
  by auto

lemma ls_bit_signed: "ls_bit (of_int i::'a::len word) = ls_bit (of_int i::'a::len signed word)"
  unfolding ls_bit_def
  apply (split if_splits)
  apply (intro conjI impI)
   apply (split if_splits)
   apply (intro conjI impI refl)
  apply (metis (full_types) nth_0 of_int_sign word_exists_nth)
  apply (split if_splits)
  apply (intro conjI impI)
   apply (metis (full_types) nth_0 of_int_sign word_exists_nth)
  apply (rule arg_cong[where f = Some])
  by (meson of_int_sign)

lemma ls_bit_not_zero:"w\<noteq>0 \<Longrightarrow> \<exists>n. ls_bit w = Some n"
  unfolding ls_bit_def by auto

lemma ls_bit_exists:"(w::'a :: len  word ) \<noteq> 0 \<Longrightarrow> \<exists>n. test_bit w n \<and> (\<forall>i < n. \<not>test_bit w i)"
proof (rule ccontr)
  assume a0:"w\<noteq>0"
  assume a1:"\<nexists>n. w !! n \<and> (\<forall>i<n. \<not> w !! i)" 
  then show False using word_exists_nth[OF a0] a1 by (meson  exists_least_iff) 
qed

lemma ls_bit_unique:"test_bit w n \<and> (\<forall>i < n. \<not>test_bit w i) \<Longrightarrow>
                     test_bit w n1 \<and> (\<forall>i < n1. \<not>test_bit w i) \<Longrightarrow>
                     n=n1"
  using nat_neq_iff by blast

lemma ls_bit_Some_not_zero:"ls_bit w = Some n \<Longrightarrow> w\<noteq>0"
  unfolding ls_bit_def by auto

lemma ls_bit_p: 
  assumes a0:"ls_bit w = Some n" 
  shows"test_bit w n \<and> (\<forall>i < n. \<not>test_bit w i)"
proof- 
  have u:"\<exists>!n. test_bit w n \<and> (\<forall>i < n. \<not>test_bit w i)"
    using ls_bit_exists[OF ls_bit_Some_not_zero[OF a0]] ls_bit_unique by auto
  thus ?thesis using ls_bit_Some_not_zero[OF a0] theI'[OF u] 
      a0[simplified ls_bit_def ls_bit_Some_not_zero[OF a0] if_False]  
    by blast
qed 

lemma ls_bit_less_length:"ls_bit w = Some n \<Longrightarrow> n < size w"
  by (fastforce dest: ls_bit_p simp :test_bit_size)

lemma power_ls_bit: "n < len_of TYPE('a::len) \<Longrightarrow> ls_bit ((2::'a::len word) ^ n) = Some n"
  unfolding ls_bit_def
  apply (rule the1I2)
  apply (auto simp:nth_w2p)
  done

declare[[show_types]]
lemma ls_bit_NOT:
  assumes a0:"ls_bit w = Some m" and
          a1:"w' = ( NOT w)"
  shows "\<not> test_bit w' m \<and> (\<forall>i < m. test_bit w' i)"
proof-
  have ls_bit:"test_bit w m \<and> (\<forall>i < m. \<not>test_bit w i)"
    using ls_bit_p[OF a0] by auto
  then have "\<not> test_bit w' m" using a1 
    by (simp add: test_bit_size word_ops_nth_size)
  moreover have "(\<forall>i < m. test_bit w' i)"
  proof-
    {fix i
      assume a00:"i<m"
      then have "\<not> test_bit w i" using conjunct2[OF ls_bit] by auto
      then have "test_bit w' i" using test_bit_size
        by (metis a00 a1 dual_order.strict_trans ls_bit word_ops_nth_size)    
    } thus ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma eqFalseI: "\<not>P \<Longrightarrow> P = False"
  by simp

lemma bin_plus_one_1: 
  assumes "\<not> bin_nth b m" and "\<forall>i<m. bin_nth b i"
  shows "bin_nth (b + (1::int)) m"
  using assms proof (induction b arbitrary :m rule: bin_induct)
  case (3 bin bit)
  show ?case 
  proof (cases bit)
    {
      case False
      with 3 have "m = 0"
        using bin_nth_0_BIT by blast
      with False show ?thesis 
        by auto
    next
      case True
      with 3 have "\<not> bin_nth bin (m-1)" "\<forall>i<(m-1). bin_nth bin i"
        apply (auto simp: bin_nth_Bit)
        by (metis (no_types) "3.prems"(2) add.right_neutral add_Suc_right bin_nth_Suc_BIT less_diff_conv)
      with 3 have "bin_nth (bin + 1) (m - 1)"
        by blast
      with True show ?thesis
        by (metis (mono_tags, lifting) "3.prems"(1) bin_nth_0_BIT bin_nth_minus not_gr_zero succ_BIT_simps(2))
    }
  qed
qed auto

lemma bin_plus_one_2:
  assumes "\<forall>i<m. bin_nth b i"and " i < m"
  shows " \<not> bin_nth (b + (1::int)) i"
using assms proof (induction b arbitrary:m i rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases bit)
    {
      case False
      with 3 have "m = 0"
        using bin_nth_0_BIT by blast
      with 3 show ?thesis
        by simp
    next
      case True
      with 3 have "\<forall>i<(m-1). bin_nth bin i"
        using less_diff_conv by auto
      with 3 have "\<forall>i < (m-1). \<not> bin_nth (bin + 1) i"
        by blast
      from True have "bit = True" by simp
      show ?thesis
        unfolding \<open>bit = _\<close>
        apply auto
        apply (cases i, auto)
        apply (subgoal_tac "nat < (m - 1)")
        using \<open>\<forall>i < (m-1). \<not> bin_nth _ _\<close>
         apply blast
        using \<open>i < m\<close>
        by simp
    }
  qed
qed auto

lemma bin_plus_one_3:
  assumes "\<not> bin_nth w m" and "i > m"
  shows "bin_nth (w+1) i = bin_nth w i"
  using assms proof (induction w arbitrary: i m rule:bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases bit)
    {
      case True
      with 3 have "m \<noteq> 0"
        by (meson bin_nth_0_BIT)
      with 3 have " \<not> bin_nth bin (m-1)"
        using bin_nth_minus by blast
      with 3 have "\<forall>i > (m-1).bin_nth (bin + 1) i = bin_nth bin i"
        by blast
      show ?thesis
        unfolding True[THEN eqTrueI]
        unfolding succ_BIT_simps
        apply (cases i)
        using \<open>i > m\<close> apply blast
        apply simp
        using \<open>i > m\<close> \<open>\<forall>i > (m-1).bin_nth _ _ = _\<close> \<open>(m::nat) \<noteq> (0::nat)\<close> 
        by auto
    next
      case False
      show ?thesis 
        unfolding \<open>\<not>bit\<close>[THEN eqFalseI]
        unfolding succ_BIT_simps
        apply (cases i)
        using \<open>i > m\<close> apply blast
        by simp
    }
  qed
qed auto

lemma ls_bit_SUCC:
  assumes "\<not> (w::'a::len word) !! m \<and> (\<forall>i < m. w !! i)" and
          "m < len_of TYPE('a::len)"
  shows "(w+1) !! m \<and> (\<forall>i < m. \<not> (w+1) !! i) \<and> (\<forall>i > m. (w+1) !! i = w !! i)"
  using assms apply transfer
  apply (auto simp: bin_plus_one_1 bin_plus_one_2 bin_plus_one_3)
  done
lemma word_and_complement':
  assumes "n < size w" and "w\<noteq>0"
  shows "((w::'a::len word) && - w) !! n = ((2::'a::len word) ^ the (ls_bit w)) !! n"
proof-
  obtain m where "ls_bit w = Some m" "the (ls_bit w) = m"
    using ls_bit_not_zero[OF \<open>w\<noteq>0\<close>] by auto
  then have "w !! m" "(\<forall>i < m. \<not> w !! i)"
    using ls_bit_p by auto
  hence "m < size w"
    by (simp add: test_bit_size)
  have "\<not> (NOT w)!! m" "(\<forall>i < m.(NOT w) !!i)"
    using ls_bit_NOT[OF \<open>ls_bit w = _\<close>] by auto
  hence "(- w) !! m " "(\<forall>i < m. \<not>(- w) !! i)" "\<forall>i > m. (- w) !! i = (NOT w) !! i"
    unfolding twos_complement
    unfolding word_succ_p1
    using ls_bit_SUCC \<open>m < _\<close>
    by (metis word_size)+
  with \<open>w !! m\<close> \<open>(\<forall>i < m. \<not> w !! i)\<close> 
  have "(w && -w) !! m"  "(\<forall>i < m. \<not> (w && -w) !! i)"
    using word_ops_nth_size[OF \<open>m < _\<close>] by force+
  moreover from \<open>\<forall>i > m. (- w) !! i = (NOT w) !! i\<close>
  have "\<forall>i > m. \<not> (w && - w) !! i"
    by (metis test_bit_bin word_ops_nth_size wsst_TYs(3))
  moreover have "((2::'a::len word) ^ m) !! m" 
    using nth_w2p_same  \<open>m < _\<close>
    by (auto simp: word_size)
  moreover have "\<forall>i \<noteq> m. \<not>((2::'a::len word) ^ m) !! i"
    by (simp add: nth_w2p) 
  ultimately have "(w && -w) !! n = ((2::'a::len word) ^ m) !! n"
    by (metis (full_types) linorder_neqE_nat)
  thus ?thesis unfolding \<open>the _ = _\<close> .
qed

declare[[coercion uint]]
value "bin_nth (4::4 word) 1"

lemma word_and_complement: "w \<noteq> 0 \<Longrightarrow> (w::('a :: len) word) && - w = 2 ^ (the (ls_bit w))"
  apply (subst word_eq_iff) 
  using word_and_complement'
  by (auto simp: word_size)

lemma power_ge1: "(2::nat) ^ n \<ge> 1"
  by simp

(* looks awful *)
lemma table_2_power: "(2::nat) ^ i \<le> 255 \<Longrightarrow> table.[2 ^ i] = of_int i"
  apply (cases i)
   apply (auto simp: table_simp)
  apply (case_tac nat)
   apply (auto simp: table_simp)
  apply (case_tac nata)
   apply (auto simp: table_simp)
  apply (case_tac nat)
   apply (auto simp: table_simp)
  apply (case_tac nata)
   apply (auto simp: table_simp)
  apply (case_tac nat)
   apply (auto simp: table_simp)
  apply (case_tac nata)
   apply (auto simp: table_simp)
  apply (case_tac nat)
   apply (auto simp: table_simp)
  using power_ge1
  using not_less_eq_eq by fastforce

lemma word_is_not_zeroI: " i mod (2 ^ len_of TYPE('a)) \<noteq> 0 \<Longrightarrow> word_of_int i \<noteq> (0::'a::len0 word)"
  by (metis uint_eq_0 word_uint.eq_norm)

lemma power_msb: "msb ((2 ::'a::len signed word) ^ n) = (n+1 = len_of TYPE('a))"
  by (auto simp: msb_nth nth_w2p)

lemma ls_bit_lower_bound: "ls_bit w = Some m \<Longrightarrow> w \<ge> 2 ^ m"
  by (fastforce dest:ls_bit_p intro:bang_is_le)

lemma mod_le_simp:"i> 0 \<Longrightarrow> i < m \<Longrightarrow> i mod m = (i::int)"
  by simp
lemma uint_2: "len_of TYPE('a) > 1 \<Longrightarrow> uint (2::'a::len word) = 2"
  by (metis (no_types) Euclidean_Division.mod_less le_def len_gt_0 mod2_gr_0 nat_neq_iff uint_2_id)
lemma the_some: "a = Some b \<Longrightarrow> the a = b"
  by simp

lemma ls_bit_less_length': "w \<noteq> 0 \<Longrightarrow> the (ls_bit (w :: 'a::len word)) < len_of TYPE('a)"
  unfolding ls_bit_def
  apply auto
  by (metis (mono_tags) ls_bit_def ls_bit_p test_bit_bin) 

lemma ls_bit_less_power: 
  assumes "i > 0" "(i::int) \<le> 2 ^ m - 1"
          "m \<le> len_of TYPE('a)"
        shows "the (ls_bit ((of_int i)::'a::len word)) < m"
proof (cases "len_of TYPE('a) > 1")
  case True
  show ?thesis
  proof -
    have "i < 2 ^ len_of TYPE('a)"
      using assms
      by (smt power_increasing) 
    obtain n where "ls_bit ((of_int i)::'a::len word) = Some n"
      apply atomize_elim
      apply (rule ls_bit_not_zero)
      apply (subst word_of_int)
      apply (rule word_is_not_zeroI)
      using assms
      by (smt int_mod_eq power_increasing) 
    hence *:"((of_int i)::'a::len word) \<ge> 2 ^ n"
      using ls_bit_lower_bound by blast
    from * have "i \<ge> 2 ^ n"
      apply -
      apply (subst (asm) word_arith_power_alt)
      apply (subst (asm) word_of_int)
      apply (subst (asm) wi_le)
      apply (subst (asm) mod_le_simp[OF \<open>i > 0\<close> \<open>i < 2 ^ _\<close>])
      apply (subst (asm) uint_2[OF True])
      using ls_bit_less_length[OF \<open> _ = Some _\<close>]
      by (simp add: word_size)
    with \<open>i \<le> _ - 1\<close> have "n < m"
      by (smt power_less_imp_less_exp)
    thus ?thesis unfolding the_some[OF \<open>_ = Some n\<close>, symmetric] .
  qed
next
  case False
  hence "LENGTH('a) = 0 \<or> LENGTH('a) = 1"
    by linarith
  with assms have "m = 0 \<or> m = 1"
    by auto
  thus ?thesis
    using assms
    apply auto
    by (smt of_int_1 tlsf.the_some ls_bit_1)
qed

lemma p_ge_8: "2 ^ p > (255::nat) \<Longrightarrow> p \<ge> 8" (* could be proved easier *)
  apply (rule ccontr)
  apply (drule not_le_imp_less)
  using power_strict_increasing[of p 8 "2::nat"]
  by force
lemma p_ge_16: "2 ^ p > (65535::nat) \<Longrightarrow> p \<ge> 16"
  apply (rule ccontr)
  apply (drule not_le_imp_less)
  using power_strict_increasing[of p 16 "2::nat"]
  by force
lemma p_ge_24: "2 ^ p > (16777215::nat) \<Longrightarrow> p \<ge> 24"
  apply (rule ccontr)
  apply (drule not_le_imp_less)
  using power_strict_increasing[of p 24 "2::nat"]
  by force

thm word_of_int_power_hom
thm word_arith_power_alt

lemma ls_bit_correct_8:
  assumes "(0::int) < i" "i \<le> (2147483647::int)"
    "nat (sint ((of_int i::32 sword) && - of_int i)) \<le> (65535::nat)"
    "(255::nat) < nat (sint ((of_int i::32 sword) && - of_int i))"
  shows "sint (table.[unat ((of_int (sint ((of_int i::32 sword) && - of_int i))::32 word) >> (8::nat))]) + (8::int)
         = int (the (ls_bit (of_int i::32 word)))"
proof -
    let ?ls = "the (ls_bit ((of_int i)::32 sword))"
    from assms(1-2) have "of_int i \<noteq> (0::32 sword)"
      by (auto simp:word_of_int word_is_not_zeroI)
    from assms(1-2) have "?ls < 31"
      by (auto intro: ls_bit_less_power)
    hence "?ls < LENGTH (32 signed)"
      by simp
    from \<open>?ls < 31\<close> have "2 ^ ?ls < (2::int) ^ 31"
      by (metis numeral_One numeral_less_iff power_strict_increasing_iff semiring_norm(76))
    have "256 = (2::nat) ^ 8"
      by eval
    from assms(4) have "?ls \<ge> 8"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      apply auto
      by (rule p_ge_8)
    from assms(3) have " (2::nat) ^ (?ls - (8::nat)) \<le> (255::nat)"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      by (subst power_diff[OF _ \<open>?ls \<ge> 8\<close>], auto)
    show ?thesis
      unfolding word_and_complement[OF \<open>of_int i \<noteq> _\<close>]
      apply (subst (2) word_sint_msb_eq)
      unfolding power_msb
      using \<open>the _ < 31\<close>
      apply simp
      apply (subst word_arith_power_alt)
      apply (subst word_ubin.eq_norm)
      unfolding bintrunc_mod2p
      apply simp
      apply (subst mod_le_simp)
      apply simp
      using \<open>2 ^ ?ls < _\<close>
      apply simp
      apply simp
      unfolding shiftr_div_2n'
      apply simp
      unfolding \<open>256 = _\<close>
      thm power_diff
      apply (subst power_diff[symmetric])
      using \<open>?ls \<ge> 8\<close> apply auto
      unfolding table_2_power[OF \<open>_ \<le> 255\<close>]
      apply(auto simp:sint_word_ariths)
      unfolding word_of_nat
      unfolding word_sbin.eq_norm
      using \<open>?ls \<ge> 8\<close> \<open>?ls < 31\<close>
      apply (auto simp:sbintrunc_mod2p) 
      using ls_bit_signed by metis
  qed

lemma ls_bit_correct_16:
  assumes "(0::int) < i" "i \<le> (2147483647::int)"
    "nat (sint ((of_int i::32 sword) && - of_int i)) \<le> (16777215::nat)"
    "(65535::nat) < nat (sint ((of_int i::32 sword) && - of_int i))"
  shows "sint (table.[unat ((of_int (sint ((of_int i::32 sword) && - of_int i))::32 word) >> (16::nat))]) + (16::int)
         = int (the (ls_bit (of_int i::32 word)))"
proof -
    let ?ls = "the (ls_bit ((of_int i)::32 sword))"
    from assms(1-2) have "of_int i \<noteq> (0::32 sword)"
      by (auto simp:word_of_int word_is_not_zeroI)
    from assms(1-2) have "?ls < 31"
      by (auto intro: ls_bit_less_power)
    hence "?ls < LENGTH (32 signed)"
      by simp
    from \<open>?ls < 31\<close> have "2 ^ ?ls < (2::int) ^ 31"
      by (metis numeral_One numeral_less_iff power_strict_increasing_iff semiring_norm(76))
    have "65536 = (2::nat) ^ 16"
      by eval
    from assms(4) have "?ls \<ge> 16"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      apply auto
      by (rule p_ge_16)
    from assms(3) have " (2::nat) ^ (?ls - (16::nat)) \<le> (255::nat)"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      by (subst power_diff[OF _ \<open>?ls \<ge> 16\<close>], auto)
    show ?thesis
      unfolding word_and_complement[OF \<open>of_int i \<noteq> _\<close>]
      apply (subst (2) word_sint_msb_eq)
      unfolding power_msb
      using \<open>the _ < 31\<close>
      apply simp
      apply (subst word_arith_power_alt)
      apply (subst word_ubin.eq_norm)
      unfolding bintrunc_mod2p
      apply simp
      apply (subst mod_le_simp)
      apply simp
      using \<open>2 ^ ?ls < _\<close>
      apply simp
      apply simp
      unfolding shiftr_div_2n'
      apply simp
      unfolding \<open>65536 = _\<close>
      thm power_diff
      apply (subst power_diff[symmetric])
      using \<open>?ls \<ge> 16\<close> apply auto
      unfolding table_2_power[OF \<open>_ \<le> 255\<close>]
      apply(auto simp:sint_word_ariths)
      unfolding word_of_nat
      unfolding word_sbin.eq_norm
      using \<open>?ls \<ge> 16\<close> \<open>?ls < 31\<close>
      apply (auto simp:sbintrunc_mod2p) 
      using ls_bit_signed by metis
  qed

lemma ls_bit_correct_24:
  assumes "(0::int) < i" "i \<le> (2147483647::int)"
          "(16777215::nat) < nat (sint ((of_int i::32 sword) && - of_int i))"
  shows "sint (table.[unat ((of_int (sint ((of_int i::32 sword) && - of_int i))::32 word) >> (24::nat))]) + (24::int)
         = int (the (ls_bit (of_int i::32 word)))"
proof -
let ?ls = "the (ls_bit ((of_int i)::32 sword))"
    from assms(1-2) have "of_int i \<noteq> (0::32 sword)"
      by (auto simp:word_of_int word_is_not_zeroI)
    from assms(1-2) have "?ls < 31"
      by (auto intro: ls_bit_less_power)
    hence "?ls < LENGTH (32 signed)"
      by simp
    from \<open>?ls < 31\<close> have "2 ^ ?ls < (2::int) ^ 31"
      by (metis numeral_One numeral_less_iff power_strict_increasing_iff semiring_norm(76))
    have "16777216 = (2::nat) ^ 24"
      by eval
    from assms(3) have "?ls \<ge> 24"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      apply auto
      by (rule p_ge_24)
    have "sint ((of_int i::32 sword) && - of_int i) \<ge> 0"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      by auto
    hence "nat (sint ((of_int i::32 sword) && - of_int i)) \<le> 2 ^ 31 - 1"  (* an implicit assumption *)
      using INT_MIN_MAX_lemmas(10)[of "(of_int i::32 sword) && - of_int i"]
      unfolding INT_MAX_def
      by auto
    hence " (2::nat) ^ (?ls - (24::nat)) \<le> (255::nat)"
      unfolding word_and_complement[OF \<open>_ \<noteq> 0\<close>]
      unfolding word_sint_msb_eq power_msb
      using \<open>?ls < 31\<close>
      apply auto
      unfolding unat_def[symmetric]
      by (subst power_diff[OF _ \<open>?ls \<ge> 24\<close>], auto)
      show ?thesis
      unfolding word_and_complement[OF \<open>of_int i \<noteq> _\<close>]
      apply (subst (2) word_sint_msb_eq)
      unfolding power_msb
      using \<open>the _ < 31\<close>
      apply simp
      apply (subst word_arith_power_alt)
      apply (subst word_ubin.eq_norm)
      unfolding bintrunc_mod2p
      apply simp
      apply (subst mod_le_simp)
      apply simp
      using \<open>2 ^ ?ls < _\<close>
      apply simp
      apply simp
      unfolding shiftr_div_2n'
      apply simp
      unfolding \<open>16777216 = _\<close>
      apply (subst power_diff[symmetric])
      using \<open>?ls \<ge> 24\<close> apply auto
      unfolding table_2_power[OF \<open>_ \<le> 255\<close>]
      apply(auto simp:sint_word_ariths)
      unfolding word_of_nat
      unfolding word_sbin.eq_norm
      using \<open>?ls \<ge> 24\<close> \<open>?ls < 31\<close>
      apply (auto simp:sbintrunc_mod2p)
      using ls_bit_signed by metis
  qed
end
theory Fp_Round_Value
  imports Fp_Rational_Scale
begin

section \<open>Signed rational values on the scaled grid\<close>

definition signed_rat :: "bool \<Rightarrow> rat \<Rightarrow> rat" where
  "signed_rat negative x = (if negative then - x else x)"

definition scaled_exact_value ::
  "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> rat" where
  "scaled_exact_value negative n d k =
    signed_rat negative ((of_nat n / of_nat d) * rat_pow2 k)"

definition scaled_rounded_value ::
  "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> rat" where
  "scaled_rounded_value rm negative n d k =
    signed_rat negative (of_nat (scaled_round_integer rm negative n d k))"

definition exact_input_value :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
  "exact_input_value negative n d = signed_rat negative (of_nat n / of_nat d)"

definition rounded_grid_value ::
  "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> rat" where
  "rounded_grid_value rm negative n d k =
    signed_rat negative
      (of_nat (scaled_round_integer rm negative n d k) * rat_pow2 (- k))"

definition grid_point_value :: "bool \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> rat" where
  "grid_point_value negative k m =
    signed_rat negative (of_nat m * rat_pow2 (- k))"

lemma signed_rat_simps [simp]:
  "signed_rat False x = x"
  "signed_rat True x = - x"
  by (simp_all add: signed_rat_def)

lemma abs_signed_rat [simp]:
  "\<bar>signed_rat negative x\<bar> = \<bar>x\<bar>"
  by (cases negative) simp_all

lemma abs_signed_rat_diff [simp]:
  "\<bar>signed_rat negative x - signed_rat negative y\<bar> = \<bar>x - y\<bar>"
  by (cases negative) (simp_all add: abs_minus_commute)

lemma signed_rat_mult_right:
  "signed_rat negative (x * c) = signed_rat negative x * c"
  by (cases negative) simp_all

lemma rat_pow2_neg_cancel [simp]:
  "rat_pow2 k * rat_pow2 (- k) = 1"
proof -
  have "rat_pow2 k * rat_pow2 (- k) = rat_pow2 (k + (- k))"
    by (simp only: rat_pow2_add[symmetric])
  also have "... = 1" by (simp add: rat_pow2_def)
  finally show ?thesis .
qed

lemma rat_pow2_neg_cancel_left [simp]:
  "rat_pow2 (- k) * rat_pow2 k = 1"
  using rat_pow2_neg_cancel[of "- k"] by simp

lemma scaled_exact_value_unscale:
  "scaled_exact_value negative n d k * rat_pow2 (- k) =
    exact_input_value negative n d"
  by (cases negative)
    (simp_all add: scaled_exact_value_def exact_input_value_def
      signed_rat_mult_right algebra_simps)

lemma scaled_rounded_value_unscale:
  "scaled_rounded_value rm negative n d k * rat_pow2 (- k) =
    rounded_grid_value rm negative n d k"
  by (simp add: scaled_rounded_value_def rounded_grid_value_def
      signed_rat_mult_right)

lemma signed_grid_point_unscale:
  "signed_rat negative (of_nat z) * rat_pow2 (- k) =
    grid_point_value negative k z"
  by (simp add: grid_point_value_def signed_rat_mult_right)

lemma abs_diff_mult_nonnegative:
  fixes a b c :: rat
  assumes "0 \<le> c"
  shows "\<bar>a - b\<bar> * c = \<bar>a * c - b * c\<bar>"
proof -
  have distribute: "(a - b) * c = a * c - b * c"
    by (rule left_diff_distrib)
  have "\<bar>a - b\<bar> * c = \<bar>a - b\<bar> * \<bar>c\<bar>"
    using assms by simp
  also have "... = \<bar>(a - b) * c\<bar>"
    by (simp only: abs_mult)
  also have "... = \<bar>a * c - b * c\<bar>"
    using distribute by simp
  finally show ?thesis .
qed

lemma scaled_exact_value_as_ratio:
  assumes "0 < d"
  shows
    "scaled_exact_value negative n d k =
      signed_rat negative
        ((of_nat (scaled_numerator n d k) :: rat) /
          of_nat (scaled_denominator n d k))"
  unfolding scaled_exact_value_def
  using scale_ratio_exact[OF assms, of n k] by simp

lemma rounded_grid_value_is_grid_point [simp]:
  "rounded_grid_value rm negative n d k =
    grid_point_value negative k (scaled_round_integer rm negative n d k)"
  by (simp add: rounded_grid_value_def grid_point_value_def)

section \<open>Rational interpretation of quotient/remainder error\<close>

lemma scaled_error_divide_eq_abs:
  assumes qpos: "0 < q"
  shows
    "(of_nat (scaled_error p q m) :: rat) / of_nat q =
      \<bar>(of_nat m :: rat) - of_nat p / of_nat q\<bar>"
proof (cases "m * q \<le> p")
  case True
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have order:
    "(of_nat m :: rat) \<le> of_nat p / of_nat q"
  proof -
    have cross:
      "(of_nat m :: rat) * of_nat q \<le> of_nat p"
      using True by (simp only: of_nat_mult[symmetric] of_nat_le_iff)
    from cross show ?thesis
      by (simp only: pos_le_divide_eq[OF qrat])
  qed
  have nonpos:
    "(of_nat m :: rat) - of_nat p / of_nat q \<le> 0"
    using order by linarith
  have algebra:
    "(of_nat (p - m * q) :: rat) / of_nat q =
      of_nat p / of_nat q - of_nat m"
    using True qrat
    by (simp add: of_nat_diff diff_divide_distrib)
  show ?thesis
    using True nonpos algebra
    by (simp add: scaled_error_def abs_of_nonpos)
next
  case False
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have pm_le: "p \<le> m * q" using False by simp
  have order:
    "of_nat p / of_nat q < (of_nat m :: rat)"
  proof -
    have cross:
      "(of_nat p :: rat) < of_nat m * of_nat q"
      using False by (simp only: not_le of_nat_mult[symmetric] of_nat_less_iff)
    from cross show ?thesis
      by (simp only: pos_divide_less_eq[OF qrat])
  qed
  have nonneg:
    "0 \<le> (of_nat m :: rat) - of_nat p / of_nat q"
    using order by linarith
  have algebra:
    "(of_nat (m * q - p) :: rat) / of_nat q =
      of_nat m - of_nat p / of_nat q"
    using pm_le qrat
    by (simp add: of_nat_diff diff_divide_distrib)
  show ?thesis
    using False nonneg algebra
    by (simp add: scaled_error_def abs_of_nonneg)
qed

lemma round_integer_rat_unit_interval:
  assumes qpos: "0 < q"
  shows
    "(of_nat (round_integer rm negative p q) :: rat) <
       of_nat p / of_nat q + 1"
    "of_nat p / of_nat q <
       (of_nat (round_integer rm negative p q) :: rat) + 1"
proof -
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have first_nat:
    "round_integer rm negative p q * q < p + q"
    by (rule round_integer_unit_interval(1)[OF qpos])
  have first_cross:
    "(of_nat (round_integer rm negative p q) :: rat) * of_nat q <
      of_nat p + of_nat q"
    using first_nat
    by (simp only: of_nat_mult[symmetric] of_nat_add[symmetric] of_nat_less_iff)
  have first_fraction:
    "(of_nat (round_integer rm negative p q) :: rat) <
      (of_nat p + of_nat q) / of_nat q"
    using first_cross by (simp only: pos_less_divide_eq[OF qrat])
  have fraction:
    "((of_nat p + of_nat q) / of_nat q :: rat) =
      of_nat p / of_nat q + 1"
    using qrat by (simp add: add_divide_distrib)
  from first_fraction fraction show
    "(of_nat (round_integer rm negative p q) :: rat) <
      of_nat p / of_nat q + 1"
    by simp

  have second_nat:
    "p < (round_integer rm negative p q + 1) * q"
    by (rule round_integer_unit_interval(2)[OF qpos])
  have second_cast:
    "(of_nat p :: rat) <
      of_nat ((round_integer rm negative p q + 1) * q)"
    by (rule of_nat_less_iff[THEN iffD2], rule second_nat)
  have second_cross:
    "(of_nat p :: rat) <
      (of_nat (round_integer rm negative p q) + 1) * of_nat q"
    using second_cast by (simp add: algebra_simps)
  from second_cross show
    "of_nat p / of_nat q <
      (of_nat (round_integer rm negative p q) :: rat) + 1"
    by (simp only: pos_divide_less_eq[OF qrat])
qed

lemma round_integer_rat_error_less_one:
  assumes "0 < q"
  shows
    "\<bar>(of_nat (round_integer rm negative p q) :: rat) -
       of_nat p / of_nat q\<bar> < 1"
proof -
  have below:
    "(of_nat (round_integer rm negative p q) :: rat) <
      of_nat p / of_nat q + 1"
    by (rule round_integer_rat_unit_interval(1)[OF assms])
  have above:
    "of_nat p / of_nat q <
      (of_nat (round_integer rm negative p q) :: rat) + 1"
    by (rule round_integer_rat_unit_interval(2)[OF assms])
  show ?thesis using below above by (simp add: abs_less_iff; linarith)
qed

section \<open>Mode-independent bracketing\<close>

lemma scaled_round_value_unit_interval:
  assumes "0 < d"
  shows
    "(of_nat (scaled_round_integer rm negative n d k) :: rat) <
       (of_nat n / of_nat d) * rat_pow2 k + 1"
    "(of_nat n / of_nat d) * rat_pow2 k <
       (of_nat (scaled_round_integer rm negative n d k) :: rat) + 1"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have below:
    "(of_nat (round_integer rm negative ?p ?q) :: rat) <
      of_nat ?p / of_nat ?q + 1"
    by (rule round_integer_rat_unit_interval(1)[OF qpos])
  have above:
    "of_nat ?p / of_nat ?q <
      (of_nat (round_integer rm negative ?p ?q) :: rat) + 1"
    by (rule round_integer_rat_unit_interval(2)[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show
    "(of_nat (scaled_round_integer rm negative n d k) :: rat) <
      (of_nat n / of_nat d) * rat_pow2 k + 1"
    using below exact by (simp add: scaled_round_integer_def)
  show
    "(of_nat n / of_nat d) * rat_pow2 k <
      (of_nat (scaled_round_integer rm negative n d k) :: rat) + 1"
    using above exact by (simp add: scaled_round_integer_def)
qed

lemma scaled_round_value_error_less_one:
  assumes "0 < d"
  shows
    "\<bar>scaled_rounded_value rm negative n d k -
       scaled_exact_value negative n d k\<bar> < 1"
proof -
  have below:
    "(of_nat (scaled_round_integer rm negative n d k) :: rat) <
      (of_nat n / of_nat d) * rat_pow2 k + 1"
    by (rule scaled_round_value_unit_interval(1)[OF assms])
  have above:
    "(of_nat n / of_nat d) * rat_pow2 k <
      (of_nat (scaled_round_integer rm negative n d k) :: rat) + 1"
    by (rule scaled_round_value_unit_interval(2)[OF assms])
  show ?thesis
    using below above
    by (simp add: scaled_rounded_value_def scaled_exact_value_def abs_less_iff;
        linarith)
qed

section \<open>Directed modes\<close>

lemma signed_ratio_le_integer_iff:
  assumes qpos: "0 < q"
  shows
    "signed_rat negative (of_nat p / of_nat q) \<le>
       signed_rat negative (of_nat m) \<longleftrightarrow>
     signed_mag negative p \<le> signed_mag negative (m * q)"
proof (cases negative)
  case False
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  with False show ?thesis
    by (simp add: pos_divide_le_eq;
        simp only: of_nat_mult[symmetric] of_nat_le_iff)
next
  case True
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  with True show ?thesis
    by (simp add: pos_le_divide_eq;
        simp only: of_nat_mult[symmetric] of_nat_le_iff)
qed

lemma signed_integer_le_ratio_iff:
  assumes qpos: "0 < q"
  shows
    "signed_rat negative (of_nat m) \<le>
       signed_rat negative (of_nat p / of_nat q) \<longleftrightarrow>
     signed_mag negative (m * q) \<le> signed_mag negative p"
proof (cases negative)
  case False
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  with False show ?thesis
    by (simp add: pos_le_divide_eq;
        simp only: of_nat_mult[symmetric] of_nat_le_iff)
next
  case True
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  with True show ?thesis
    by (simp add: pos_divide_le_eq;
        simp only: of_nat_mult[symmetric] of_nat_le_iff)
qed

lemma round_integer_RTP_rat:
  assumes qpos: "0 < q"
  shows
    "signed_rat negative (of_nat p / of_nat q) \<le>
      signed_rat negative (of_nat (round_integer RTP negative p q))"
proof -
  have core:
    "signed_mag negative p \<le>
      signed_mag negative (round_integer RTP negative p q * q)"
    by (rule RTP_directed[OF qpos])
  have bridge:
    "signed_rat negative (of_nat p / of_nat q) \<le>
       signed_rat negative (of_nat (round_integer RTP negative p q)) \<longleftrightarrow>
     signed_mag negative p \<le>
       signed_mag negative (round_integer RTP negative p q * q)"
    by (rule signed_ratio_le_integer_iff[OF qpos])
  from core bridge show ?thesis by blast
qed

lemma round_integer_RTN_rat:
  assumes qpos: "0 < q"
  shows
    "signed_rat negative (of_nat (round_integer RTN negative p q)) \<le>
      signed_rat negative (of_nat p / of_nat q)"
proof -
  have core:
    "signed_mag negative (round_integer RTN negative p q * q) \<le>
      signed_mag negative p"
    by (rule RTN_directed[OF qpos])
  have bridge:
    "signed_rat negative (of_nat (round_integer RTN negative p q)) \<le>
       signed_rat negative (of_nat p / of_nat q) \<longleftrightarrow>
     signed_mag negative (round_integer RTN negative p q * q) \<le>
       signed_mag negative p"
    by (rule signed_integer_le_ratio_iff[OF qpos])
  from core bridge show ?thesis by blast
qed

lemma round_integer_RTZ_rat:
  assumes qpos: "0 < q"
  shows
    "if negative
     then signed_rat negative (of_nat p / of_nat q) \<le>
       signed_rat negative (of_nat (round_integer RTZ negative p q))
     else signed_rat negative (of_nat (round_integer RTZ negative p q)) \<le>
       signed_rat negative (of_nat p / of_nat q)"
proof (cases negative)
  case True
  have core:
    "signed_mag True p \<le>
      signed_mag True (round_integer RTZ True p q * q)"
    using RTZ_directed[of True p q] by simp
  have bridge:
    "signed_rat True (of_nat p / of_nat q) \<le>
       signed_rat True (of_nat (round_integer RTZ True p q)) \<longleftrightarrow>
     signed_mag True p \<le>
       signed_mag True (round_integer RTZ True p q * q)"
    by (rule signed_ratio_le_integer_iff[OF qpos])
  with True core show ?thesis by simp
next
  case False
  have core:
    "signed_mag False (round_integer RTZ False p q * q) \<le>
      signed_mag False p"
    using RTZ_directed[of False p q] by simp
  have bridge:
    "signed_rat False (of_nat (round_integer RTZ False p q)) \<le>
       signed_rat False (of_nat p / of_nat q) \<longleftrightarrow>
     signed_mag False (round_integer RTZ False p q * q) \<le>
       signed_mag False p"
    by (rule signed_integer_le_ratio_iff[OF qpos])
  with False core show ?thesis by simp
qed

lemma scaled_RTP_value_directed:
  assumes "0 < d"
  shows
    "scaled_exact_value negative n d k \<le>
      scaled_rounded_value RTP negative n d k"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "signed_rat negative ((of_nat ?p :: rat) / of_nat ?q) \<le>
      signed_rat negative (of_nat (round_integer RTP negative ?p ?q))"
    by (rule round_integer_RTP_rat[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma scaled_RTN_value_directed:
  assumes "0 < d"
  shows
    "scaled_rounded_value RTN negative n d k \<le>
      scaled_exact_value negative n d k"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "signed_rat negative (of_nat (round_integer RTN negative ?p ?q)) \<le>
      signed_rat negative ((of_nat ?p :: rat) / of_nat ?q)"
    by (rule round_integer_RTN_rat[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma scaled_RTZ_value_directed:
  assumes "0 < d"
  shows
    "if negative
     then scaled_exact_value negative n d k \<le>
       scaled_rounded_value RTZ negative n d k
     else scaled_rounded_value RTZ negative n d k \<le>
       scaled_exact_value negative n d k"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "if negative
     then signed_rat negative ((of_nat ?p :: rat) / of_nat ?q) \<le>
       signed_rat negative (of_nat (round_integer RTZ negative ?p ?q))
     else signed_rat negative (of_nat (round_integer RTZ negative ?p ?q)) \<le>
       signed_rat negative ((of_nat ?p :: rat) / of_nat ?q)"
    by (rule round_integer_RTZ_rat[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp only: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma grid_RTP_value_directed:
  assumes "0 < d"
  shows
    "exact_input_value negative n d \<le>
      rounded_grid_value RTP negative n d k"
proof -
  have scaled:
    "scaled_exact_value negative n d k \<le>
      scaled_rounded_value RTP negative n d k"
    by (rule scaled_RTP_value_directed[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have
    "scaled_exact_value negative n d k * rat_pow2 (- k) \<le>
      scaled_rounded_value RTP negative n d k * rat_pow2 (- k)"
    by (rule mult_right_mono[OF scaled nonneg])
  then show ?thesis
    by (simp only: scaled_exact_value_unscale scaled_rounded_value_unscale)
qed

lemma grid_RTN_value_directed:
  assumes "0 < d"
  shows
    "rounded_grid_value RTN negative n d k \<le>
      exact_input_value negative n d"
proof -
  have scaled:
    "scaled_rounded_value RTN negative n d k \<le>
      scaled_exact_value negative n d k"
    by (rule scaled_RTN_value_directed[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have
    "scaled_rounded_value RTN negative n d k * rat_pow2 (- k) \<le>
      scaled_exact_value negative n d k * rat_pow2 (- k)"
    by (rule mult_right_mono[OF scaled nonneg])
  then show ?thesis
    by (simp only: scaled_exact_value_unscale scaled_rounded_value_unscale)
qed

lemma grid_RTZ_value_directed:
  assumes "0 < d"
  shows
    "if negative
     then exact_input_value negative n d \<le>
       rounded_grid_value RTZ negative n d k
     else rounded_grid_value RTZ negative n d k \<le>
       exact_input_value negative n d"
proof (cases negative)
  case True
  have scaled:
    "scaled_exact_value True n d k \<le>
      scaled_rounded_value RTZ True n d k"
    using scaled_RTZ_value_directed[OF assms, of True n k] by simp
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have
    "scaled_exact_value True n d k * rat_pow2 (- k) \<le>
      scaled_rounded_value RTZ True n d k * rat_pow2 (- k)"
    by (rule mult_right_mono[OF scaled nonneg])
  with True show ?thesis
    by (simp only: if_True scaled_exact_value_unscale
        scaled_rounded_value_unscale)
next
  case False
  have scaled:
    "scaled_rounded_value RTZ False n d k \<le>
      scaled_exact_value False n d k"
    using scaled_RTZ_value_directed[OF assms, of False n k] by simp
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have
    "scaled_rounded_value RTZ False n d k * rat_pow2 (- k) \<le>
      scaled_exact_value False n d k * rat_pow2 (- k)"
    by (rule mult_right_mono[OF scaled nonneg])
  with False show ?thesis
    by (simp only: if_False scaled_exact_value_unscale
        scaled_rounded_value_unscale)
qed

section \<open>Nearest modes and global grid optimality\<close>

lemma round_integer_RNE_rat_error_half:
  assumes qpos: "0 < q"
  shows
    "\<bar>(of_nat (round_integer RNE negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le> 1 / 2"
proof -
  let ?e = "scaled_error p q (round_integer RNE negative p q)"
  have half_nat: "2 * ?e \<le> q"
    by (rule RNE_scaled_error_half[OF qpos])
  have half_rat: "2 * (of_nat ?e :: rat) \<le> of_nat q"
    using half_nat by simp
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have divided: "(of_nat ?e :: rat) / of_nat q \<le> 1 / 2"
    using half_rat qrat
    by (simp add: pos_divide_le_eq; linarith)
  have error:
    "(of_nat ?e :: rat) / of_nat q =
      \<bar>(of_nat (round_integer RNE negative p q) :: rat) -
        of_nat p / of_nat q\<bar>"
    by (rule scaled_error_divide_eq_abs[OF qpos])
  from divided error show ?thesis by simp
qed

lemma round_integer_RNA_rat_error_half:
  assumes qpos: "0 < q"
  shows
    "\<bar>(of_nat (round_integer RNA negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le> 1 / 2"
proof -
  let ?e = "scaled_error p q (round_integer RNA negative p q)"
  have half_nat: "2 * ?e \<le> q"
    by (rule RNA_scaled_error_half[OF qpos])
  have half_rat: "2 * (of_nat ?e :: rat) \<le> of_nat q"
    using half_nat by simp
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have divided: "(of_nat ?e :: rat) / of_nat q \<le> 1 / 2"
    using half_rat qrat
    by (simp add: pos_divide_le_eq; linarith)
  have error:
    "(of_nat ?e :: rat) / of_nat q =
      \<bar>(of_nat (round_integer RNA negative p q) :: rat) -
        of_nat p / of_nat q\<bar>"
    by (rule scaled_error_divide_eq_abs[OF qpos])
  from divided error show ?thesis by simp
qed

lemma half_error_integer_is_nearest:
  fixes x :: rat
  assumes half: "\<bar>(of_nat m :: rat) - x\<bar> \<le> 1 / 2"
  shows
    "\<bar>(of_nat m :: rat) - x\<bar> \<le>
      \<bar>(of_nat z :: rat) - x\<bar>"
proof (cases "z = m")
  case True
  then show ?thesis by simp
next
  case False
  have gap:
    "1 \<le> \<bar>(of_nat z :: rat) - of_nat m\<bar>"
  proof (cases "z < m")
    case True
    have step: "(of_nat z :: rat) + 1 \<le> of_nat m"
      using True by simp
    have nonpos: "(of_nat z :: rat) - of_nat m \<le> 0"
      using step by linarith
    show ?thesis
      using step by (simp add: abs_of_nonpos nonpos; linarith)
  next
    case not_less: False
    have mz: "m < z" using not_less False by auto
    have step: "(of_nat m :: rat) + 1 \<le> of_nat z"
      using mz by simp
    have nonneg: "0 \<le> (of_nat z :: rat) - of_nat m"
      using step by linarith
    show ?thesis
      using step by (simp add: abs_of_nonneg nonneg; linarith)
  qed
  have triangle:
    "\<bar>(of_nat z :: rat) - of_nat m\<bar> \<le>
      \<bar>(of_nat z :: rat) - x\<bar> + \<bar>(of_nat m :: rat) - x\<bar>"
  proof -
    have split:
      "(of_nat z :: rat) - of_nat m =
        ((of_nat z :: rat) - x) + (x - of_nat m)"
      by linarith
    have
      "\<bar>(of_nat z :: rat) - of_nat m\<bar> =
        \<bar>((of_nat z :: rat) - x) + (x - of_nat m)\<bar>"
      using split by simp
    also have "... \<le>
        \<bar>(of_nat z :: rat) - x\<bar> + \<bar>x - of_nat m\<bar>"
      by (rule abs_triangle_ineq)
    also have "... =
        \<bar>(of_nat z :: rat) - x\<bar> + \<bar>(of_nat m :: rat) - x\<bar>"
      by (simp add: abs_minus_commute)
    finally show ?thesis .
  qed
  from gap triangle half show ?thesis by linarith
qed

lemma round_integer_RNE_nearest:
  assumes "0 < q"
  shows
    "\<bar>(of_nat (round_integer RNE negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le>
     \<bar>(of_nat z :: rat) - of_nat p / of_nat q\<bar>"
proof (rule half_error_integer_is_nearest)
  show
    "\<bar>(of_nat (round_integer RNE negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le> 1 / 2"
    by (rule round_integer_RNE_rat_error_half[OF assms])
qed

lemma round_integer_RNA_nearest:
  assumes "0 < q"
  shows
    "\<bar>(of_nat (round_integer RNA negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le>
     \<bar>(of_nat z :: rat) - of_nat p / of_nat q\<bar>"
proof (rule half_error_integer_is_nearest)
  show
    "\<bar>(of_nat (round_integer RNA negative p q) :: rat) -
       of_nat p / of_nat q\<bar> \<le> 1 / 2"
    by (rule round_integer_RNA_rat_error_half[OF assms])
qed

lemma scaled_RNE_value_error_half:
  assumes "0 < d"
  shows
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> \<le> 1 / 2"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "\<bar>(of_nat (round_integer RNE negative ?p ?q) :: rat) -
       of_nat ?p / of_nat ?q\<bar> \<le> 1 / 2"
    by (rule round_integer_RNE_rat_error_half[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma scaled_RNA_value_error_half:
  assumes "0 < d"
  shows
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> \<le> 1 / 2"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "\<bar>(of_nat (round_integer RNA negative ?p ?q) :: rat) -
       of_nat ?p / of_nat ?q\<bar> \<le> 1 / 2"
    by (rule round_integer_RNA_rat_error_half[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma scaled_RNE_nearest_grid_point:
  assumes "0 < d"
  shows
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar>"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "\<bar>(of_nat (round_integer RNE negative ?p ?q) :: rat) -
       of_nat ?p / of_nat ?q\<bar> \<le>
     \<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar>"
    by (rule round_integer_RNE_nearest[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma scaled_RNA_nearest_grid_point:
  assumes "0 < d"
  shows
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar>"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF assms])
  have core:
    "\<bar>(of_nat (round_integer RNA negative ?p ?q) :: rat) -
       of_nat ?p / of_nat ?q\<bar> \<le>
     \<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar>"
    by (rule round_integer_RNA_nearest[OF qpos])
  have exact:
    "(of_nat ?p :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF assms])
  show ?thesis
    using core exact
    by (simp add: scaled_exact_value_def scaled_rounded_value_def
        scaled_round_integer_def)
qed

lemma rounded_grid_error_unscale:
  "\<bar>scaled_rounded_value rm negative n d k -
      scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) =
    \<bar>rounded_grid_value rm negative n d k -
      exact_input_value negative n d\<bar>"
proof -
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have scaled:
    "\<bar>scaled_rounded_value rm negative n d k -
        scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) =
      \<bar>scaled_rounded_value rm negative n d k * rat_pow2 (- k) -
        scaled_exact_value negative n d k * rat_pow2 (- k)\<bar>"
    by (rule abs_diff_mult_nonnegative[OF nonneg])
  from scaled show ?thesis
    by (simp only: scaled_rounded_value_unscale scaled_exact_value_unscale)
qed

lemma grid_point_error_unscale:
  "\<bar>signed_rat negative (of_nat z) -
      scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) =
    \<bar>grid_point_value negative k z - exact_input_value negative n d\<bar>"
proof -
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have scaled:
    "\<bar>signed_rat negative (of_nat z) -
        scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) =
      \<bar>signed_rat negative (of_nat z) * rat_pow2 (- k) -
        scaled_exact_value negative n d k * rat_pow2 (- k)\<bar>"
    by (rule abs_diff_mult_nonnegative[OF nonneg])
  from scaled show ?thesis
    by (simp only: signed_grid_point_unscale scaled_exact_value_unscale)
qed

lemma grid_RNE_value_error_half_ulp:
  assumes "0 < d"
  shows
    "\<bar>rounded_grid_value RNE negative n d k -
       exact_input_value negative n d\<bar> \<le> rat_pow2 (- k) / 2"
proof -
  have half:
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> \<le> 1 / 2"
    by (rule scaled_RNE_value_error_half[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have multiplied:
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) \<le>
      (1 / 2) * rat_pow2 (- k)"
    by (rule mult_right_mono[OF half nonneg])
  have half_step:
    "((1 / 2) :: rat) * rat_pow2 (- k) = rat_pow2 (- k) / 2"
    by simp
  show ?thesis
    using multiplied half_step
    by (simp only: rounded_grid_error_unscale)
qed

lemma grid_RNA_value_error_half_ulp:
  assumes "0 < d"
  shows
    "\<bar>rounded_grid_value RNA negative n d k -
       exact_input_value negative n d\<bar> \<le> rat_pow2 (- k) / 2"
proof -
  have half:
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> \<le> 1 / 2"
    by (rule scaled_RNA_value_error_half[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have multiplied:
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) \<le>
      (1 / 2) * rat_pow2 (- k)"
    by (rule mult_right_mono[OF half nonneg])
  have half_step:
    "((1 / 2) :: rat) * rat_pow2 (- k) = rat_pow2 (- k) / 2"
    by simp
  show ?thesis
    using multiplied half_step
    by (simp only: rounded_grid_error_unscale)
qed

lemma grid_RNE_nearest_grid_point:
  assumes "0 < d"
  shows
    "\<bar>rounded_grid_value RNE negative n d k -
       exact_input_value negative n d\<bar> \<le>
     \<bar>grid_point_value negative k z - exact_input_value negative n d\<bar>"
proof -
  have nearest:
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar>"
    by (rule scaled_RNE_nearest_grid_point[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have multiplied:
    "\<bar>scaled_rounded_value RNE negative n d k -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k)"
    by (rule mult_right_mono[OF nearest nonneg])
  from multiplied show ?thesis
    by (simp only: rounded_grid_error_unscale grid_point_error_unscale)
qed

lemma grid_RNA_nearest_grid_point:
  assumes "0 < d"
  shows
    "\<bar>rounded_grid_value RNA negative n d k -
       exact_input_value negative n d\<bar> \<le>
     \<bar>grid_point_value negative k z - exact_input_value negative n d\<bar>"
proof -
  have nearest:
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar>"
    by (rule scaled_RNA_nearest_grid_point[OF assms])
  have nonneg: "0 \<le> rat_pow2 (- k)" by simp
  have multiplied:
    "\<bar>scaled_rounded_value RNA negative n d k -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k) \<le>
     \<bar>signed_rat negative (of_nat z) -
       scaled_exact_value negative n d k\<bar> * rat_pow2 (- k)"
    by (rule mult_right_mono[OF nearest nonneg])
  from multiplied show ?thesis
    by (simp only: rounded_grid_error_unscale grid_point_error_unscale)
qed

lemma scaled_RNE_tie_even:
  assumes denominator: "0 < d"
      and tie:
        "scaled_denominator n d k =
          2 * (scaled_numerator n d k mod scaled_denominator n d k)"
  shows "even (scaled_round_integer RNE negative n d k)"
  unfolding scaled_round_integer_def
  by (rule RNE_integer_at_half_is_even[OF
        scaled_denominator_pos[OF denominator] tie])

lemma scaled_RNA_tie_away:
  assumes denominator: "0 < d"
      and tie:
        "scaled_denominator n d k =
          2 * (scaled_numerator n d k mod scaled_denominator n d k)"
  shows
    "scaled_round_integer RNA negative n d k =
      scaled_numerator n d k div scaled_denominator n d k + 1"
  unfolding scaled_round_integer_def
  by (rule RNA_integer_at_half[OF
        scaled_denominator_pos[OF denominator] tie])

end

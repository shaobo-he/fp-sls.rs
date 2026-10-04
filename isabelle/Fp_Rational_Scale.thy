theory Fp_Rational_Scale
  imports Fp_Round_Int "HOL-Library.Float"
begin

section \<open>Exact power-of-two scaling\<close>

text \<open>
  This is the HOL counterpart of \<open>scale_ratio\<close> in
  \<open>src/data/fp.rs\<close>.  A non-negative shift multiplies the
  numerator; a negative shift multiplies the denominator.  No reduction of
  the resulting fraction is required by the rounding algorithm.
\<close>

definition rat_pow2 :: "int \<Rightarrow> rat" where
  "rat_pow2 k = (2 :: rat) powi k"

lemma rat_pow2_pos [simp]: "0 < rat_pow2 k"
  by (simp add: rat_pow2_def)

lemma rat_pow2_nonnegative [simp]: "0 \<le> rat_pow2 k"
  using rat_pow2_pos[of k] by linarith

lemma rat_pow2_add:
  "rat_pow2 (a + b) = rat_pow2 a * rat_pow2 b"
  unfolding rat_pow2_def by (rule power_int_add) simp

lemma rat_pow2_int_nat [simp]:
  "rat_pow2 (int p) = (of_nat (2 ^ p) :: rat)"
  by (simp add: rat_pow2_def power_int_def)

lemma rat_pow2_increasing:
  assumes "a \<le> b"
  shows "rat_pow2 a \<le> rat_pow2 b"
  unfolding rat_pow2_def
  by (rule power_int_increasing[OF assms]) simp

lemma rat_pow2_scale_cancel:
  "rat_pow2 e * rat_pow2 (int p - e) = (of_nat (2 ^ p) :: rat)"
proof -
  have "rat_pow2 e * rat_pow2 (int p - e) =
      rat_pow2 (e + (int p - e))"
    by (simp only: rat_pow2_add[symmetric])
  also have "... = rat_pow2 (int p)" by simp
  also have "... = (of_nat (2 ^ p) :: rat)" by simp
  finally show ?thesis .
qed

lemma rat_pow2_succ_scale_cancel:
  "rat_pow2 (e + 1) * rat_pow2 (int p - e) =
    (of_nat (2 ^ Suc p) :: rat)"
proof -
  have "rat_pow2 (e + 1) * rat_pow2 (int p - e) =
      rat_pow2 ((e + 1) + (int p - e))"
    by (simp only: rat_pow2_add[symmetric])
  also have "... = rat_pow2 (int (Suc p))" by (simp add: add.commute)
  also have "... = (of_nat (2 ^ Suc p) :: rat)"
    by (rule rat_pow2_int_nat)
  finally show ?thesis .
qed

lemma of_rat_rat_pow2_real [simp]:
  "(of_rat (rat_pow2 k) :: real) =
    (2::real) powr (of_int k)"
  by (cases "0 \<le> k")
    (simp_all add: rat_pow2_def power_int_def of_rat_power of_rat_inverse
        of_rat_divide powr_int power_divide)

definition scale_ratio :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<times> nat" where
  "scale_ratio n d k =
    (if 0 \<le> k
     then (n * 2 ^ nat k, d)
     else (n, d * 2 ^ nat (- k)))"

definition scaled_numerator :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "scaled_numerator n d k = fst (scale_ratio n d k)"

definition scaled_denominator :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "scaled_denominator n d k = snd (scale_ratio n d k)"

definition scaled_round_integer ::
  "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "scaled_round_integer rm negative n d k =
    round_integer rm negative
      (scaled_numerator n d k) (scaled_denominator n d k)"

lemma scale_ratio_nonnegative:
  assumes "0 \<le> k"
  shows "scale_ratio n d k = (n * 2 ^ nat k, d)"
  using assms by (simp add: scale_ratio_def)

lemma scale_ratio_negative:
  assumes "k < 0"
  shows "scale_ratio n d k = (n, d * 2 ^ nat (- k))"
  using assms by (simp add: scale_ratio_def)

lemma scaled_numerator_nonnegative:
  assumes "0 \<le> k"
  shows "scaled_numerator n d k = n * 2 ^ nat k"
  using assms by (simp add: scaled_numerator_def scale_ratio_nonnegative)

lemma scaled_denominator_nonnegative:
  assumes "0 \<le> k"
  shows "scaled_denominator n d k = d"
  using assms by (simp add: scaled_denominator_def scale_ratio_nonnegative)

lemma scaled_numerator_negative:
  assumes "k < 0"
  shows "scaled_numerator n d k = n"
  using assms by (simp add: scaled_numerator_def scale_ratio_negative)

lemma scaled_denominator_negative:
  assumes "k < 0"
  shows "scaled_denominator n d k = d * 2 ^ nat (- k)"
  using assms by (simp add: scaled_denominator_def scale_ratio_negative)

lemma scaled_denominator_pos:
  assumes "0 < d"
  shows "0 < scaled_denominator n d k"
proof (cases "0 \<le> k")
  case True
  with assms show ?thesis by (simp add: scaled_denominator_nonnegative)
next
  case False
  then have "k < 0" by simp
  with assms show ?thesis by (simp add: scaled_denominator_negative)
qed

lemma scale_ratio_exact:
  assumes "0 < d"
  shows
    "(of_nat (scaled_numerator n d k) :: rat) /
       of_nat (scaled_denominator n d k) =
     (of_nat n / of_nat d) * rat_pow2 k"
proof (cases "0 \<le> k")
  case True
  with assms show ?thesis
    by (simp add: scaled_numerator_nonnegative scaled_denominator_nonnegative
        rat_pow2_def power_int_def field_simps)
next
  case False
  then have neg: "k < 0" by simp
  with assms show ?thesis
    by (simp add: scaled_numerator_negative scaled_denominator_negative
        rat_pow2_def power_int_def power_inverse field_simps)
qed

section \<open>Rounding the scaled ratio\<close>

lemma scaled_round_integer_unfold:
  "scaled_round_integer rm negative n d k =
   round_integer rm negative
     (scaled_numerator n d k) (scaled_denominator n d k)"
  by (simp add: scaled_round_integer_def)

lemma scaled_round_integer_exact:
  assumes
    "scaled_numerator n d k mod scaled_denominator n d k = 0"
  shows
    "scaled_round_integer rm negative n d k =
     scaled_numerator n d k div scaled_denominator n d k"
  using assms by (simp add: scaled_round_integer_def)

lemma scaled_round_integer_zero [simp]:
  "scaled_round_integer rm negative 0 d k = 0"
  by (cases "0 \<le> k")
    (simp_all add: scaled_round_integer_def scaled_numerator_nonnegative
      scaled_denominator_nonnegative scaled_numerator_negative
      scaled_denominator_negative)

lemma scaled_round_integer_cases:
  "scaled_round_integer rm negative n d k =
      scaled_numerator n d k div scaled_denominator n d k
   \<or> scaled_round_integer rm negative n d k =
      scaled_numerator n d k div scaled_denominator n d k + 1"
  unfolding scaled_round_integer_def by (rule round_integer_cases)

text \<open>
  The next bounds are independent of the rounding mode.  They are the sharp
  bounds needed by the encoding proof: rounding a value in the half-open
  interval \<open>[lower, upper)\<close> can reach \<open>upper\<close>, but cannot
  exceed it.  At a normal binade boundary that one endpoint is precisely the
  carry case; on the subnormal grid it is promotion to the smallest normal.
\<close>

lemma scaled_round_integer_bounds:
  "scaled_numerator n d k div scaled_denominator n d k
      \<le> scaled_round_integer rm negative n d k
   \<and> scaled_round_integer rm negative n d k
      \<le> scaled_numerator n d k div scaled_denominator n d k + 1"
  unfolding scaled_round_integer_def by (rule round_integer_bounds)

lemma scaled_round_integer_floor_le:
  "scaled_numerator n d k div scaled_denominator n d k
    \<le> scaled_round_integer rm negative n d k"
  using scaled_round_integer_bounds[of n d k rm negative] by blast

lemma scaled_round_integer_le_floor_plus_one:
  "scaled_round_integer rm negative n d k
    \<le> scaled_numerator n d k div scaled_denominator n d k + 1"
  using scaled_round_integer_bounds[of n d k rm negative] by blast

lemma scaled_round_integer_lower_bound:
  assumes denominator: "0 < d"
      and lower:
        "lower * scaled_denominator n d k \<le> scaled_numerator n d k"
  shows "lower \<le> scaled_round_integer rm negative n d k"
proof -
  have qpos: "0 < scaled_denominator n d k"
    by (rule scaled_denominator_pos[OF denominator])
  have quotient:
    "lower \<le> scaled_numerator n d k div scaled_denominator n d k"
    using lower qpos by (simp add: less_eq_div_iff_mult_less_eq)
  from quotient scaled_round_integer_floor_le show ?thesis
    by (rule order_trans)
qed

lemma scaled_round_integer_upper_bound:
  assumes denominator: "0 < d"
      and upper:
        "scaled_numerator n d k < upper * scaled_denominator n d k"
  shows "scaled_round_integer rm negative n d k \<le> upper"
proof -
  have qpos: "0 < scaled_denominator n d k"
    by (rule scaled_denominator_pos[OF denominator])
  have quotient:
    "scaled_numerator n d k div scaled_denominator n d k < upper"
    using upper qpos by (simp add: div_less_iff_less_mult)
  have rounded:
    "scaled_round_integer rm negative n d k
      \<le> scaled_numerator n d k div scaled_denominator n d k + 1"
    by (rule scaled_round_integer_le_floor_plus_one)
  from rounded quotient show ?thesis by linarith
qed

lemma scaled_round_integer_between:
  assumes denominator: "0 < d"
      and lower:
        "lower * scaled_denominator n d k \<le> scaled_numerator n d k"
      and upper:
        "scaled_numerator n d k < upper * scaled_denominator n d k"
  shows
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k \<le> upper"
  using scaled_round_integer_lower_bound[OF denominator lower]
    scaled_round_integer_upper_bound[OF denominator upper]
  by blast

lemma scaled_round_integer_between_strict:
  assumes denominator: "0 < d"
      and lower:
        "lower * scaled_denominator n d k \<le> scaled_numerator n d k"
      and upper:
        "scaled_numerator n d k < upper * scaled_denominator n d k"
      and no_upper: "scaled_round_integer rm negative n d k \<noteq> upper"
  shows
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k < upper"
proof -
  have bounds:
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k \<le> upper"
    by (rule scaled_round_integer_between[OF denominator lower upper])
  from bounds no_upper show ?thesis by linarith
qed

lemma scaled_round_integer_of_multiple:
  assumes denominator: "0 < d"
      and multiple:
        "scaled_numerator n d k =
          exact * scaled_denominator n d k"
  shows "scaled_round_integer rm negative n d k = exact"
proof -
  have qpos: "0 < scaled_denominator n d k"
    by (rule scaled_denominator_pos[OF denominator])
  show ?thesis
    unfolding scaled_round_integer_def
    using multiple qpos by simp
qed

lemma scaled_round_integer_lower_from_ratio:
  assumes denominator: "0 < d"
      and lower:
        "(of_nat lower :: rat) \<le>
          (of_nat n / of_nat d) * rat_pow2 k"
  shows "lower \<le> scaled_round_integer rm negative n d k"
proof -
  have scale:
    "(of_nat (scaled_numerator n d k) :: rat) /
       of_nat (scaled_denominator n d k) =
     (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF denominator])
  have ratio:
    "(of_nat lower :: rat) \<le>
      of_nat (scaled_numerator n d k) /
        of_nat (scaled_denominator n d k)"
    using lower scale by simp
  have qpos: "0 < scaled_denominator n d k"
    by (rule scaled_denominator_pos[OF denominator])
  have qpos_rat:
    "0 < (of_nat (scaled_denominator n d k) :: rat)"
    using qpos by simp
  have product_rat:
    "(of_nat lower :: rat) * of_nat (scaled_denominator n d k)
      \<le> of_nat (scaled_numerator n d k)"
    using ratio by (simp only: pos_le_divide_eq[OF qpos_rat])
  have product:
    "lower * scaled_denominator n d k \<le> scaled_numerator n d k"
    using product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_le_iff)
  show ?thesis
    by (rule scaled_round_integer_lower_bound[OF denominator product])
qed

lemma scaled_round_integer_upper_from_ratio:
  assumes denominator: "0 < d"
      and upper:
        "(of_nat n / of_nat d) * rat_pow2 k < (of_nat bound :: rat)"
  shows "scaled_round_integer rm negative n d k \<le> bound"
proof -
  have scale:
    "(of_nat (scaled_numerator n d k) :: rat) /
       of_nat (scaled_denominator n d k) =
     (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF denominator])
  have ratio:
    "(of_nat (scaled_numerator n d k) :: rat) /
       of_nat (scaled_denominator n d k) < of_nat bound"
    using upper scale by simp
  have qpos: "0 < scaled_denominator n d k"
    by (rule scaled_denominator_pos[OF denominator])
  have qpos_rat:
    "0 < (of_nat (scaled_denominator n d k) :: rat)"
    using qpos by simp
  have product_rat:
    "(of_nat (scaled_numerator n d k) :: rat) <
      of_nat bound * of_nat (scaled_denominator n d k)"
    using ratio by (simp only: pos_divide_less_eq[OF qpos_rat])
  have product:
    "scaled_numerator n d k < bound * scaled_denominator n d k"
    using product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_less_iff)
  show ?thesis
    by (rule scaled_round_integer_upper_bound[OF denominator product])
qed

lemma scaled_round_integer_between_from_ratio:
  assumes denominator: "0 < d"
      and lower:
        "(of_nat lower :: rat) \<le>
          (of_nat n / of_nat d) * rat_pow2 k"
      and upper:
        "(of_nat n / of_nat d) * rat_pow2 k < (of_nat upper :: rat)"
  shows
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k \<le> upper"
  using scaled_round_integer_lower_from_ratio[OF denominator lower]
    scaled_round_integer_upper_from_ratio[OF denominator upper]
  by blast

lemma scaled_round_integer_between_from_ratio_strict:
  assumes denominator: "0 < d"
      and lower:
        "(of_nat lower :: rat) \<le>
          (of_nat n / of_nat d) * rat_pow2 k"
      and upper:
        "(of_nat n / of_nat d) * rat_pow2 k < (of_nat upper :: rat)"
      and no_upper: "scaled_round_integer rm negative n d k \<noteq> upper"
  shows
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k < upper"
proof -
  have bounds:
    "lower \<le> scaled_round_integer rm negative n d k \<and>
     scaled_round_integer rm negative n d k \<le> upper"
    by (rule scaled_round_integer_between_from_ratio[OF denominator lower upper])
  from bounds no_upper show ?thesis by linarith
qed

lemma scaled_RNE_error_half:
  assumes "0 < d"
  shows
    "2 * scaled_error
       (scaled_numerator n d k) (scaled_denominator n d k)
       (scaled_round_integer RNE negative n d k)
     \<le> scaled_denominator n d k"
  unfolding scaled_round_integer_def
  by (rule RNE_scaled_error_half[OF scaled_denominator_pos[OF assms]])

lemma scaled_RNA_error_half:
  assumes "0 < d"
  shows
    "2 * scaled_error
       (scaled_numerator n d k) (scaled_denominator n d k)
       (scaled_round_integer RNA negative n d k)
     \<le> scaled_denominator n d k"
  unfolding scaled_round_integer_def
  by (rule RNA_scaled_error_half[OF scaled_denominator_pos[OF assms]])

end

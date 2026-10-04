(* SPDX-License-Identifier: MIT *)

section \<open>Finite arbitrary-precision binary source values\<close>

theory Fp_Arbitrary_Precision
  imports Fp_Round_Format Fp_Round_Value
begin

text \<open>
  A finite arbitrary-precision binary value needs no fixed significand width:
  its significand is an unbounded natural number and its exponent is an
  integer.  The sign remains separate, including when the significand is zero,
  so the record also models the two signed-zero inputs used by the rounding
  interface.

  This is a mathematical source model.  It deliberately does not identify the
  record with a particular library representation such as Rug or MPFR.
\<close>

record ap_binary_float =
  ap_negative :: bool
  ap_significand :: nat
  ap_exponent :: int

definition ap_binary_value :: "ap_binary_float \<Rightarrow> rat" where
  "ap_binary_value x =
    signed_rat (ap_negative x)
      (of_nat (ap_significand x) * rat_pow2 (ap_exponent x))"

definition ap_is_zero :: "ap_binary_float \<Rightarrow> bool" where
  "ap_is_zero x \<longleftrightarrow> ap_significand x = 0"

text \<open>
  Moving a negative binary exponent into the denominator yields precisely the
  natural numerator/denominator interface accepted by
  @{const round_rational_to_format_bits}.  No fraction reduction is needed.
\<close>

definition ap_rational_input :: "ap_binary_float \<Rightarrow> nat \<times> nat" where
  "ap_rational_input x = scale_ratio (ap_significand x) 1 (ap_exponent x)"

definition ap_numerator :: "ap_binary_float \<Rightarrow> nat" where
  "ap_numerator x = fst (ap_rational_input x)"

definition ap_denominator :: "ap_binary_float \<Rightarrow> nat" where
  "ap_denominator x = snd (ap_rational_input x)"

lemma ap_rational_input_nonnegative_exponent:
  assumes "0 \<le> ap_exponent x"
  shows "ap_rational_input x =
    (ap_significand x * 2 ^ nat (ap_exponent x), 1)"
  using assms
  by (simp add: ap_rational_input_def scale_ratio_nonnegative)

lemma ap_rational_input_negative_exponent:
  assumes "ap_exponent x < 0"
  shows "ap_rational_input x =
    (ap_significand x, 2 ^ nat (- ap_exponent x))"
  using assms
  by (simp add: ap_rational_input_def scale_ratio_negative)

lemma ap_denominator_pos [simp]:
  "0 < ap_denominator x"
proof (cases "0 \<le> ap_exponent x")
  case True
  then show ?thesis
    by (simp add: ap_denominator_def ap_rational_input_nonnegative_exponent)
next
  case False
  then have "ap_exponent x < 0" by simp
  then show ?thesis
    by (simp add: ap_denominator_def ap_rational_input_negative_exponent)
qed

lemma ap_numerator_pos_iff [simp]:
  "0 < ap_numerator x \<longleftrightarrow> 0 < ap_significand x"
proof (cases "0 \<le> ap_exponent x")
  case True
  then show ?thesis
    by (simp add: ap_numerator_def ap_rational_input_nonnegative_exponent)
next
  case False
  then have "ap_exponent x < 0" by simp
  then show ?thesis
    by (simp add: ap_numerator_def ap_rational_input_negative_exponent)
qed

lemma ap_nonzero_numerator_pos:
  assumes "\<not> ap_is_zero x"
  shows "0 < ap_numerator x"
  using assms by (simp add: ap_is_zero_def)

lemma ap_unsigned_ratio_exact:
  "(of_nat (ap_numerator x) :: rat) / of_nat (ap_denominator x) =
    of_nat (ap_significand x) * rat_pow2 (ap_exponent x)"
  unfolding ap_numerator_def ap_denominator_def ap_rational_input_def
  using scale_ratio_exact[of 1 "ap_significand x" "ap_exponent x"]
  by (simp add: scaled_numerator_def scaled_denominator_def)

theorem ap_exact_input_value:
  "exact_input_value (ap_negative x) (ap_numerator x) (ap_denominator x) =
    ap_binary_value x"
  by (simp add: exact_input_value_def ap_binary_value_def
      ap_unsigned_ratio_exact)

lemma ap_binary_value_zero_iff [simp]:
  "ap_binary_value x = 0 \<longleftrightarrow> ap_is_zero x"
proof -
  have power_nonzero: "rat_pow2 (ap_exponent x) \<noteq> 0"
    using rat_pow2_pos[of "ap_exponent x"] by linarith
  show ?thesis
    by (cases "ap_negative x")
      (simp_all add: ap_binary_value_def ap_is_zero_def power_nonzero)
qed

definition round_ap_binary_to_format_bits ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> ap_binary_float \<Rightarrow> fp_bits" where
  "round_ap_binary_to_format_bits f rm x =
    round_rational_to_format_bits f rm (ap_negative x)
      (ap_numerator x) (ap_denominator x)"

lemma round_ap_binary_to_format_bits_unfold:
  "round_ap_binary_to_format_bits f rm x =
    round_rational_to_format_bits f rm (ap_negative x)
      (ap_numerator x) (ap_denominator x)"
  by (simp add: round_ap_binary_to_format_bits_def)

lemma round_ap_binary_to_format_bits_negative_bit [simp]:
  "negative_bit (round_ap_binary_to_format_bits f rm x) = ap_negative x"
  by (simp add: round_ap_binary_to_format_bits_def)

theorem ap_nonzero_has_positive_exact_rational_input:
  assumes nonzero: "\<not> ap_is_zero x"
  obtains n d where
    "0 < n"
    "0 < d"
    "exact_input_value (ap_negative x) n d = ap_binary_value x"
    "round_ap_binary_to_format_bits f rm x =
      round_rational_to_format_bits f rm (ap_negative x) n d"
proof
  show "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  show "0 < ap_denominator x" by simp
  show "exact_input_value (ap_negative x)
      (ap_numerator x) (ap_denominator x) = ap_binary_value x"
    by (rule ap_exact_input_value)
  show "round_ap_binary_to_format_bits f rm x =
      round_rational_to_format_bits f rm (ap_negative x)
        (ap_numerator x) (ap_denominator x)"
    by (rule round_ap_binary_to_format_bits_unfold)
qed

end

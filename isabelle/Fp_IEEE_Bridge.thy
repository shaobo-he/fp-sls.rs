(*  SPDX-License-Identifier: MIT

    Bridge between AFP's type-indexed IEEE representation and the dynamic
    format/bit records used by the fp-sls reference model.
*)

section \<open>AFP IEEE fields as a run-time format\<close>

theory Fp_IEEE_Bridge
  imports
    Fp_Format
    IEEE_Floating_Point.IEEE_Properties
begin

text \<open>
  AFP stores the exponent and fraction widths in the type.  The dynamic model
  follows SMT-LIB and the Rust implementation by counting the hidden leading
  significand bit in @{const precision_bits}.
\<close>

definition runtime_format ::
    "('e::len, 'f::len) float itself \<Rightarrow> binary_format"
  where
    "runtime_format _ =
      \<lparr>exponent_bits = LENGTH('e), precision_bits = Suc LENGTH('f)\<rparr>"

lemma runtime_format_fields [simp]:
  "exponent_bits (runtime_format TYPE(('e::len, 'f::len) float)) = LENGTH('e)"
  "precision_bits (runtime_format TYPE(('e::len, 'f::len) float)) = Suc LENGTH('f)"
  "fraction_bits (runtime_format TYPE(('e::len, 'f::len) float)) = LENGTH('f)"
  by (simp_all add: runtime_format_def fraction_bits_def)

lemma runtime_format_exponent_all_ones [simp]:
  "exponent_all_ones (runtime_format TYPE(('e::len, 'f::len) float)) =
    IEEE.emax TYPE(('e, 'f) float)"
  by (simp add: exponent_all_ones_def emax_eq)

lemma runtime_format_bias [simp]:
  "format_bias (runtime_format TYPE(('e::len, 'f::len) float)) =
    IEEE.bias TYPE(('e, 'f) float)"
  by (simp add: format_bias_def IEEE.bias_def)

lemma runtime_format_emin [simp]:
  "format_emin (runtime_format TYPE(('e::len, 'f::len) float)) =
    1 - int (IEEE.bias TYPE(('e, 'f) float))"
  by (simp add: format_emin_def)

lemma runtime_format_valid:
  assumes "2 \<le> LENGTH('e::len)"
  shows "valid_format (runtime_format TYPE(('e, 'f::len) float))"
proof -
  have "Suc 0 \<le> LENGTH('f)"
    by (rule Suc_leI) simp
  with assms show ?thesis
    by (simp add: valid_format_def)
qed

section \<open>Field extraction\<close>

definition runtime_bits :: "('e::len, 'f::len) float \<Rightarrow> fp_bits"
  where
    "runtime_bits x =
      \<lparr>negative_bit = (IEEE.sign x = 1),
       exponent_field = IEEE.exponent x,
       fraction_field = IEEE.fraction x\<rparr>"

definition runtime_float_of_bits ::
    "fp_bits \<Rightarrow> ('e::len, 'f::len) float"
  where
    "runtime_float_of_bits b = IEEE.Abs_float
      (of_nat (if negative_bit b then 1 else 0),
       of_nat (exponent_field b), of_nat (fraction_field b))"

lemma runtime_bits_fields [simp]:
  "negative_bit (runtime_bits x) \<longleftrightarrow> IEEE.sign x = 1"
  "exponent_field (runtime_bits x) = IEEE.exponent x"
  "fraction_field (runtime_bits x) = IEEE.fraction x"
  by (simp_all add: runtime_bits_def)

lemma runtime_bits_of_runtime_float:
  assumes "bits_well_formed
    (runtime_format TYPE(('e::len, 'f::len) float)) b"
  shows "runtime_bits (runtime_float_of_bits b :: ('e, 'f) float) = b"
proof -
  have exponent_bound: "exponent_field b < 2 ^ LENGTH('e)"
    using assms by (simp add: bits_well_formed_def)
  have fraction_bound: "fraction_field b < 2 ^ LENGTH('f)"
    using assms by (simp add: bits_well_formed_def)
  have exponent_word:
    "unat (of_nat (exponent_field b) :: 'e word) = exponent_field b"
    by (rule unat_of_nat_len[OF exponent_bound])
  have fraction_word:
    "unat (of_nat (fraction_field b) :: 'f word) = fraction_field b"
    by (rule unat_of_nat_len[OF fraction_bound])
  show ?thesis
    by (rule fp_bits.equality)
      (simp_all add: runtime_bits_def runtime_float_of_bits_def
        IEEE.sign.rep_eq IEEE.exponent.rep_eq IEEE.fraction.rep_eq
        IEEE.Abs_float_inverse exponent_word fraction_word)
qed

lemma ieee_exponent_field_bound:
  fixes x :: "('e::len, 'f::len) float"
  shows "IEEE.exponent x < 2 ^ LENGTH('e)"
proof -
  have le: "IEEE.exponent x \<le> 2 ^ LENGTH('e) - 1"
    using exponent_le[of x] by (simp add: mask_eq_exp_minus_1)
  have pos: "0 < (2::nat) ^ LENGTH('e)" by simp
  have pred: "(2::nat) ^ LENGTH('e) - 1 < 2 ^ LENGTH('e)"
    by (rule diff_less) (simp_all add: pos)
  from le pred show ?thesis by (rule order_le_less_trans)
qed

lemma ieee_fraction_field_bound:
  fixes x :: "('e::len, 'f::len) float"
  shows "IEEE.fraction x < 2 ^ LENGTH('f)"
proof -
  have le: "IEEE.fraction x \<le> 2 ^ LENGTH('f) - 1"
    using float_frac_le[of x] .
  have pos: "0 < (2::nat) ^ LENGTH('f)" by simp
  have pred: "(2::nat) ^ LENGTH('f) - 1 < 2 ^ LENGTH('f)"
    by (rule diff_less) (simp_all add: pos)
  from le pred show ?thesis by (rule order_le_less_trans)
qed

lemma runtime_bits_well_formed [simp]:
  fixes x :: "('e::len, 'f::len) float"
  shows "bits_well_formed
    (runtime_format TYPE(('e, 'f) float)) (runtime_bits x)"
  using ieee_exponent_field_bound[of x] ieee_fraction_field_bound[of x]
  by (simp add: bits_well_formed_def)

section \<open>Classification agreement\<close>

text \<open>
  These equivalences are the checked representation bridge needed before a
  dynamic rounding result can be related to AFP's IEEE semantics.  They are
  unconditional: field well-formedness follows from the word types themselves.
\<close>

lemma runtime_bits_is_nan_iff [simp]:
  fixes x :: "('e::len, 'f::len) float"
  shows "bits_is_nan (runtime_format TYPE(('e, 'f) float)) (runtime_bits x)
    \<longleftrightarrow> IEEE.is_nan x"
  by (simp add: bits_is_nan_def IEEE.is_nan_def)

lemma runtime_bits_is_infinity_iff [simp]:
  fixes x :: "('e::len, 'f::len) float"
  shows "bits_is_infinity (runtime_format TYPE(('e, 'f) float)) (runtime_bits x)
    \<longleftrightarrow> IEEE.is_infinity x"
  by (simp add: bits_is_infinity_def IEEE.is_infinity_def)

lemma runtime_bits_is_zero_iff [simp]:
  fixes x :: "('e::len, 'f::len) float"
  shows "bits_is_zero (runtime_bits x) \<longleftrightarrow> IEEE.is_zero x"
  by (simp add: bits_is_zero_def IEEE.is_zero_def)

lemma decode_runtime_bits_nan:
  fixes x :: "('e::len, 'f::len) float"
  assumes "IEEE.is_nan x"
  shows "decode_bits (runtime_format TYPE(('e, 'f) float)) (runtime_bits x) =
    Dynamic_NaN"
  using assms by (simp add: decode_bits_def)

lemma decode_runtime_bits_infinity:
  fixes x :: "('e::len, 'f::len) float"
  assumes infinity: "IEEE.is_infinity x"
  shows "decode_bits (runtime_format TYPE(('e, 'f) float)) (runtime_bits x) =
    Dynamic_Infinity (IEEE.sign x = 1)"
proof -
  have "\<not> IEEE.is_nan x"
    using infinity float_distinct(1) by blast
  with infinity show ?thesis
    by (simp add: decode_bits_def)
qed

lemma decode_runtime_bits_zero:
  fixes x :: "('e::len, 'f::len) float"
  assumes zero: "IEEE.is_zero x"
  shows "decode_bits (runtime_format TYPE(('e, 'f) float)) (runtime_bits x) =
    Dynamic_Finite (IEEE.sign x = 1) 0"
proof -
  have not_nan: "\<not> IEEE.is_nan x"
    using zero float_distinct(4) by blast
  have not_infinity: "\<not> IEEE.is_infinity x"
    using zero float_distinct(7) by blast
  from zero not_nan not_infinity show ?thesis
    by (simp add: decode_bits_def finite_magnitude_def IEEE.is_zero_def)
qed

section \<open>Finite-value agreement\<close>

text \<open>
  The dynamic model stores an exact rational magnitude, whereas AFP's
  @{const IEEE.valof} returns a real.  The first lemma connects the two
  definitions of an integer power of two; the remaining algebra is independent
  of the floating-point classification.
\<close>

lemma of_rat_pow2_rat_real [simp]:
  "(of_rat (pow2_rat k) :: real) = (2::real) powi k"
proof (cases "0 \<le> k")
  case True
  then show ?thesis
    by (simp add: pow2_rat_def power_int_def of_rat_power)
next
  case False
  have cast:
    "(of_rat (pow2_rat k) :: real) =
      inverse ((2::real) ^ nat (- k))"
    using False
    by (simp add: pow2_rat_def of_rat_inverse of_rat_power)
  also have "... = inverse (2::real) ^ nat (- k)"
    by (rule power_inverse[symmetric])
  also have "... = (2::real) powi k"
    using False by (simp add: power_int_def)
  finally show ?thesis .
qed

lemma real_two_powi_nat_sub_nat_sub:
  "(2::real) powi (int a - int b - int c) =
    (2 ^ a / 2 ^ b) / 2 ^ c"
  by (simp add: power_int_diff)

lemma real_two_powi_one_sub_nat_sub:
  "(2::real) powi (1 - int b - int c) =
    (2 / 2 ^ b) / 2 ^ c"
  by (simp add: power_int_diff)

lemma abs_valof_fields:
  fixes x :: "('e::len, 'f::len) float"
  shows "\<bar>IEEE.valof x\<bar> =
    (if IEEE.exponent x = 0 then
       (2 / 2 ^ IEEE.bias TYPE(('e, 'f) float)) *
         (real (IEEE.fraction x) / 2 ^ LENGTH('f))
     else
       (2 ^ IEEE.exponent x / 2 ^ IEEE.bias TYPE(('e, 'f) float)) *
         (1 + real (IEEE.fraction x) / 2 ^ LENGTH('f)))"
  by (simp add: valof_eq abs_mult)

lemma add_scale_divide:
  fixes p a b :: real
  assumes "p \<noteq> 0"
  shows "(p + a) * (b / p) = b * (1 + a / p)"
proof -
  have reorder: "a * (b / p) = b * (a / p)"
    by (simp add: divide_inverse mult_ac)
  have cancel: "p * b / p = b"
    by (rule nonzero_mult_div_cancel_left[OF assms])
  have "(p + a) * (b / p) = p * (b / p) + a * (b / p)"
    by (rule distrib_right)
  also have "... = b + a * (b / p)" by (simp add: cancel)
  also have "... = b + b * (a / p)" by (simp add: reorder)
  also have "... = b * (1 + a / p)" by (simp add: distrib_left)
  finally show ?thesis .
qed

lemma runtime_magnitude_eq_abs_valof:
  fixes x :: "('e::len, 'f::len) float"
  shows "(of_rat
      (finite_magnitude (runtime_format TYPE(('e, 'f) float)) (runtime_bits x))
      :: real) = \<bar>IEEE.valof x\<bar>"
proof (cases "IEEE.exponent x = 0")
  case True
  then show ?thesis
    by (simp add: finite_magnitude_def of_rat_mult abs_valof_fields
        real_two_powi_one_sub_nat_sub divide_inverse mult_ac)
next
  case False
  have algebra:
    "((2::real) ^ LENGTH('f) + real (IEEE.fraction x)) *
       (((2::real) ^ IEEE.exponent x /
          2 ^ IEEE.bias TYPE(('e, 'f) float)) / 2 ^ LENGTH('f)) =
     ((2::real) ^ IEEE.exponent x /
        2 ^ IEEE.bias TYPE(('e, 'f) float)) *
       (1 + real (IEEE.fraction x) / 2 ^ LENGTH('f))"
    by (rule add_scale_divide) simp
  show ?thesis
    using False algebra
    by (simp add: finite_magnitude_def of_rat_add of_rat_mult of_rat_power
        abs_valof_fields real_two_powi_nat_sub_nat_sub)
qed

text \<open>
  The equation above also holds for AFP's formal valuation of special bit
  patterns.  The following is the semantically relevant corollary: under the
  precise assumption that the source is finite, the dynamic finite magnitude
  is exactly the absolute AFP value after embedding the rational into the
  reals.
\<close>

lemma finite_magnitude_runtime_bits_eq_abs_valof:
  fixes x :: "('e::len, 'f::len) float"
  assumes "IEEE.is_finite x"
  shows "(of_rat
      (finite_magnitude (runtime_format TYPE(('e, 'f) float)) (runtime_bits x))
      :: real) = \<bar>IEEE.valof x\<bar>"
  using runtime_magnitude_eq_abs_valof[of x] .

end

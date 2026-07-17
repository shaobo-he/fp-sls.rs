(* SPDX-License-Identifier: MIT *)

section \<open>Overflow boundaries and mode-dependent results\<close>

theory Fp_Round_Overflow
  imports
    Fp_Round_Format
    Fp_IEEE_Exact
    Fp_SingleNaN_Bridge
begin

text \<open>
  The dynamic reference model and AFP use the same two finite endpoints.
  Exposing them explicitly on the single-NaN quotient makes the overflow
  clauses of @{const fp_round_rel} usable without reasoning about quotient
  representatives at every call site.
\<close>

definition fp_top_finite ::
    "('e::len, 'f::len) floatSingleNaN" where
  "fp_top_finite = single_nan_of_float
    (IEEE.topfloat :: ('e, 'f) float)"

definition fp_bottom_finite ::
    "('e::len, 'f::len) floatSingleNaN" where
  "fp_bottom_finite = single_nan_of_float
    (IEEE.bottomfloat :: ('e, 'f) float)"

lemma fp_top_finite_is_finite [simp]:
  "is_finite (fp_top_finite :: ('e::len, 'f::len) floatSingleNaN)"
  by (simp only: fp_top_finite_def single_nan_of_float_is_finite;
      rule finite_topfloat)

lemma fp_bottom_finite_is_finite [simp]:
  "is_finite (fp_bottom_finite :: ('e::len, 'f::len) floatSingleNaN)"
  by (simp only: fp_bottom_finite_def single_nan_of_float_is_finite;
      rule finite_bottomfloat)

lemma fp_top_finite_valof:
  assumes width: "1 < LENGTH('e::len)"
  shows "valof (fp_top_finite :: ('e, 'f::len) floatSingleNaN) =
    fp_largest TYPE(('e, 'f) floatSingleNaN)"
proof -
  have finite:
    "IEEE.is_finite (IEEE.topfloat :: ('e, 'f) float)"
    by (rule finite_topfloat)
  have quotient:
    "valof (single_nan_of_float (IEEE.topfloat :: ('e, 'f) float)) =
      IEEE.valof (IEEE.topfloat :: ('e, 'f) float)"
    by (rule single_nan_of_float_valof[OF finite])
  show ?thesis
    using quotient valof_topfloat[OF width, where 'f='f]
    by (simp add: fp_top_finite_def fp_largest_def)
qed

lemma fp_bottom_finite_valof:
  assumes width: "1 < LENGTH('e::len)"
  shows "valof (fp_bottom_finite :: ('e, 'f::len) floatSingleNaN) =
    - fp_largest TYPE(('e, 'f) floatSingleNaN)"
proof -
  have finite:
    "IEEE.is_finite (IEEE.bottomfloat :: ('e, 'f) float)"
    by (rule finite_bottomfloat)
  have quotient:
    "valof (single_nan_of_float (IEEE.bottomfloat :: ('e, 'f) float)) =
      IEEE.valof (IEEE.bottomfloat :: ('e, 'f) float)"
    by (rule single_nan_of_float_valof[OF finite])
  show ?thesis
    using quotient bottomfloat_eq_m_largest[OF width, where 'f='f]
    by (simp add: fp_bottom_finite_def fp_largest_def)
qed

lemma fp_largest_nonnegative:
  assumes width: "1 < LENGTH('e::len)"
  shows "0 \<le> fp_largest TYPE(('e, 'f::len) floatSingleNaN)"
proof -
  have nonnegative:
    "0 \<le> IEEE.valof (IEEE.topfloat :: ('e, 'f) float)"
    by (rule valof_nonneg) (rule topfloat_simps(1))
  show ?thesis
    using nonnegative valof_topfloat[OF width, where 'f='f]
    by (simp add: fp_largest_def)
qed

lemma fp_top_greatest_finite_below:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and above: "fp_largest TYPE(('e, 'f::len) floatSingleNaN) < x"
  shows "fp_greatest_finite_below x
    (fp_top_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have top_value:
    "valof (fp_top_finite :: ('e, 'f) floatSingleNaN) =
      fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_top_finite_valof[OF width])
  show ?thesis
    unfolding fp_greatest_finite_below_def
  proof (intro conjI allI impI)
    show "is_finite (fp_top_finite :: ('e, 'f) floatSingleNaN)" by simp
    show "valof (fp_top_finite :: ('e, 'f) floatSingleNaN) \<le> x"
      using top_value above by linarith
    fix b :: "('e, 'f) floatSingleNaN"
    assume "is_finite b \<and> valof b \<le> x"
    then have "is_finite b" by simp
    then have "valof b \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
      by (rule fp_finite_le_largest[OF width])
    then show "valof b \<le> valof
        (fp_top_finite :: ('e, 'f) floatSingleNaN)"
      using top_value by simp
  qed
qed

lemma fp_bottom_least_finite_above:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and below: "x < - fp_largest TYPE(('e, 'f::len) floatSingleNaN)"
  shows "fp_least_finite_above x
    (fp_bottom_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have bottom_value:
    "valof (fp_bottom_finite :: ('e, 'f) floatSingleNaN) =
      - fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_bottom_finite_valof[OF width])
  show ?thesis
    unfolding fp_least_finite_above_def
  proof (intro conjI allI impI)
    show "is_finite (fp_bottom_finite :: ('e, 'f) floatSingleNaN)" by simp
    show "x \<le> valof (fp_bottom_finite :: ('e, 'f) floatSingleNaN)"
      using bottom_value below by linarith
    fix b :: "('e, 'f) floatSingleNaN"
    assume "is_finite b \<and> x \<le> valof b"
    then have "is_finite b" by simp
    then have "- fp_largest TYPE(('e, 'f) floatSingleNaN) \<le> valof b"
      by (rule fp_finite_ge_minus_largest[OF width])
    then show "valof (fp_bottom_finite :: ('e, 'f) floatSingleNaN)
        \<le> valof b"
      using bottom_value by simp
  qed
qed

section \<open>The corrected IEEE relation at overflow\<close>

lemma fp_threshold_pos:
  assumes width: "1 < LENGTH('e::len)"
  shows "0 < fp_threshold TYPE(('e, 'f::len) floatSingleNaN)"
proof -
  have top_lt:
    "valof (fp_top_finite :: ('e, 'f) floatSingleNaN) <
      fp_threshold TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_finite_lt_threshold[OF width]) simp
  have top_nonnegative:
    "0 \<le> valof (fp_top_finite :: ('e, 'f) floatSingleNaN)"
    using fp_top_finite_valof[OF width, where 'f='f]
      fp_largest_nonnegative[OF width, where 'f='f]
    by simp
  show ?thesis using top_nonnegative top_lt by linarith
qed

lemma fp_round_RNE_at_positive_threshold [simp]:
  assumes width: "1 < LENGTH('e::len)"
  shows "fp_round_rel RNE
      (fp_threshold TYPE(('e::len, 'f::len) floatSingleNaN))
      (plus_infinity :: ('e, 'f) floatSingleNaN)"
  using fp_threshold_pos[OF width, where 'f='f] by simp

lemma fp_round_RNE_at_negative_threshold [simp]:
  assumes width: "1 < LENGTH('e::len)"
  shows "fp_round_rel RNE
      (- fp_threshold TYPE(('e::len, 'f::len) floatSingleNaN))
      (minus_infinity :: ('e, 'f) floatSingleNaN)"
  using fp_threshold_pos[OF width, where 'f='f] by simp

lemma fp_round_RNA_at_positive_threshold [simp]:
  assumes width: "1 < LENGTH('e::len)"
  shows "fp_round_rel RNA
      (fp_threshold TYPE(('e::len, 'f::len) floatSingleNaN))
      (plus_infinity :: ('e, 'f) floatSingleNaN)"
  using fp_threshold_pos[OF width, where 'f='f] by simp

lemma fp_round_RNA_at_negative_threshold [simp]:
  assumes width: "1 < LENGTH('e::len)"
  shows "fp_round_rel RNA
      (- fp_threshold TYPE(('e::len, 'f::len) floatSingleNaN))
      (minus_infinity :: ('e, 'f) floatSingleNaN)"
  using fp_threshold_pos[OF width, where 'f='f] by simp

lemma fp_round_RTP_above_largest [simp]:
  assumes "fp_largest TYPE(('e::len, 'f::len) floatSingleNaN) < x"
  shows "fp_round_rel RTP x
    (plus_infinity :: ('e, 'f) floatSingleNaN)"
  using assms by simp

lemma fp_round_RTN_below_minus_largest [simp]:
  assumes "x < - fp_largest TYPE(('e::len, 'f::len) floatSingleNaN)"
  shows "fp_round_rel RTN x
    (minus_infinity :: ('e, 'f) floatSingleNaN)"
  using assms by simp

lemma fp_round_RTN_above_largest [simp]:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and above: "fp_largest TYPE(('e, 'f::len) floatSingleNaN) < x"
  shows "fp_round_rel RTN x
    (fp_top_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have nonnegative:
    "0 \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_largest_nonnegative[OF width])
  have not_negative_overflow:
    "\<not> x < - fp_largest TYPE(('e, 'f) floatSingleNaN)"
    using nonnegative above by linarith
  show ?thesis
    using not_negative_overflow fp_top_greatest_finite_below[OF width above]
    by simp
qed

lemma fp_round_RTZ_above_largest [simp]:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and above: "fp_largest TYPE(('e, 'f::len) floatSingleNaN) < x"
  shows "fp_round_rel RTZ x
    (fp_top_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have nonnegative:
    "0 \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_largest_nonnegative[OF width])
  have x_nonnegative: "0 \<le> x" using nonnegative above by linarith
  show ?thesis
    using x_nonnegative fp_top_greatest_finite_below[OF width above]
    by simp
qed

lemma fp_round_RTP_below_minus_largest [simp]:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and below: "x < - fp_largest TYPE(('e, 'f::len) floatSingleNaN)"
  shows "fp_round_rel RTP x
    (fp_bottom_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have nonnegative:
    "0 \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_largest_nonnegative[OF width])
  have not_positive_overflow:
    "\<not> fp_largest TYPE(('e, 'f) floatSingleNaN) < x"
    using nonnegative below by linarith
  show ?thesis
    using not_positive_overflow fp_bottom_least_finite_above[OF width below]
    by simp
qed

lemma fp_round_RTZ_below_minus_largest [simp]:
  fixes x :: real
  assumes width: "1 < LENGTH('e::len)"
      and below: "x < - fp_largest TYPE(('e, 'f::len) floatSingleNaN)"
  shows "fp_round_rel RTZ x
    (fp_bottom_finite :: ('e, 'f) floatSingleNaN)"
proof -
  have x_negative: "x < 0"
    using below fp_largest_nonnegative[OF width, where 'f='f] by linarith
  show ?thesis
    using x_negative fp_bottom_least_finite_above[OF width below]
    by simp
qed

section \<open>Agreement of the dynamic endpoint encodings\<close>

lemma runtime_bits_topfloat:
  "runtime_bits (IEEE.topfloat :: ('e::len, 'f::len) float) =
    maximum_finite_bits (runtime_format TYPE(('e, 'f) float)) False"
  using topfloat_simps[where 'e='e and 'f='f]
  by (simp add: runtime_bits_def maximum_finite_bits_def)

lemma runtime_bits_bottomfloat:
  "runtime_bits (IEEE.bottomfloat :: ('e::len, 'f::len) float) =
    maximum_finite_bits (runtime_format TYPE(('e, 'f) float)) True"
  using bottomfloat_simps[where 'e='e and 'f='f]
  by (simp add: runtime_bits_def maximum_finite_bits_def)

lemma runtime_bits_plus_infinity:
  "runtime_bits (IEEE.plus_infinity :: ('e::len, 'f::len) float) =
    infinity_bits (runtime_format TYPE(('e, 'f) float)) False"
  using infinity_simps[where 'e='e and 'f='f]
  by (simp add: runtime_bits_def infinity_bits_def)

lemma runtime_bits_minus_infinity:
  "runtime_bits (IEEE.minus_infinity :: ('e::len, 'f::len) float) =
    infinity_bits (runtime_format TYPE(('e, 'f) float)) True"
  using infinity_simps[where 'e='e and 'f='f]
  by (simp add: runtime_bits_def infinity_bits_def)

lemma runtime_maximum_finite_magnitude:
  assumes width: "1 < LENGTH('e::len)"
  shows "(of_rat (finite_magnitude
      (runtime_format TYPE(('e, 'f::len) float))
      (maximum_finite_bits
        (runtime_format TYPE(('e, 'f) float)) negative)) :: real) =
    fp_largest TYPE(('e, 'f) floatSingleNaN)"
proof -
  let ?top = "IEEE.topfloat :: ('e, 'f) float"
  have bits:
    "finite_magnitude (runtime_format TYPE(('e, 'f) float))
        (maximum_finite_bits
          (runtime_format TYPE(('e, 'f) float)) negative) =
      finite_magnitude (runtime_format TYPE(('e, 'f) float))
        (runtime_bits ?top)"
    using runtime_bits_topfloat[where 'e='e and 'f='f]
    by (cases negative)
      (simp_all add: finite_magnitude_def maximum_finite_bits_def
        runtime_bits_def)
  have magnitude:
    "(of_rat (finite_magnitude (runtime_format TYPE(('e, 'f) float))
        (runtime_bits ?top)) :: real) = \<bar>IEEE.valof ?top\<bar>"
    by (rule runtime_magnitude_eq_abs_valof)
  have nonnegative: "0 \<le> IEEE.valof ?top"
    by (rule valof_nonneg) (rule topfloat_simps(1))
  show ?thesis
    using bits magnitude nonnegative valof_topfloat[OF width, where 'f='f]
    by (simp add: fp_largest_def)
qed

section \<open>The dynamic nearest-overflow threshold\<close>

definition format_nearest_overflow_threshold ::
    "binary_format \<Rightarrow> rat" where
  "format_nearest_overflow_threshold f =
    ((of_nat (2 ^ precision_bits f) :: rat) - 1 / 2) *
      rat_pow2 (format_emax f - int (fraction_bits f))"

definition format_maximum_finite_magnitude ::
    "binary_format \<Rightarrow> rat" where
  "format_maximum_finite_magnitude f =
    ((of_nat (2 ^ precision_bits f) :: rat) - 1) *
      rat_pow2 (format_emax f - int (fraction_bits f))"

lemma valid_format_bias_pos:
  assumes valid: "valid_format f"
  shows "0 < format_bias f"
proof -
  have bits: "2 \<le> exponent_bits f"
    by (rule valid_format_exponent_bits[OF valid])
  have exponent: "1 \<le> exponent_bits f - 1"
    using bits by simp
  have power: "(2::nat) ^ 1 \<le> 2 ^ (exponent_bits f - 1)"
    by (rule power_increasing) (use exponent in simp_all)
  show ?thesis
    using power by (simp add: format_bias_def)
qed

lemma valid_format_emin_le_emax:
  assumes valid: "valid_format f"
  shows "format_emin f \<le> format_emax f"
  using valid_format_bias_pos[OF valid]
  by (simp add: format_emin_def format_emax_def; linarith)

lemma valid_format_twice_bias:
  assumes valid: "valid_format f"
  shows "2 * format_bias f = exponent_all_ones f - 1"
proof -
  have bits_pos: "0 < exponent_bits f"
    using valid by (simp add: valid_format_def)
  then obtain k where bits: "exponent_bits f = Suc k"
    by (cases "exponent_bits f") auto
  have power_pos: "0 < (2::nat) ^ k" by simp
  show ?thesis
    using power_pos
    by (simp add: format_bias_def exponent_all_ones_def bits power_Suc
        algebra_simps)
qed

lemma normal_result_bits_at_maximum:
  assumes valid: "valid_format f"
  shows "normal_result_bits f negative
      (2 ^ precision_bits f - 1) (format_emax f) =
    maximum_finite_bits f negative"
proof -
  have precision: "precision_bits f = Suc (fraction_bits f)"
    by (rule valid_format_precision_as_fraction[OF valid])
  have bias_pos: "0 < format_bias f"
    by (rule valid_format_bias_pos[OF valid])
  have exponent:
    "nat (format_emax f + int (format_bias f)) =
      exponent_all_ones f - 1"
    using valid_format_twice_bias[OF valid] bias_pos
    by (simp add: format_emax_def)
  have fraction:
    "(2::nat) ^ precision_bits f - 1 - 2 ^ fraction_bits f =
      2 ^ fraction_bits f - 1"
    using precision by (simp add: power_Suc)
  show ?thesis
  proof (rule fp_bits.equality)
    show "negative_bit
        (normal_result_bits f negative (2 ^ precision_bits f - 1)
          (format_emax f)) =
      negative_bit (maximum_finite_bits f negative)"
      by (simp add: normal_result_bits_def maximum_finite_bits_def)
    show "exponent_field
        (normal_result_bits f negative (2 ^ precision_bits f - 1)
          (format_emax f)) =
      exponent_field (maximum_finite_bits f negative)"
      by (simp add: normal_result_bits_def maximum_finite_bits_def exponent)
    show "fraction_field
        (normal_result_bits f negative (2 ^ precision_bits f - 1)
          (format_emax f)) =
      fraction_field (maximum_finite_bits f negative)"
      using fraction
      by (simp only: normal_result_bits_def maximum_finite_bits_def
          fp_bits.simps)
    show "fp_bits.more
        (normal_result_bits f negative (2 ^ precision_bits f - 1)
          (format_emax f)) =
      fp_bits.more (maximum_finite_bits f negative)"
      by (simp add: normal_result_bits_def maximum_finite_bits_def)
  qed
qed

lemma maximum_finite_magnitude_formula:
  assumes valid: "valid_format f"
  shows "finite_magnitude f (maximum_finite_bits f negative) =
    format_maximum_finite_magnitude f"
proof -
  let ?m = "(2::nat) ^ precision_bits f - 1"
  have bits:
    "normal_result_bits f negative ?m (format_emax f) =
      maximum_finite_bits f negative"
    by (rule normal_result_bits_at_maximum[OF valid])
  have normal: "format_emin f \<le> format_emax f"
    by (rule valid_format_emin_le_emax[OF valid])
  have biased_pos:
    "0 < format_emax f + int (format_bias f)"
    by (rule normal_biased_exponent_bounds(1)[OF valid normal]) simp
  have biased_bound:
    "nat (format_emax f + int (format_bias f)) < exponent_all_ones f"
    by (rule normal_biased_exponent_bounds(2)[OF valid normal]) simp
  have significand_lower: "(2::nat) ^ fraction_bits f \<le> ?m"
  proof -
    have precision: "precision_bits f = Suc (fraction_bits f)"
      by (rule valid_format_precision_as_fraction[OF valid])
    have power_pos: "0 < (2::nat) ^ fraction_bits f" by simp
    show ?thesis using precision power_pos by (simp add: power_Suc)
  qed
  have decoded:
    "decode_bits f (normal_result_bits f negative ?m (format_emax f)) =
      Dynamic_Finite negative
        (of_nat ?m *
          pow2_rat (format_emax f - int (fraction_bits f)))"
    by (rule decode_normal_result_bits[
          OF valid biased_pos biased_bound significand_lower])
  have decoded_max:
    "decode_bits f (maximum_finite_bits f negative) =
      Dynamic_Finite negative
        (finite_magnitude f (maximum_finite_bits f negative))"
    by (rule decode_maximum_finite_bits[OF valid])
  have equality:
    "finite_magnitude f (maximum_finite_bits f negative) =
      of_nat ?m * pow2_rat (format_emax f - int (fraction_bits f))"
    using decoded decoded_max bits by simp
  show ?thesis
    using equality
    by (simp add: format_maximum_finite_magnitude_def
        rat_pow2_eq_pow2_rat)
qed

lemma runtime_format_maximum_finite_magnitude:
  assumes width: "1 < LENGTH('e::len)"
  shows "(of_rat (format_maximum_finite_magnitude
      (runtime_format TYPE(('e, 'f::len) float))) :: real) =
    fp_largest TYPE(('e, 'f) floatSingleNaN)"
proof -
  have valid:
    "valid_format (runtime_format TYPE(('e, 'f) float))"
    by (rule runtime_format_valid) (use width in simp)
  have formula:
    "format_maximum_finite_magnitude
        (runtime_format TYPE(('e, 'f) float)) =
      finite_magnitude (runtime_format TYPE(('e, 'f) float))
        (maximum_finite_bits
          (runtime_format TYPE(('e, 'f) float)) False)"
    using maximum_finite_magnitude_formula[OF valid, of False] by simp
  show ?thesis
    using runtime_maximum_finite_magnitude[OF width, of False, where 'f='f]
      formula by simp
qed

lemma format_maximum_at_least_binade:
  assumes valid: "valid_format f"
  shows "rat_pow2 (format_emax f) \<le>
    format_maximum_finite_magnitude f"
proof -
  let ?fb = "fraction_bits f"
  let ?step = "rat_pow2 (format_emax f - int ?fb)"
  have precision: "precision_bits f = Suc ?fb"
    by (rule valid_format_precision_as_fraction[OF valid])
  have one_le: "(1::rat) \<le> of_nat (2 ^ ?fb)" by simp
  have precision_power:
    "(of_nat (2 ^ precision_bits f) :: rat) =
      2 * of_nat (2 ^ ?fb)"
    using precision by (simp add: power_Suc)
  have coefficient:
    "(of_nat (2 ^ ?fb) :: rat) \<le>
      of_nat (2 ^ precision_bits f) - 1"
    using one_le precision_power by linarith
  have multiplied:
    "(of_nat (2 ^ ?fb) :: rat) * ?step \<le>
      (of_nat (2 ^ precision_bits f) - 1) * ?step"
    by (rule mult_right_mono[OF coefficient rat_pow2_nonnegative])
  have split:
    "(of_nat (2 ^ ?fb) :: rat) * ?step =
      rat_pow2 (format_emax f)"
  proof -
    have "(of_nat (2 ^ ?fb) :: rat) * ?step =
        rat_pow2 (int ?fb) * rat_pow2 (format_emax f - int ?fb)"
      by simp
    also have "... = rat_pow2 (format_emax f)"
      by (simp only: rat_pow2_add[symmetric]; simp add: add.commute)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding format_maximum_finite_magnitude_def
  proof -
    have "rat_pow2 (format_emax f) =
        (of_nat (2 ^ ?fb) :: rat) * ?step"
      using split by simp
    also have "... \<le>
        (of_nat (2 ^ precision_bits f) - 1) * ?step"
      by (rule multiplied)
    finally show
      "rat_pow2 (format_emax f) \<le>
        (of_nat (2 ^ precision_bits f) - 1) * ?step" .
  qed
qed

lemma format_threshold_at_least_binade:
  assumes valid: "valid_format f"
  shows "rat_pow2 (format_emax f) \<le>
    format_nearest_overflow_threshold f"
proof -
  let ?fb = "fraction_bits f"
  let ?step = "rat_pow2 (format_emax f - int ?fb)"
  have precision: "precision_bits f = Suc ?fb"
    by (rule valid_format_precision_as_fraction[OF valid])
  have coefficient:
    "(of_nat (2 ^ ?fb) :: rat) \<le>
      of_nat (2 ^ precision_bits f) - 1 / 2"
  proof -
    have one_le: "(1::rat) \<le> of_nat (2 ^ ?fb)" by simp
    have precision_power:
      "(of_nat (2 ^ precision_bits f) :: rat) =
        2 * of_nat (2 ^ ?fb)"
      using precision by (simp add: power_Suc)
    show ?thesis
      using precision_power one_le by linarith
  qed
  have multiplied:
    "(of_nat (2 ^ ?fb) :: rat) * ?step \<le>
      (of_nat (2 ^ precision_bits f) - 1 / 2) * ?step"
    by (rule mult_right_mono[OF coefficient rat_pow2_nonnegative])
  have split:
    "(of_nat (2 ^ ?fb) :: rat) * ?step =
      rat_pow2 (format_emax f)"
  proof -
    have
      "(of_nat (2 ^ ?fb) :: rat) * ?step =
        rat_pow2 (int ?fb) *
          rat_pow2 (format_emax f - int ?fb)"
      by simp
    also have "... = rat_pow2 (format_emax f)"
      by (simp only: rat_pow2_add[symmetric]; simp add: add.commute)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding format_nearest_overflow_threshold_def
  proof -
    have "rat_pow2 (format_emax f) =
        (of_nat (2 ^ ?fb) :: rat) * ?step"
      using split by simp
    also have "... \<le>
        (of_nat (2 ^ precision_bits f) - 1 / 2) * ?step"
      by (rule multiplied)
    finally show
      "rat_pow2 (format_emax f) \<le>
        (of_nat (2 ^ precision_bits f) - 1 / 2) * ?step" .
  qed
qed

lemma runtime_format_nearest_overflow_threshold:
  "(of_rat (format_nearest_overflow_threshold
      (runtime_format TYPE(('e::len, 'f::len) float))) :: real) =
    fp_threshold TYPE(('e, 'f) floatSingleNaN)"
proof -
  let ?E = "LENGTH('e)"
  let ?F = "LENGTH('f)"
  let ?B = "(2::nat) ^ (?E - 1) - 1"
  have E_pos: "0 < ?E" by simp
  then obtain k where E: "?E = Suc k"
    by (cases ?E) auto
  have exponent_identity: "(2::nat) ^ ?E - 2 = 2 * ?B"
    using E by (simp add: power_Suc algebra_simps)
  have exponent_scale:
    "(2::real) ^ (2 ^ ?E - 2) / 2 ^ ?B = 2 ^ ?B"
  proof -
    have "(2::real) ^ ((2::nat) ^ ?E - 2) / 2 ^ ?B =
        2 ^ (2 * ?B) / 2 ^ ?B"
      by (simp only: exponent_identity)
    also have "... = 2 ^ ?B"
    proof -
      have twice: "2 * ?B = ?B + ?B" by simp
      have square: "(2::real) ^ (2 * ?B) = 2 ^ ?B * 2 ^ ?B"
        by (simp only: twice power_add)
      show ?thesis by (simp only: square; simp)
    qed
    finally show ?thesis .
  qed
  have powr_scale:
    "(2::real) powr (real ?B - real ?F) =
      2 ^ ?B / 2 ^ ?F"
  proof -
    have B_power: "(2::real) powr real ?B = 2 ^ ?B"
      by (rule powr_realpow) simp
    have F_power: "(2::real) powr real ?F = 2 ^ ?F"
      by (rule powr_realpow) simp
    have "(2::real) powr (real ?B - real ?F) =
        2 powr real ?B / 2 powr real ?F"
      by (rule powr_diff)
    also have "... = 2 ^ ?B / 2 ^ ?F"
      by (simp only: B_power F_power)
    finally show ?thesis .
  qed
  have coefficient_scale:
    "(2 * (2::real) ^ ?F - 1 / 2) * (2 ^ ?B / 2 ^ ?F) =
      2 ^ ?B * (2 - 1 / (2 * 2 ^ ?F))"
  proof -
    let ?P = "(2::real) ^ ?F"
    let ?Q = "(2::real) ^ ?B"
    have P_nonzero: "?P \<noteq> 0" by simp
    have cancel: "?P * (?Q / ?P) = ?Q"
      using P_nonzero by simp
    have half: "(1 / 2) * (?Q / ?P) = ?Q / (2 * ?P)"
    proof -
      have "(1 / 2) * (?Q / ?P) =
          ?Q * (inverse 2 * inverse ?P)"
        by (simp only: divide_inverse mult_1; simp only: mult_ac)
      also have "... = ?Q * inverse (2 * ?P)"
        by (simp only: inverse_mult_distrib)
      also have "... = ?Q / (2 * ?P)"
        by (simp only: divide_inverse)
      finally show ?thesis .
    qed
    have "(2 * ?P - 1 / 2) * (?Q / ?P) =
        (2 * ?P) * (?Q / ?P) - (1 / 2) * (?Q / ?P)"
      by (rule left_diff_distrib)
    also have "... = 2 * ?Q - ?Q / (2 * ?P)"
      using cancel half by (simp add: mult.assoc)
    also have "... = ?Q * (2 - 1 / (2 * ?P))"
    proof -
      have two: "2 * ?Q = ?Q * 2" by (rule mult.commute)
      have fraction: "?Q / (2 * ?P) = ?Q * (1 / (2 * ?P))"
        by simp
      show ?thesis
        using two fraction right_diff_distrib[of ?Q 2 "1 / (2 * ?P)"]
        by simp
    qed
    finally show ?thesis .
  qed
  have dynamic_expression:
    "(of_rat (format_nearest_overflow_threshold
        (runtime_format TYPE(('e, 'f) float))) :: real) =
      (2 * (2::real) ^ ?F - 1 / 2) *
        2 powr (real ?B - real ?F)"
    by (simp add: format_nearest_overflow_threshold_def format_emax_def
        IEEE.bias_def power_Suc of_rat_diff of_rat_divide of_rat_mult
        of_rat_power)
  have ieee_expression:
    "fp_threshold TYPE(('e, 'f) floatSingleNaN) =
      ((2::real) ^ ((2::nat) ^ ?E - 2) / 2 ^ ?B) *
        (2 - 1 / (2 * 2 ^ ?F))"
  proof -
    have emax_minus:
      "IEEE.emax TYPE(('e, 'f) float) - 1 =
        (2::nat) ^ ?E - 2"
      using E by (simp add: emax_eq power_Suc numeral_2_eq_2)
    have bias_eq:
      "IEEE.bias TYPE(('e, 'f) float) = ?B"
      by (simp add: IEEE.bias_def)
    have fraction_power:
      "(2::real) ^ Suc ?F = 2 * 2 ^ ?F"
      by (simp add: power_Suc mult.commute)
    show ?thesis
      unfolding fp_threshold_def threshold_def
      by (simp only: emax_minus bias_eq fraction_power)
  qed
  have ieee_simplified:
    "fp_threshold TYPE(('e, 'f) floatSingleNaN) =
      (2::real) ^ ?B * (2 - 1 / (2 * 2 ^ ?F))"
  proof -
    have "fp_threshold TYPE(('e, 'f) floatSingleNaN) =
        ((2::real) ^ ((2::nat) ^ ?E - 2) / 2 ^ ?B) *
          (2 - 1 / (2 * 2 ^ ?F))"
      by (rule ieee_expression)
    also have "... =
        (2::real) ^ ?B * (2 - 1 / (2 * 2 ^ ?F))"
      by (simp only: exponent_scale)
    finally show ?thesis .
  qed
  have "(of_rat (format_nearest_overflow_threshold
      (runtime_format TYPE(('e, 'f) float))) :: real) =
      (2 * (2::real) ^ ?F - 1 / 2) *
        (2 ^ ?B / 2 ^ ?F)"
    using dynamic_expression powr_scale by simp
  also have "... =
      (2::real) ^ ?B * (2 - 1 / (2 * 2 ^ ?F))"
    by (rule coefficient_scale)
  also have "... = fp_threshold TYPE(('e, 'f) floatSingleNaN)"
    using ieee_simplified by simp
  finally show ?thesis .
qed

lemma scaled_nearest_upper_half_rounds_up:
  fixes upper :: nat
  assumes denominator: "0 < d"
      and upper_pos: "0 < upper"
      and upper_even: "even upper"
      and lower_half:
        "(of_nat upper :: rat) - 1 / 2 \<le>
          (of_nat n / of_nat d) * rat_pow2 k"
      and below_upper:
        "(of_nat n / of_nat d) * rat_pow2 k < of_nat upper"
  shows
    "scaled_round_integer Fp_Round_Int.RNE negative n d k = upper"
    "scaled_round_integer Fp_Round_Int.RNA negative n d k = upper"
proof -
  let ?a = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q"
    by (rule scaled_denominator_pos[OF denominator])
  have qpos_rat: "0 < (of_nat ?q :: rat)" using qpos by simp
  have exact:
    "(of_nat ?a :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF denominator])
  have predecessor_cast:
    "(of_nat (upper - 1) :: rat) = of_nat upper - 1"
    using upper_pos by simp
  have predecessor_le:
    "(of_nat (upper - 1) :: rat) \<le>
      (of_nat ?a :: rat) / of_nat ?q"
    using lower_half exact predecessor_cast by linarith
  have predecessor_product_rat:
    "(of_nat (upper - 1) :: rat) * of_nat ?q \<le> of_nat ?a"
    using predecessor_le
    by (simp only: pos_le_divide_eq[OF qpos_rat])
  have predecessor_product:
    "?q * (upper - 1) \<le> ?a"
    using predecessor_product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_le_iff mult.commute)
  have upper_product_rat:
    "(of_nat ?a :: rat) < of_nat upper * of_nat ?q"
  proof -
    have ratio:
      "(of_nat ?a :: rat) / of_nat ?q < of_nat upper"
      using below_upper exact by simp
    show ?thesis
      using ratio by (simp only: pos_divide_less_eq[OF qpos_rat])
  qed
  have upper_product: "?a < ?q * upper"
    using upper_product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_less_iff mult.commute)
  have successor: "Suc (upper - 1) = upper"
    using upper_pos by simp
  have quotient: "?a div ?q = upper - 1"
    by (rule div_nat_eqI[OF predecessor_product])
      (use upper_product successor in simp)
  have decomposition_nat:
    "(upper - 1) * ?q + ?a mod ?q = ?a"
    using div_mult_mod_eq[of ?a ?q] quotient by simp
  have decomposition_rat:
    "(of_nat (upper - 1) :: rat) * of_nat ?q +
      of_nat (?a mod ?q) = of_nat ?a"
  proof -
    have casted:
      "(of_nat ((upper - 1) * ?q + ?a mod ?q) :: rat) = of_nat ?a"
      using decomposition_nat by simp
    show ?thesis using casted by simp
  qed
  have lower_product:
    "((of_nat upper :: rat) - 1 / 2) * of_nat ?q \<le> of_nat ?a"
  proof -
    have
      "((of_nat upper :: rat) - 1 / 2) * of_nat ?q \<le>
        ((of_nat n / of_nat d) * rat_pow2 k) * of_nat ?q"
      by (rule mult_right_mono[OF lower_half]) simp
    also have "... = of_nat ?a"
      using exact qpos_rat by (simp add: field_simps)
    finally show ?thesis .
  qed
  have half_remainder_rat:
    "(of_nat ?q :: rat) \<le> 2 * of_nat (?a mod ?q)"
  proof -
    have lower_expanded:
      "(of_nat upper :: rat) * of_nat ?q - of_nat ?q / 2 \<le>
        of_nat ?a"
      using lower_product by (simp add: algebra_simps)
    have decomposition_expanded:
      "(of_nat upper :: rat) * of_nat ?q - of_nat ?q +
          of_nat (?a mod ?q) = of_nat ?a"
      using decomposition_rat predecessor_cast
      by (simp add: algebra_simps)
    show ?thesis using lower_expanded decomposition_expanded by linarith
  qed
  have half_remainder:
    "?q \<le> 2 * (?a mod ?q)"
    using half_remainder_rat
    by (simp only: of_nat_mult[symmetric] of_nat_le_iff)
  have remainder_nonzero: "?a mod ?q \<noteq> 0"
    using qpos half_remainder by auto
  have predecessor_odd: "odd (upper - 1)"
    using upper_even upper_pos by simp
  show
    "scaled_round_integer Fp_Round_Int.RNE negative n d k = upper"
    unfolding scaled_round_integer_def round_integer_def
      round_quotient_def
    using quotient half_remainder remainder_nonzero predecessor_odd successor
    by auto
  show
    "scaled_round_integer Fp_Round_Int.RNA negative n d k = upper"
    unfolding scaled_round_integer_def round_integer_def
      round_quotient_def
    using quotient half_remainder remainder_nonzero successor
    by auto
qed

lemma scaled_directed_top_interval:
  fixes upper :: nat
  assumes denominator: "0 < d"
      and upper_pos: "0 < upper"
      and above_predecessor:
        "(of_nat upper :: rat) - 1 <
          (of_nat n / of_nat d) * rat_pow2 k"
      and below_upper:
        "(of_nat n / of_nat d) * rat_pow2 k < of_nat upper"
  shows
    "scaled_round_integer Fp_Round_Int.RTP False n d k = upper"
    "scaled_round_integer Fp_Round_Int.RTP True n d k = upper - 1"
    "scaled_round_integer Fp_Round_Int.RTN False n d k = upper - 1"
    "scaled_round_integer Fp_Round_Int.RTN True n d k = upper"
    "scaled_round_integer Fp_Round_Int.RTZ negative n d k = upper - 1"
proof -
  let ?a = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q"
    by (rule scaled_denominator_pos[OF denominator])
  have qpos_rat: "0 < (of_nat ?q :: rat)" using qpos by simp
  have exact:
    "(of_nat ?a :: rat) / of_nat ?q =
      (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF denominator])
  have predecessor_cast:
    "(of_nat (upper - 1) :: rat) = of_nat upper - 1"
    using upper_pos by simp
  have predecessor_less:
    "(of_nat (upper - 1) :: rat) <
      (of_nat ?a :: rat) / of_nat ?q"
    using above_predecessor exact predecessor_cast by simp
  have predecessor_product_rat:
    "(of_nat (upper - 1) :: rat) * of_nat ?q < of_nat ?a"
    using predecessor_less
    by (simp only: pos_less_divide_eq[OF qpos_rat])
  have predecessor_product:
    "?q * (upper - 1) < ?a"
    using predecessor_product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_less_iff mult.commute)
  have upper_ratio:
    "(of_nat ?a :: rat) / of_nat ?q < of_nat upper"
    using below_upper exact by simp
  have upper_product_rat:
    "(of_nat ?a :: rat) < of_nat upper * of_nat ?q"
    using upper_ratio
    by (simp only: pos_divide_less_eq[OF qpos_rat])
  have upper_product: "?a < ?q * upper"
    using upper_product_rat
    by (simp only: of_nat_mult[symmetric] of_nat_less_iff mult.commute)
  have successor: "Suc (upper - 1) = upper"
    using upper_pos by simp
  have quotient: "?a div ?q = upper - 1"
    by (rule div_nat_eqI)
      (use predecessor_product upper_product successor in auto)
  have remainder_nonzero: "?a mod ?q \<noteq> 0"
  proof
    assume zero: "?a mod ?q = 0"
    have decomposition: "(?a div ?q) * ?q + ?a mod ?q = ?a"
      by (rule div_mult_mod_eq)
    show False
      using predecessor_product decomposition quotient zero
      by (simp add: mult.commute)
  qed
  show
    "scaled_round_integer Fp_Round_Int.RTP False n d k = upper"
    unfolding scaled_round_integer_def round_integer_RTP_positive
      ceil_quotient_def
    using quotient remainder_nonzero successor by simp
  show
    "scaled_round_integer Fp_Round_Int.RTP True n d k = upper - 1"
    unfolding scaled_round_integer_def
    using quotient by simp
  show
    "scaled_round_integer Fp_Round_Int.RTN False n d k = upper - 1"
    unfolding scaled_round_integer_def
    using quotient by simp
  show
    "scaled_round_integer Fp_Round_Int.RTN True n d k = upper"
    unfolding scaled_round_integer_def round_integer_RTN_negative
      ceil_quotient_def
    using quotient remainder_nonzero successor by simp
  show
    "scaled_round_integer Fp_Round_Int.RTZ negative n d k = upper - 1"
    unfolding scaled_round_integer_def
    using quotient by simp
qed

lemma apply_significand_carry_exponent:
  shows "\<not> core_is_subnormal (apply_significand_carry f m e)"
    and "e \<le> core_exponent (apply_significand_carry f m e)"
  by (cases "m = 2 ^ precision_bits f")
    (simp_all add: apply_significand_carry_def)

lemma round_rational_core_at_above_emax:
  assumes normal: "format_emin f \<le> e"
      and above: "format_emax f < e"
  shows
    "\<not> core_is_subnormal
      (round_rational_core_at f rm negative n d e)"
    "format_emax f < core_exponent
      (round_rational_core_at f rm negative n d e)"
proof -
  let ?m = "scaled_round_integer rm negative n d
    (int (fraction_bits f) - e)"
  have core:
    "round_rational_core_at f rm negative n d e =
      apply_significand_carry f ?m e"
    by (rule round_rational_core_at_normal[OF normal])
  show "\<not> core_is_subnormal
      (round_rational_core_at f rm negative n d e)"
    using core apply_significand_carry_exponent(1)[of f ?m e] by simp
  have "e \<le> core_exponent (round_rational_core_at f rm negative n d e)"
    using core apply_significand_carry_exponent(2)[of e f ?m] by simp
  with above show "format_emax f < core_exponent
      (round_rational_core_at f rm negative n d e)"
    by linarith
qed

lemma round_rational_to_format_bits_above_emax:
  assumes valid: "valid_format f"
      and logarithm: "floor_log2_rel n d e"
      and above: "format_emax f < e"
  shows "round_rational_to_format_bits f rm negative n d =
    overflow_bits f rm negative"
proof -
  have normal: "format_emin f \<le> e"
    using valid_format_emin_le_emax[OF valid] above by linarith
  have not_subnormal:
    "\<not> core_is_subnormal
      (round_rational_core_at f rm negative n d e)"
    by (rule round_rational_core_at_above_emax(1)[OF normal above])
  have core_above:
    "format_emax f < core_exponent
      (round_rational_core_at f rm negative n d e)"
    by (rule round_rational_core_at_above_emax(2)[OF normal above])
  have chosen: "floor_log2_spec n d = e"
    by (rule floor_log2_spec_eq[OF logarithm])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    using chosen not_subnormal core_above by simp
qed

lemma round_rational_to_format_bits_emax_carry:
  assumes valid: "valid_format f"
      and logarithm: "floor_log2_rel n d (format_emax f)"
      and carry:
        "scaled_round_integer rm negative n d
          (int (fraction_bits f) - format_emax f) =
        2 ^ precision_bits f"
  shows "round_rational_to_format_bits f rm negative n d =
    overflow_bits f rm negative"
proof -
  have normal: "format_emin f \<le> format_emax f"
    by (rule valid_format_emin_le_emax[OF valid])
  have precision_pos: "0 < precision_bits f"
    using valid by (simp add: valid_format_def)
  have core:
    "round_rational_core_at f rm negative n d (format_emax f) =
      \<lparr>core_significand = 2 ^ fraction_bits f,
        core_exponent = format_emax f + 1,
        core_is_subnormal = False\<rparr>"
  proof -
    have normal_core:
      "round_rational_core_at f rm negative n d (format_emax f) =
        apply_significand_carry f
          (scaled_round_integer rm negative n d
            (int (fraction_bits f) - format_emax f))
          (format_emax f)"
      by (rule round_rational_core_at_normal[OF normal])
    show ?thesis
      using normal_core carry_at_precision[OF precision_pos,
          of "format_emax f"] carry
      by simp
  qed
  have chosen: "floor_log2_spec n d = format_emax f"
    by (rule floor_log2_spec_eq[OF logarithm])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    using chosen core by simp
qed

lemma round_rational_to_format_bits_emax_no_carry_maximum:
  assumes valid: "valid_format f"
      and logarithm: "floor_log2_rel n d (format_emax f)"
      and no_carry:
        "scaled_round_integer rm negative n d
          (int (fraction_bits f) - format_emax f) =
        2 ^ precision_bits f - 1"
  shows "round_rational_to_format_bits f rm negative n d =
    maximum_finite_bits f negative"
proof -
  have normal: "format_emin f \<le> format_emax f"
    by (rule valid_format_emin_le_emax[OF valid])
  have different:
    "(2::nat) ^ precision_bits f - 1 \<noteq> 2 ^ precision_bits f"
  proof (rule less_imp_neq)
    show "(2::nat) ^ precision_bits f - 1 < 2 ^ precision_bits f"
      by simp
  qed
  have core:
    "round_rational_core_at f rm negative n d (format_emax f) =
      \<lparr>core_significand = 2 ^ precision_bits f - 1,
        core_exponent = format_emax f,
        core_is_subnormal = False\<rparr>"
  proof -
    have normal_core:
      "round_rational_core_at f rm negative n d (format_emax f) =
        apply_significand_carry f
          (scaled_round_integer rm negative n d
            (int (fraction_bits f) - format_emax f))
          (format_emax f)"
      by (rule round_rational_core_at_normal[OF normal])
    have unchanged:
      "apply_significand_carry f (2 ^ precision_bits f - 1)
          (format_emax f) =
        \<lparr>core_significand = 2 ^ precision_bits f - 1,
          core_exponent = format_emax f,
          core_is_subnormal = False\<rparr>"
      by (rule no_significand_carry[OF different])
    show ?thesis
      using normal_core no_carry unchanged
      by simp
  qed
  have chosen: "floor_log2_spec n d = format_emax f"
    by (rule floor_log2_spec_eq[OF logarithm])
  have maximum:
    "normal_result_bits f negative (2 ^ precision_bits f - 1)
        (format_emax f) = maximum_finite_bits f negative"
    by (rule normal_result_bits_at_maximum[OF valid])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
      encode_rounded_core_def
    using chosen core maximum by simp
qed

theorem round_rational_to_format_bits_directed_above_maximum:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and above:
        "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows
    "round_rational_to_format_bits f Fp_Round_Int.RTP negative n d =
      (if negative then maximum_finite_bits f negative
       else infinity_bits f negative)"
    "round_rational_to_format_bits f Fp_Round_Int.RTN negative n d =
      (if negative then infinity_bits f negative
       else maximum_finite_bits f negative)"
    "round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
      maximum_finite_bits f negative"
proof -
  let ?e = "floor_log2_spec n d"
  have logarithm: "floor_log2_rel n d ?e"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  have binade_lower:
    "rat_pow2 (format_emax f) \<le> exact_magnitude n d"
    using format_maximum_at_least_binade[OF valid] above by linarith
  have exponent_lower: "format_emax f \<le> ?e"
  proof (rule ccontr)
    assume "\<not> format_emax f \<le> ?e"
    then have next_le: "?e + 1 \<le> format_emax f" by linarith
    have input_upper: "exact_magnitude n d < rat_pow2 (?e + 1)"
      using logarithm
      by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
    have power_upper:
      "rat_pow2 (?e + 1) \<le> rat_pow2 (format_emax f)"
      by (rule rat_pow2_increasing[OF next_le])
    show False using binade_lower input_upper power_upper by linarith
  qed
  have all_results:
    "round_rational_to_format_bits f Fp_Round_Int.RTP negative n d =
        (if negative then maximum_finite_bits f negative
         else infinity_bits f negative) \<and>
     round_rational_to_format_bits f Fp_Round_Int.RTN negative n d =
        (if negative then infinity_bits f negative
         else maximum_finite_bits f negative) \<and>
     round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
        maximum_finite_bits f negative"
  proof (cases "format_emax f < ?e")
    case True
    have rtp:
      "round_rational_to_format_bits f Fp_Round_Int.RTP negative n d =
        overflow_bits f Fp_Round_Int.RTP negative"
      by (rule round_rational_to_format_bits_above_emax[
            OF valid logarithm True])
    have rtn:
      "round_rational_to_format_bits f Fp_Round_Int.RTN negative n d =
        overflow_bits f Fp_Round_Int.RTN negative"
      by (rule round_rational_to_format_bits_above_emax[
            OF valid logarithm True])
    have rtz:
      "round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
        overflow_bits f Fp_Round_Int.RTZ negative"
      by (rule round_rational_to_format_bits_above_emax[
            OF valid logarithm True])
    show ?thesis using rtp rtn rtz by (cases negative) simp_all
  next
    case False
    with exponent_lower have exponent: "?e = format_emax f" by simp
    have rel_emax: "floor_log2_rel n d (format_emax f)"
      using logarithm exponent by simp
    have scaled_lower:
      "(of_nat (2 ^ precision_bits f) :: rat) - 1 <
        (of_nat n / of_nat d) *
          rat_pow2 (int (fraction_bits f) - format_emax f)"
    proof -
      have multiplied:
        "format_maximum_finite_magnitude f *
            rat_pow2 (int (fraction_bits f) - format_emax f) <
          exact_magnitude n d *
            rat_pow2 (int (fraction_bits f) - format_emax f)"
        by (rule mult_strict_right_mono[OF above rat_pow2_pos])
      have cancel:
        "format_maximum_finite_magnitude f *
            rat_pow2 (int (fraction_bits f) - format_emax f) =
          (of_nat (2 ^ precision_bits f) :: rat) - 1"
      proof -
        have power_cancel:
          "rat_pow2 (format_emax f - int (fraction_bits f)) *
              rat_pow2 (int (fraction_bits f) - format_emax f) = 1"
          by (simp only: rat_pow2_add[symmetric]; simp add: rat_pow2_def)
        show ?thesis
          unfolding format_maximum_finite_magnitude_def
          by (simp only: mult.assoc power_cancel; simp)
      qed
      show ?thesis
        using multiplied cancel by (simp add: exact_magnitude_def)
    qed
    have scaled_upper:
      "(of_nat n / of_nat d) *
          rat_pow2 (int (fraction_bits f) - format_emax f) <
        (of_nat (2 ^ precision_bits f) :: rat)"
      using floor_log2_normal_scaled_upper[OF rel_emax, of f]
        valid_format_precision_as_fraction[OF valid]
      by (simp add: exact_magnitude_def)
    have precision_pos: "0 < (2::nat) ^ precision_bits f" by simp
    note directed = scaled_directed_top_interval[
      OF denominator precision_pos scaled_lower scaled_upper]
    have rtp_outward:
      "round_rational_to_format_bits f Fp_Round_Int.RTP False n d =
        infinity_bits f False"
      using round_rational_to_format_bits_emax_carry[
          OF valid rel_emax directed(1)]
      by simp
    have rtp_inward:
      "round_rational_to_format_bits f Fp_Round_Int.RTP True n d =
        maximum_finite_bits f True"
      by (rule round_rational_to_format_bits_emax_no_carry_maximum[
            OF valid rel_emax directed(2)])
    have rtn_inward:
      "round_rational_to_format_bits f Fp_Round_Int.RTN False n d =
        maximum_finite_bits f False"
      by (rule round_rational_to_format_bits_emax_no_carry_maximum[
            OF valid rel_emax directed(3)])
    have rtn_outward:
      "round_rational_to_format_bits f Fp_Round_Int.RTN True n d =
        infinity_bits f True"
      using round_rational_to_format_bits_emax_carry[
          OF valid rel_emax directed(4)]
      by simp
    have rtz_inward:
      "round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
        maximum_finite_bits f negative"
      by (rule round_rational_to_format_bits_emax_no_carry_maximum[
            OF valid rel_emax directed(5)])
    show ?thesis
      using rtp_outward rtp_inward rtn_inward rtn_outward rtz_inward
      by (cases negative) simp_all
  qed
  show
    "round_rational_to_format_bits f Fp_Round_Int.RTP negative n d =
      (if negative then maximum_finite_bits f negative
       else infinity_bits f negative)"
    using all_results by blast
  show
    "round_rational_to_format_bits f Fp_Round_Int.RTN negative n d =
      (if negative then infinity_bits f negative
       else maximum_finite_bits f negative)"
    using all_results by blast
  show
    "round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
      maximum_finite_bits f negative"
    using all_results by blast
qed

corollary round_rational_to_format_bits_RTP_positive_above_maximum:
  assumes "valid_format f" "0 < n" "0 < d"
      "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows "round_rational_to_format_bits f Fp_Round_Int.RTP False n d =
    infinity_bits f False"
  using round_rational_to_format_bits_directed_above_maximum(1)[OF assms]
  by simp

corollary round_rational_to_format_bits_RTP_negative_above_maximum:
  assumes "valid_format f" "0 < n" "0 < d"
      "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows "round_rational_to_format_bits f Fp_Round_Int.RTP True n d =
    maximum_finite_bits f True"
  using round_rational_to_format_bits_directed_above_maximum(1)[OF assms]
  by simp

corollary round_rational_to_format_bits_RTN_positive_above_maximum:
  assumes "valid_format f" "0 < n" "0 < d"
      "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows "round_rational_to_format_bits f Fp_Round_Int.RTN False n d =
    maximum_finite_bits f False"
  using round_rational_to_format_bits_directed_above_maximum(2)[OF assms]
  by simp

corollary round_rational_to_format_bits_RTN_negative_above_maximum:
  assumes "valid_format f" "0 < n" "0 < d"
      "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows "round_rational_to_format_bits f Fp_Round_Int.RTN True n d =
    infinity_bits f True"
  using round_rational_to_format_bits_directed_above_maximum(2)[OF assms]
  by simp

corollary round_rational_to_format_bits_RTZ_above_maximum:
  assumes "valid_format f" "0 < n" "0 < d"
      "format_maximum_finite_magnitude f < exact_magnitude n d"
  shows "round_rational_to_format_bits f Fp_Round_Int.RTZ negative n d =
    maximum_finite_bits f negative"
  by (rule round_rational_to_format_bits_directed_above_maximum(3)[OF assms])

theorem round_rational_to_format_bits_nearest_overflow:
  fixes rm :: fp_round_mode
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and threshold:
        "format_nearest_overflow_threshold f \<le> exact_magnitude n d"
  shows "round_rational_to_format_bits f rm negative n d =
    infinity_bits f negative"
proof -
  let ?e = "floor_log2_spec n d"
  have logarithm: "floor_log2_rel n d ?e"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  have binade_lower:
    "rat_pow2 (format_emax f) \<le> exact_magnitude n d"
    using format_threshold_at_least_binade[OF valid] threshold by linarith
  have exponent_lower: "format_emax f \<le> ?e"
  proof (rule ccontr)
    assume "\<not> format_emax f \<le> ?e"
    then have next_le: "?e + 1 \<le> format_emax f" by linarith
    have input_upper: "exact_magnitude n d < rat_pow2 (?e + 1)"
      using logarithm by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
    have power_upper:
      "rat_pow2 (?e + 1) \<le> rat_pow2 (format_emax f)"
      by (rule rat_pow2_increasing[OF next_le])
    show False using binade_lower input_upper power_upper by linarith
  qed
  show ?thesis
  proof (cases "format_emax f < ?e")
    case True
    have overflow:
      "round_rational_to_format_bits f rm negative n d =
        overflow_bits f rm negative"
      by (rule round_rational_to_format_bits_above_emax[
            OF valid logarithm True])
    show ?thesis
      using overflow nearest by (elim disjE; simp)
  next
    case False
    with exponent_lower have exponent: "?e = format_emax f" by simp
    have scaled_lower:
      "(of_nat (2 ^ precision_bits f) :: rat) - 1 / 2 \<le>
        (of_nat n / of_nat d) *
          rat_pow2 (int (fraction_bits f) - format_emax f)"
    proof -
      have multiplied:
        "format_nearest_overflow_threshold f *
            rat_pow2 (int (fraction_bits f) - format_emax f) \<le>
          exact_magnitude n d *
            rat_pow2 (int (fraction_bits f) - format_emax f)"
        by (rule mult_right_mono[OF threshold rat_pow2_nonnegative])
      have cancel:
        "format_nearest_overflow_threshold f *
            rat_pow2 (int (fraction_bits f) - format_emax f) =
          (of_nat (2 ^ precision_bits f) :: rat) - 1 / 2"
      proof -
        have power_cancel:
          "rat_pow2 (format_emax f - int (fraction_bits f)) *
              rat_pow2 (int (fraction_bits f) - format_emax f) = 1"
          by (simp only: rat_pow2_add[symmetric]; simp add: rat_pow2_def)
        show ?thesis
          unfolding format_nearest_overflow_threshold_def
          by (simp only: mult.assoc power_cancel; simp)
      qed
      show ?thesis
        using multiplied cancel by (simp add: exact_magnitude_def)
    qed
    have rel_emax:
      "floor_log2_rel n d (format_emax f)"
      using logarithm exponent by simp
    have scaled_upper:
      "(of_nat n / of_nat d) *
          rat_pow2 (int (fraction_bits f) - format_emax f) <
        (of_nat (2 ^ precision_bits f) :: rat)"
      using floor_log2_normal_scaled_upper[OF rel_emax, of f]
        valid_format_precision_as_fraction[OF valid]
      by (simp add: exact_magnitude_def)
    have precision_pos: "0 < (2::nat) ^ precision_bits f" by simp
    have precision_even: "even (2 ^ precision_bits f)"
      using valid by (simp add: valid_format_def)
    have carries_RNE:
      "scaled_round_integer Fp_Round_Int.RNE negative n d
          (int (fraction_bits f) - format_emax f) =
        2 ^ precision_bits f"
      by (rule scaled_nearest_upper_half_rounds_up(1)[
            OF denominator precision_pos precision_even scaled_lower
              scaled_upper])
    have carries_RNA:
      "scaled_round_integer Fp_Round_Int.RNA negative n d
          (int (fraction_bits f) - format_emax f) =
        2 ^ precision_bits f"
      by (rule scaled_nearest_upper_half_rounds_up(2)[
            OF denominator precision_pos precision_even scaled_lower
              scaled_upper])
    have overflow_RNE:
      "round_rational_to_format_bits f Fp_Round_Int.RNE negative n d =
        overflow_bits f Fp_Round_Int.RNE negative"
      by (rule round_rational_to_format_bits_emax_carry[
            OF valid rel_emax carries_RNE])
    have overflow_RNA:
      "round_rational_to_format_bits f Fp_Round_Int.RNA negative n d =
        overflow_bits f Fp_Round_Int.RNA negative"
      by (rule round_rational_to_format_bits_emax_carry[
            OF valid rel_emax carries_RNA])
    show ?thesis
      using nearest overflow_RNE overflow_RNA by auto
  qed
qed

lemma dynamic_overflow_bits_policy:
  fixes rm :: fp_round_mode
  shows "overflow_bits f rm negative =
    (case rm of
       Fp_Round_Int.RNE \<Rightarrow> infinity_bits f negative
     | Fp_Round_Int.RNA \<Rightarrow> infinity_bits f negative
     | Fp_Round_Int.RTZ \<Rightarrow> maximum_finite_bits f negative
     | Fp_Round_Int.RTP \<Rightarrow> if negative then maximum_finite_bits f True
              else infinity_bits f False
     | Fp_Round_Int.RTN \<Rightarrow> if negative then infinity_bits f True
              else maximum_finite_bits f False)"
  by (cases rm; cases negative) simp_all

end

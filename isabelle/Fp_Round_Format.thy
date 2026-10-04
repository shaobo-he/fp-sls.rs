(* SPDX-License-Identifier: MIT *)

section \<open>Exact rational rounding into a run-time binary format\<close>

theory Fp_Round_Format
  imports Fp_Rational_Scale Fp_Format
begin

text \<open>
  This theory mirrors the structure of \<open>FloatingPoint::round_rational_to_format\<close>.
  It keeps the mathematical scaling step separate from the bit-layout step, so
  that carry, subnormal promotion, signed underflow, and overflow can be checked
  without referring to MPFR.
\<close>

definition exact_magnitude :: "nat \<Rightarrow> nat \<Rightarrow> rat" where
  "exact_magnitude n d = of_nat n / of_nat d"

lemma rat_pow2_eq_pow2_rat:
  "rat_pow2 k = pow2_rat k"
proof (cases "0 \<le> k")
  case True
  have rat:
    "rat_pow2 k = (2::rat) ^ nat k"
    unfolding rat_pow2_def using True by (rule power_int_nonneg_exp)
  have manual:
    "pow2_rat k = (2::rat) ^ nat k"
    using True by (simp add: pow2_rat_def)
  from rat manual show ?thesis by simp
next
  case False
  have rat:
    "rat_pow2 k = (inverse (2::rat)) ^ nat (- k)"
    using False by (simp add: rat_pow2_def power_int_def)
  also have "... = inverse ((2::rat) ^ nat (- k))"
    by (rule power_inverse)
  also have "... = pow2_rat k"
    using False by (simp add: pow2_rat_def)
  finally show ?thesis .
qed

definition floor_log2_rel :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "floor_log2_rel n d e \<longleftrightarrow>
     pow2_rat e \<le> exact_magnitude n d \<and>
     exact_magnitude n d < pow2_rat (e + 1)"

definition floor_log2_spec :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "floor_log2_spec n d = (SOME e. floor_log2_rel n d e)"

lemma floor_log2_spec_correct:
  assumes "\<exists>e. floor_log2_rel n d e"
  shows "floor_log2_rel n d (floor_log2_spec n d)"
  unfolding floor_log2_spec_def using assms by (rule someI_ex)

lemma floor_log2_rel_exists:
  assumes numerator: "0 < n"
      and denominator: "0 < d"
  shows "\<exists>e. floor_log2_rel n d e"
proof -
  have magnitude_pos: "0 < exact_magnitude n d"
    using numerator denominator by (simp add: exact_magnitude_def)
  let ?x = "(of_rat (exact_magnitude n d) :: real)"
  let ?e = "\<lfloor>log (2::real) ?x\<rfloor>"
  have x_pos: "0 < ?x" using magnitude_pos by simp
  have logarithm_bounds:
    "(2::real) powr (real_of_int ?e) \<le> ?x \<and>
     ?x < (2::real) powr (real_of_int (?e + 1))"
  proof -
    have iff:
      "\<lfloor>log (2::real) ?x\<rfloor> = ?e \<longleftrightarrow>
       (2::real) powr (real_of_int ?e) \<le> ?x \<and>
       ?x < (2::real) powr (real_of_int (?e + 1))"
      by (rule floor_log_eq_powr_iff) (simp_all add: x_pos magnitude_pos)
    from iff show ?thesis by simp
  qed
  have cast_bounds:
    "(of_rat (rat_pow2 ?e) :: real) \<le>
       of_rat (exact_magnitude n d) \<and>
     (of_rat (exact_magnitude n d) :: real) <
       of_rat (rat_pow2 (?e + 1))"
    using logarithm_bounds by simp
  have rational_bounds:
    "rat_pow2 ?e \<le> exact_magnitude n d \<and>
     exact_magnitude n d < rat_pow2 (?e + 1)"
    using cast_bounds by (simp only: of_rat_less_eq of_rat_less)
  show ?thesis
  proof (rule exI[of _ ?e])
    show "floor_log2_rel n d ?e"
      using rational_bounds
      by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  qed
qed

lemma floor_log2_spec_correct_positive:
  assumes "0 < n" "0 < d"
  shows "floor_log2_rel n d (floor_log2_spec n d)"
  by (rule floor_log2_spec_correct[OF floor_log2_rel_exists[OF assms]])

lemma floor_log2_rel_unique:
  assumes first: "floor_log2_rel n d e"
      and second: "floor_log2_rel n d e'"
  shows "e = e'"
proof -
  have first_lower: "rat_pow2 e \<le> exact_magnitude n d"
    and first_upper: "exact_magnitude n d < rat_pow2 (e + 1)"
    using first
    by (simp_all add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  have second_lower: "rat_pow2 e' \<le> exact_magnitude n d"
    and second_upper: "exact_magnitude n d < rat_pow2 (e' + 1)"
    using second
    by (simp_all add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  have not_less: "\<not> e < e'"
  proof
    assume "e < e'"
    then have "e + 1 \<le> e'" by linarith
    then have "rat_pow2 (e + 1) \<le> rat_pow2 e'"
      by (rule rat_pow2_increasing)
    with first_upper second_lower show False by linarith
  qed
  have not_greater: "\<not> e' < e"
  proof
    assume "e' < e"
    then have "e' + 1 \<le> e" by linarith
    then have "rat_pow2 (e' + 1) \<le> rat_pow2 e"
      by (rule rat_pow2_increasing)
    with second_upper first_lower show False by linarith
  qed
  from not_less not_greater show ?thesis by linarith
qed

lemma floor_log2_spec_eq:
  assumes "floor_log2_rel n d e"
  shows "floor_log2_spec n d = e"
proof -
  have exists: "\<exists>k. floor_log2_rel n d k" using assms by blast
  have chosen: "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct[OF exists])
  show ?thesis by (rule floor_log2_rel_unique[OF chosen assms])
qed

record rounded_core =
  core_significand :: nat
  core_exponent :: int
  core_is_subnormal :: bool

definition apply_significand_carry ::
    "binary_format \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> rounded_core" where
  "apply_significand_carry f m e =
     (if m = 2 ^ precision_bits f then
        \<lparr>core_significand = m div 2, core_exponent = e + 1,
          core_is_subnormal = False\<rparr>
      else
        \<lparr>core_significand = m, core_exponent = e,
          core_is_subnormal = False\<rparr>)"

lemma carry_at_precision:
  assumes "0 < precision_bits f"
  shows "apply_significand_carry f (2 ^ precision_bits f) e =
    \<lparr>core_significand = 2 ^ fraction_bits f, core_exponent = e + 1,
      core_is_subnormal = False\<rparr>"
  using assms
  by (cases "precision_bits f")
    (simp_all add: apply_significand_carry_def fraction_bits_def power_Suc)

lemma no_significand_carry:
  assumes "m \<noteq> 2 ^ precision_bits f"
  shows "apply_significand_carry f m e =
    \<lparr>core_significand = m, core_exponent = e,
      core_is_subnormal = False\<rparr>"
  using assms by (simp add: apply_significand_carry_def)

definition round_rational_core_at ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> bool \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> rounded_core" where
  "round_rational_core_at f rm negative n d e =
     (if format_emin f \<le> e then
        apply_significand_carry f
          (scaled_round_integer rm negative n d
            (int (fraction_bits f) - e)) e
      else
        \<lparr>core_significand = scaled_round_integer rm negative n d
            (int (fraction_bits f) - format_emin f),
          core_exponent = format_emin f,
          core_is_subnormal = True\<rparr>)"

definition round_rational_core ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> bool \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> rounded_core" where
  "round_rational_core f rm negative n d =
    round_rational_core_at f rm negative n d (floor_log2_spec n d)"

lemma round_rational_core_at_normal:
  assumes "format_emin f \<le> e"
  shows "round_rational_core_at f rm negative n d e =
    apply_significand_carry f
      (scaled_round_integer rm negative n d
        (int (fraction_bits f) - e)) e"
  using assms by (simp add: round_rational_core_at_def)

lemma round_rational_core_at_subnormal:
  assumes "e < format_emin f"
  shows "round_rational_core_at f rm negative n d e =
    \<lparr>core_significand = scaled_round_integer rm negative n d
        (int (fraction_bits f) - format_emin f),
      core_exponent = format_emin f,
      core_is_subnormal = True\<rparr>"
  using assms by (simp add: round_rational_core_at_def)

lemma normal_scale_is_exact:
  assumes "0 < d"
  shows
    "(of_nat (scaled_numerator n d (int (fraction_bits f) - e)) :: rat) /
       of_nat (scaled_denominator n d (int (fraction_bits f) - e)) =
     exact_magnitude n d * rat_pow2 (int (fraction_bits f) - e)"
  using scale_ratio_exact[OF assms, of n "int (fraction_bits f) - e"]
  by (simp add: exact_magnitude_def)

lemma subnormal_scale_is_exact:
  assumes "0 < d"
  shows
    "(of_nat (scaled_numerator n d
        (int (fraction_bits f) - format_emin f)) :: rat) /
       of_nat (scaled_denominator n d
        (int (fraction_bits f) - format_emin f)) =
     exact_magnitude n d *
       rat_pow2 (int (fraction_bits f) - format_emin f)"
  using scale_ratio_exact[OF assms, of n
      "int (fraction_bits f) - format_emin f"]
  by (simp add: exact_magnitude_def)

section \<open>Scaled binade bounds\<close>

lemma floor_log2_normal_scaled_lower:
  assumes rel: "floor_log2_rel n d e"
  shows "(of_nat (2 ^ fraction_bits f) :: rat) \<le>
    exact_magnitude n d * rat_pow2 (int (fraction_bits f) - e)"
proof -
  have lower: "rat_pow2 e \<le> exact_magnitude n d"
    using rel
    by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  have scaled:
    "rat_pow2 e * rat_pow2 (int (fraction_bits f) - e) \<le>
     exact_magnitude n d * rat_pow2 (int (fraction_bits f) - e)"
    by (rule mult_right_mono[OF lower rat_pow2_nonnegative])
  show ?thesis
    using scaled
    by (simp add: rat_pow2_scale_cancel)
qed

lemma floor_log2_normal_scaled_upper:
  assumes rel: "floor_log2_rel n d e"
  shows "exact_magnitude n d * rat_pow2 (int (fraction_bits f) - e) <
    (of_nat (2 ^ Suc (fraction_bits f)) :: rat)"
proof -
  have upper: "exact_magnitude n d < rat_pow2 (e + 1)"
    using rel
    by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  have scaled:
    "exact_magnitude n d * rat_pow2 (int (fraction_bits f) - e) <
     rat_pow2 (e + 1) * rat_pow2 (int (fraction_bits f) - e)"
    by (rule mult_strict_right_mono[OF upper rat_pow2_pos])
  show ?thesis
    using scaled
    by (simp add: rat_pow2_succ_scale_cancel)
qed

lemma floor_log2_subnormal_scaled_upper:
  assumes rel: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows "exact_magnitude n d *
      rat_pow2 (int (fraction_bits f) - format_emin f) <
    (of_nat (2 ^ fraction_bits f) :: rat)"
proof -
  have upper: "exact_magnitude n d < rat_pow2 (e + 1)"
    using rel
    by (simp add: floor_log2_rel_def rat_pow2_eq_pow2_rat)
  have exponent_le: "e + 1 \<le> format_emin f"
    using subnormal by linarith
  have power_le: "rat_pow2 (e + 1) \<le> rat_pow2 (format_emin f)"
    by (rule rat_pow2_increasing[OF exponent_le])
  have magnitude_lt: "exact_magnitude n d < rat_pow2 (format_emin f)"
    using upper power_le by (rule order_less_le_trans)
  have scaled:
    "exact_magnitude n d *
        rat_pow2 (int (fraction_bits f) - format_emin f) <
     rat_pow2 (format_emin f) *
        rat_pow2 (int (fraction_bits f) - format_emin f)"
    by (rule mult_strict_right_mono[OF magnitude_lt rat_pow2_pos])
  show ?thesis
    using scaled
    by (simp add: rat_pow2_scale_cancel)
qed

lemma normal_rounded_significand_bounds:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
  shows "2 ^ fraction_bits f \<le>
      scaled_round_integer rm negative n d
        (int (fraction_bits f) - e) \<and>
    scaled_round_integer rm negative n d
        (int (fraction_bits f) - e) \<le> 2 ^ precision_bits f"
proof -
  have lower:
    "(of_nat (2 ^ fraction_bits f) :: rat) \<le>
      (of_nat n / of_nat d) * rat_pow2 (int (fraction_bits f) - e)"
    using floor_log2_normal_scaled_lower[OF rel, of f]
    by (simp add: exact_magnitude_def)
  have upper:
    "(of_nat n / of_nat d) * rat_pow2 (int (fraction_bits f) - e) <
      (of_nat (2 ^ precision_bits f) :: rat)"
    using floor_log2_normal_scaled_upper[OF rel, of f]
      valid_format_precision_as_fraction[OF valid]
    by (simp add: exact_magnitude_def)
  show ?thesis
    by (rule scaled_round_integer_between_from_ratio[OF denominator lower upper])
qed

lemma subnormal_rounded_significand_upper:
  assumes denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows "scaled_round_integer rm negative n d
      (int (fraction_bits f) - format_emin f) \<le>
    2 ^ fraction_bits f"
proof -
  have upper:
    "(of_nat n / of_nat d) *
        rat_pow2 (int (fraction_bits f) - format_emin f) <
      (of_nat (2 ^ fraction_bits f) :: rat)"
    using floor_log2_subnormal_scaled_upper[OF rel subnormal]
    by (simp add: exact_magnitude_def)
  show ?thesis
    by (rule scaled_round_integer_upper_from_ratio[OF denominator upper])
qed

lemma normal_RNE_scaled_error_half:
  assumes "0 < d"
  shows
    "2 * scaled_error
       (scaled_numerator n d (int (fraction_bits f) - e))
       (scaled_denominator n d (int (fraction_bits f) - e))
       (scaled_round_integer RNE negative n d
         (int (fraction_bits f) - e))
     \<le> scaled_denominator n d (int (fraction_bits f) - e)"
  by (rule scaled_RNE_error_half[OF assms])

lemma subnormal_RNE_scaled_error_half:
  assumes "0 < d"
  shows
    "2 * scaled_error
       (scaled_numerator n d
         (int (fraction_bits f) - format_emin f))
       (scaled_denominator n d
         (int (fraction_bits f) - format_emin f))
       (scaled_round_integer RNE negative n d
         (int (fraction_bits f) - format_emin f))
     \<le> scaled_denominator n d
       (int (fraction_bits f) - format_emin f)"
  by (rule scaled_RNE_error_half[OF assms])

lemma subnormal_RNA_scaled_error_half:
  assumes "0 < d"
  shows
    "2 * scaled_error
       (scaled_numerator n d
         (int (fraction_bits f) - format_emin f))
       (scaled_denominator n d
         (int (fraction_bits f) - format_emin f))
       (scaled_round_integer RNA negative n d
         (int (fraction_bits f) - format_emin f))
     \<le> scaled_denominator n d
       (int (fraction_bits f) - format_emin f)"
  by (rule scaled_RNA_error_half[OF assms])

section \<open>Bit-pattern constructors\<close>

definition signed_zero_bits :: "bool \<Rightarrow> fp_bits" where
  "signed_zero_bits negative =
    \<lparr>negative_bit = negative, exponent_field = 0, fraction_field = 0\<rparr>"

definition infinity_bits :: "binary_format \<Rightarrow> bool \<Rightarrow> fp_bits" where
  "infinity_bits f negative =
    \<lparr>negative_bit = negative, exponent_field = exponent_all_ones f,
      fraction_field = 0\<rparr>"

definition maximum_finite_bits :: "binary_format \<Rightarrow> bool \<Rightarrow> fp_bits" where
  "maximum_finite_bits f negative =
    \<lparr>negative_bit = negative, exponent_field = exponent_all_ones f - 1,
      fraction_field = 2 ^ fraction_bits f - 1\<rparr>"

fun overflow_bits ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> bool \<Rightarrow> fp_bits" where
  "overflow_bits f RNE negative = infinity_bits f negative"
| "overflow_bits f RNA negative = infinity_bits f negative"
| "overflow_bits f RTZ negative = maximum_finite_bits f negative"
| "overflow_bits f RTP False = infinity_bits f False"
| "overflow_bits f RTP True = maximum_finite_bits f True"
| "overflow_bits f RTN False = maximum_finite_bits f False"
| "overflow_bits f RTN True = infinity_bits f True"

definition subnormal_result_bits ::
    "binary_format \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> fp_bits" where
  "subnormal_result_bits f negative m =
    \<lparr>negative_bit = negative,
      exponent_field = m div 2 ^ fraction_bits f,
      fraction_field = m mod 2 ^ fraction_bits f\<rparr>"

definition normal_result_bits ::
    "binary_format \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> fp_bits" where
  "normal_result_bits f negative m e =
    \<lparr>negative_bit = negative,
      exponent_field = nat (e + int (format_bias f)),
      fraction_field = m - 2 ^ fraction_bits f\<rparr>"

definition encode_rounded_core ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> bool \<Rightarrow> rounded_core \<Rightarrow> fp_bits"
  where
  "encode_rounded_core f rm negative c =
     (if core_is_subnormal c then
        subnormal_result_bits f negative (core_significand c)
      else if format_emax f < core_exponent c then
        overflow_bits f rm negative
      else
        normal_result_bits f negative (core_significand c) (core_exponent c))"

definition round_rational_to_format_bits ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> bool \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> fp_bits" where
  "round_rational_to_format_bits f rm negative n d =
    encode_rounded_core f rm negative
      (round_rational_core f rm negative n d)"

lemma encode_rounded_core_negative_bit [simp]:
  "negative_bit (encode_rounded_core f rm negative c) = negative"
  by (cases "core_is_subnormal c";
      cases "format_emax f < core_exponent c";
      cases rm; cases negative)
    (simp_all add: encode_rounded_core_def subnormal_result_bits_def
      normal_result_bits_def infinity_bits_def maximum_finite_bits_def)

lemma round_rational_to_format_bits_negative_bit [simp]:
  "negative_bit (round_rational_to_format_bits f rm negative n d) = negative"
  by (simp add: round_rational_to_format_bits_def)

lemma signed_zero_bits_cases [simp]:
  "signed_zero_bits False = positive_zero_bits"
  "signed_zero_bits True = negative_zero_bits"
  by (simp_all add: signed_zero_bits_def positive_zero_bits_def negative_zero_bits_def)

lemma infinity_bits_is_infinity [simp]:
  "bits_is_infinity f (infinity_bits f negative)"
  by (simp add: bits_is_infinity_def infinity_bits_def)

lemma infinity_bits_not_nan [simp]:
  "\<not> bits_is_nan f (infinity_bits f negative)"
  by (simp add: bits_is_nan_def infinity_bits_def)

lemma decode_infinity_bits [simp]:
  "decode_bits f (infinity_bits f negative) = Dynamic_Infinity negative"
  by (simp only: decode_bits_def infinity_bits_not_nan
      infinity_bits_is_infinity if_False if_True;
      simp add: infinity_bits_def)

lemma exponent_all_ones_pos:
  assumes "0 < exponent_bits f"
  shows "0 < exponent_all_ones f"
proof -
  have "1 < (2::nat) ^ exponent_bits f"
    by (rule one_less_power) (simp_all add: assms)
  then show ?thesis by (simp add: exponent_all_ones_def)
qed

lemma exponent_all_ones_gt_one:
  assumes "valid_format f"
  shows "1 < exponent_all_ones f"
proof -
  have eb: "2 \<le> exponent_bits f"
    using assms by (rule valid_format_exponent_bits)
  have pow_ge: "(2::nat) ^ 2 \<le> 2 ^ exponent_bits f"
    by (rule power_increasing) (simp_all add: eb)
  then obtain k where power_eq: "(2::nat) ^ exponent_bits f = 4 + k"
    by (auto simp: nat_le_iff_add)
  show ?thesis
    unfolding exponent_all_ones_def using power_eq by simp
qed

lemma infinity_bits_well_formed:
  assumes "valid_format f"
  shows "bits_well_formed f (infinity_bits f negative)"
proof -
  have eb: "0 < exponent_bits f" using assms
    by (simp add: valid_format_def)
  have fb: "0 < fraction_bits f" using assms
    by (rule valid_format_fraction_bits_pos)
  show ?thesis
    using exponent_all_ones_pos[OF eb]
    by (simp add: bits_well_formed_def infinity_bits_def exponent_all_ones_def fb)
qed

lemma maximum_finite_bits_well_formed:
  assumes "valid_format f"
  shows "bits_well_formed f (maximum_finite_bits f negative)"
proof -
  have eb: "0 < exponent_bits f" using assms
    by (simp add: valid_format_def)
  have fb: "0 < fraction_bits f" using assms
    by (rule valid_format_fraction_bits_pos)
  show ?thesis
    using exponent_all_ones_pos[OF eb]
    by (simp add: bits_well_formed_def maximum_finite_bits_def
        exponent_all_ones_def fb)
qed

lemma maximum_finite_bits_not_infinity:
  assumes "valid_format f"
  shows "\<not> bits_is_infinity f (maximum_finite_bits f negative)"
proof -
  have pos: "0 < exponent_all_ones f"
    using exponent_all_ones_gt_one[OF assms] by linarith
  then obtain k where all_ones: "exponent_all_ones f = Suc k"
    by (cases "exponent_all_ones f") auto
  show ?thesis
    using all_ones
    by (simp add: bits_is_infinity_def maximum_finite_bits_def)
qed

lemma maximum_finite_bits_not_nan:
  assumes "valid_format f"
  shows "\<not> bits_is_nan f (maximum_finite_bits f negative)"
proof -
  have pos: "0 < exponent_all_ones f"
    using exponent_all_ones_gt_one[OF assms] by linarith
  then obtain k where all_ones: "exponent_all_ones f = Suc k"
    by (cases "exponent_all_ones f") auto
  show ?thesis
    using all_ones
    by (simp add: bits_is_nan_def maximum_finite_bits_def)
qed

lemma decode_maximum_finite_bits:
  assumes "valid_format f"
  shows "decode_bits f (maximum_finite_bits f negative) =
    Dynamic_Finite negative (finite_magnitude f (maximum_finite_bits f negative))"
  using maximum_finite_bits_not_infinity[OF assms, of negative]
    maximum_finite_bits_not_nan[OF assms, of negative]
  by (simp add: decode_bits_def maximum_finite_bits_def)

lemma overflow_bits_well_formed:
  assumes "valid_format f"
  shows "bits_well_formed f (overflow_bits f rm negative)"
  using infinity_bits_well_formed[OF assms]
    maximum_finite_bits_well_formed[OF assms]
  by (cases rm; cases negative) simp_all

lemma overflow_bits_policy:
  "overflow_bits f rm negative = infinity_bits f negative \<or>
   overflow_bits f rm negative = maximum_finite_bits f negative"
  by (cases rm; cases negative) simp_all

section \<open>Subnormal grid and promotion to the smallest normal\<close>

lemma subnormal_result_fields_below:
  assumes "m < 2 ^ fraction_bits f"
  shows "exponent_field (subnormal_result_bits f negative m) = 0"
    and "fraction_field (subnormal_result_bits f negative m) = m"
  using assms by (simp_all add: subnormal_result_bits_def)

lemma subnormal_result_fields_at_boundary:
  assumes "0 < fraction_bits f"
  shows "exponent_field
      (subnormal_result_bits f negative (2 ^ fraction_bits f)) = 1"
    and "fraction_field
      (subnormal_result_bits f negative (2 ^ fraction_bits f)) = 0"
  using assms by (simp_all add: subnormal_result_bits_def)

lemma subnormal_result_bits_well_formed:
  assumes valid: "valid_format f"
      and bound: "m \<le> 2 ^ fraction_bits f"
  shows "bits_well_formed f (subnormal_result_bits f negative m)"
proof -
  have eb: "2 \<le> exponent_bits f" using valid
    by (rule valid_format_exponent_bits)
  have pow: "0 < (2::nat) ^ fraction_bits f" by simp
  have exp_le: "m div 2 ^ fraction_bits f \<le> 1"
  proof -
    from bound consider (below) "m < 2 ^ fraction_bits f"
      | (equal) "m = 2 ^ fraction_bits f"
      by (metis le_neq_implies_less)
    then show ?thesis
    proof cases
      case below
      then show ?thesis by simp
    next
      case equal
      with pow show ?thesis by simp
    qed
  qed
  have exp_bound: "m div 2 ^ fraction_bits f < 2 ^ exponent_bits f"
  proof -
    have "1 < (2::nat) ^ exponent_bits f"
      using eb one_less_power[of "2::nat" "exponent_bits f"] by simp
    with exp_le show ?thesis by linarith
  qed
  show ?thesis
    using exp_bound pow
    by (simp add: bits_well_formed_def subnormal_result_bits_def)
qed

lemma decode_subnormal_result_bits:
  assumes valid: "valid_format f"
      and bound: "m \<le> 2 ^ fraction_bits f"
  shows "decode_bits f (subnormal_result_bits f negative m) =
    Dynamic_Finite negative
      (of_nat m * pow2_rat (format_emin f - int (fraction_bits f)))"
proof -
  have all_gt: "1 < exponent_all_ones f"
    by (rule exponent_all_ones_gt_one[OF valid])
  from bound consider (below) "m < 2 ^ fraction_bits f"
    | (equal) "m = 2 ^ fraction_bits f"
    by (metis le_neq_implies_less)
  then show ?thesis
  proof cases
    case below
    then show ?thesis
      using all_gt
      by (simp add: decode_bits_def bits_is_nan_def bits_is_infinity_def
          subnormal_result_bits_def finite_magnitude_def)
  next
    case equal
    then show ?thesis
      using all_gt valid_format_fraction_bits_pos[OF valid]
      by (simp add: decode_bits_def bits_is_nan_def bits_is_infinity_def
          subnormal_result_bits_def finite_magnitude_def format_emin_def)
  qed
qed

lemma decode_subnormal_result_zero [simp]:
  assumes "valid_format f"
  shows "decode_bits f (subnormal_result_bits f negative 0) =
    Dynamic_Finite negative 0"
proof -
  have eb: "0 < exponent_bits f" using assms
    by (simp add: valid_format_def)
  have all_ones: "exponent_all_ones f \<noteq> 0"
  proof
    assume "exponent_all_ones f = 0"
    with exponent_all_ones_pos[OF eb] show False by simp
  qed
  show ?thesis
    using all_ones
    by (simp add: subnormal_result_bits_def decode_bits_def bits_is_nan_def
        bits_is_infinity_def finite_magnitude_def)
qed

lemma subnormal_zero_preserves_sign:
  assumes "valid_format f"
  shows "decode_bits f (subnormal_result_bits f negative 0) =
    Dynamic_Finite negative 0"
  using assms by simp

section \<open>Normal encoding and final regime choice\<close>

lemma normal_result_bits_well_formed:
  assumes valid: "valid_format f"
      and biased_pos: "0 < e + int (format_bias f)"
      and biased_bound:
        "nat (e + int (format_bias f)) < exponent_all_ones f"
      and significand_lower: "2 ^ fraction_bits f \<le> m"
      and significand_upper:
        "m < 2 ^ fraction_bits f + 2 ^ fraction_bits f"
  shows "bits_well_formed f (normal_result_bits f negative m e)"
proof -
  have exponent_bound:
    "nat (e + int (format_bias f)) < 2 ^ exponent_bits f"
  proof -
    have "exponent_all_ones f < 2 ^ exponent_bits f"
      using valid exponent_all_ones_pos
      by (simp add: exponent_all_ones_def valid_format_def)
    with biased_bound show ?thesis by (rule order_less_trans)
  qed
  have fraction_bound:
    "m - 2 ^ fraction_bits f < 2 ^ fraction_bits f"
    using significand_lower significand_upper
    by (simp add: less_diff_conv2)
  show ?thesis
    using exponent_bound fraction_bound
    by (simp add: bits_well_formed_def normal_result_bits_def)
qed

lemma decode_normal_result_bits:
  assumes valid: "valid_format f"
      and biased_pos: "0 < e + int (format_bias f)"
      and biased_bound:
        "nat (e + int (format_bias f)) < exponent_all_ones f"
      and significand_lower: "2 ^ fraction_bits f \<le> m"
  shows "decode_bits f (normal_result_bits f negative m e) =
    Dynamic_Finite negative
      (of_nat m * pow2_rat (e - int (fraction_bits f)))"
proof -
  have exponent_nonzero:
    "nat (e + int (format_bias f)) \<noteq> 0"
    using biased_pos by simp
  have exponent_not_special:
    "nat (e + int (format_bias f)) \<noteq> exponent_all_ones f"
    using biased_bound by auto
  have exponent_cast:
    "int (nat (e + int (format_bias f))) = e + int (format_bias f)"
    using biased_pos by simp
  have significand:
    "2 ^ fraction_bits f + (m - 2 ^ fraction_bits f) = m"
    using significand_lower by simp
  show ?thesis
    using exponent_nonzero exponent_not_special exponent_cast significand
    by (simp add: decode_bits_def bits_is_nan_def bits_is_infinity_def
        normal_result_bits_def finite_magnitude_def)
qed

definition core_encoding_invariant :: "binary_format \<Rightarrow> rounded_core \<Rightarrow> bool"
  where
  "core_encoding_invariant f c \<longleftrightarrow>
    (if core_is_subnormal c then
       core_significand c \<le> 2 ^ fraction_bits f
     else if format_emax f < core_exponent c then True
     else
       0 < core_exponent c + int (format_bias f) \<and>
       nat (core_exponent c + int (format_bias f)) < exponent_all_ones f \<and>
       2 ^ fraction_bits f \<le> core_significand c \<and>
       core_significand c <
         2 ^ fraction_bits f + 2 ^ fraction_bits f)"

lemma apply_significand_carry_invariant:
  assumes valid: "valid_format f"
      and exponent_lower: "format_emin f \<le> e"
      and significand_lower: "2 ^ fraction_bits f \<le> m"
      and significand_upper: "m \<le> 2 ^ precision_bits f"
  shows "core_encoding_invariant f (apply_significand_carry f m e)"
proof (cases "m = 2 ^ precision_bits f")
  case carry: True
  have precision_pos: "0 < precision_bits f"
    using valid by (simp add: valid_format_def)
  have core:
    "apply_significand_carry f m e =
      \<lparr>core_significand = 2 ^ fraction_bits f,
        core_exponent = e + 1, core_is_subnormal = False\<rparr>"
    using carry carry_at_precision[OF precision_pos, of e] by simp
  show ?thesis
  proof (cases "format_emax f < e + 1")
    case True
    with core show ?thesis by (simp add: core_encoding_invariant_def)
  next
    case False
    have lower: "format_emin f \<le> e + 1"
      using exponent_lower by linarith
    have upper: "e + 1 \<le> format_emax f"
      using False by simp
    have biased_pos:
      "0 < (e + 1) + int (format_bias f)"
      by (rule normal_biased_exponent_bounds(1)[OF valid lower upper])
    have biased_bound:
      "nat ((e + 1) + int (format_bias f)) < exponent_all_ones f"
      by (rule normal_biased_exponent_bounds(2)[OF valid lower upper])
    have fraction_upper:
      "(2::nat) ^ fraction_bits f <
        2 ^ fraction_bits f + 2 ^ fraction_bits f"
      by simp
    from core False biased_pos biased_bound fraction_upper show ?thesis
      by (simp add: core_encoding_invariant_def)
  qed
next
  case no_carry: False
  have core:
    "apply_significand_carry f m e =
      \<lparr>core_significand = m, core_exponent = e,
        core_is_subnormal = False\<rparr>"
    by (rule no_significand_carry[OF no_carry])
  have strict_precision: "m < 2 ^ precision_bits f"
    using significand_upper no_carry by (metis le_neq_implies_less)
  have fraction_upper:
    "m < 2 ^ fraction_bits f + 2 ^ fraction_bits f"
    using strict_precision valid_format_precision_power[OF valid] by simp
  show ?thesis
  proof (cases "format_emax f < e")
    case True
    with core show ?thesis by (simp add: core_encoding_invariant_def)
  next
    case False
    have upper: "e \<le> format_emax f" using False by simp
    have biased_pos: "0 < e + int (format_bias f)"
      by (rule normal_biased_exponent_bounds(1)
          [OF valid exponent_lower upper])
    have biased_bound:
      "nat (e + int (format_bias f)) < exponent_all_ones f"
      by (rule normal_biased_exponent_bounds(2)
          [OF valid exponent_lower upper])
    from core False biased_pos biased_bound significand_lower fraction_upper
    show ?thesis by (simp add: core_encoding_invariant_def)
  qed
qed

lemma round_rational_core_at_invariant:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
  shows "core_encoding_invariant f
    (round_rational_core_at f rm negative n d e)"
proof (cases "format_emin f \<le> e")
  case normal: True
  have bounds:
    "2 ^ fraction_bits f \<le>
       scaled_round_integer rm negative n d
         (int (fraction_bits f) - e) \<and>
     scaled_round_integer rm negative n d
         (int (fraction_bits f) - e) \<le> 2 ^ precision_bits f"
    by (rule normal_rounded_significand_bounds[OF valid denominator rel])
  have invariant:
    "core_encoding_invariant f
      (apply_significand_carry f
        (scaled_round_integer rm negative n d
          (int (fraction_bits f) - e)) e)"
  proof -
    have lower:
      "2 ^ fraction_bits f \<le>
        scaled_round_integer rm negative n d
          (int (fraction_bits f) - e)"
      using bounds by blast
    have upper:
      "scaled_round_integer rm negative n d
          (int (fraction_bits f) - e) \<le> 2 ^ precision_bits f"
      using bounds by blast
    show ?thesis
      by (rule apply_significand_carry_invariant
          [OF valid normal lower upper])
  qed
  show ?thesis
    using normal invariant by (simp add: round_rational_core_at_def)
next
  case False
  then have subnormal: "e < format_emin f" by simp
  have bound:
    "scaled_round_integer rm negative n d
       (int (fraction_bits f) - format_emin f) \<le>
     2 ^ fraction_bits f"
    by (rule subnormal_rounded_significand_upper
        [OF denominator rel subnormal])
  show ?thesis
    using False bound
    by (simp add: round_rational_core_at_def core_encoding_invariant_def)
qed

lemma round_rational_core_invariant_from_log:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and log_exists: "\<exists>e. floor_log2_rel n d e"
  shows "core_encoding_invariant f
    (round_rational_core f rm negative n d)"
proof -
  have rel: "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct[OF log_exists])
  show ?thesis
    unfolding round_rational_core_def
    by (rule round_rational_core_at_invariant[OF valid denominator rel])
qed

lemma round_rational_core_invariant:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
  shows "core_encoding_invariant f
    (round_rational_core f rm negative n d)"
  by (rule round_rational_core_invariant_from_log
      [OF valid denominator floor_log2_rel_exists[OF numerator denominator]])

lemma encode_rounded_core_well_formed:
  assumes valid: "valid_format f"
      and invariant: "core_encoding_invariant f c"
  shows "bits_well_formed f (encode_rounded_core f rm negative c)"
proof (cases "core_is_subnormal c")
  case True
  with invariant have bound:
    "core_significand c \<le> 2 ^ fraction_bits f"
    by (simp add: core_encoding_invariant_def)
  from True show ?thesis
    by (simp add: encode_rounded_core_def
        subnormal_result_bits_well_formed[OF valid bound])
next
  case False
  show ?thesis
  proof (cases "format_emax f < core_exponent c")
    case True
    with False show ?thesis
      by (simp add: encode_rounded_core_def overflow_bits_well_formed[OF valid])
  next
    case not_overflow: False
    with invariant False have normal:
      "0 < core_exponent c + int (format_bias f)"
      "nat (core_exponent c + int (format_bias f)) < exponent_all_ones f"
      "2 ^ fraction_bits f \<le> core_significand c"
      "core_significand c <
        2 ^ fraction_bits f + 2 ^ fraction_bits f"
      by (simp_all add: core_encoding_invariant_def)
    from False not_overflow show ?thesis
      by (simp add: encode_rounded_core_def
          normal_result_bits_well_formed[OF valid normal])
  qed
qed

lemma decode_encode_rounded_core:
  assumes valid: "valid_format f"
      and invariant: "core_encoding_invariant f c"
  shows "decode_bits f (encode_rounded_core f rm negative c) =
    (if core_is_subnormal c then
       Dynamic_Finite negative
         (of_nat (core_significand c) *
           pow2_rat (format_emin f - int (fraction_bits f)))
     else if format_emax f < core_exponent c then
       decode_bits f (overflow_bits f rm negative)
     else
       Dynamic_Finite negative
         (of_nat (core_significand c) *
           pow2_rat (core_exponent c - int (fraction_bits f))))"
proof (cases "core_is_subnormal c")
  case subnormal: True
  with invariant have bound:
    "core_significand c \<le> 2 ^ fraction_bits f"
    by (simp add: core_encoding_invariant_def)
  show ?thesis
    using subnormal decode_subnormal_result_bits[OF valid bound, of negative]
    by (simp add: encode_rounded_core_def)
next
  case normal: False
  show ?thesis
  proof (cases "format_emax f < core_exponent c")
    case overflow: True
    with normal show ?thesis by (simp add: encode_rounded_core_def)
  next
    case no_overflow: False
    with invariant normal have biased_pos:
      "0 < core_exponent c + int (format_bias f)"
      by (simp add: core_encoding_invariant_def)
    from invariant normal no_overflow have biased_bound:
      "nat (core_exponent c + int (format_bias f)) < exponent_all_ones f"
      by (simp add: core_encoding_invariant_def)
    from invariant normal no_overflow have significand_lower:
      "2 ^ fraction_bits f \<le> core_significand c"
      by (simp add: core_encoding_invariant_def)
    have decoded:
      "decode_bits f
        (normal_result_bits f negative (core_significand c) (core_exponent c)) =
       Dynamic_Finite negative
        (of_nat (core_significand c) *
          pow2_rat (core_exponent c - int (fraction_bits f)))"
      by (rule decode_normal_result_bits
          [OF valid biased_pos biased_bound significand_lower])
    from normal no_overflow decoded show ?thesis
      by (simp add: encode_rounded_core_def)
  qed
qed

lemma round_rational_to_format_bits_well_formed_from_invariant:
  assumes "valid_format f"
      and "core_encoding_invariant f (round_rational_core f rm negative n d)"
  shows "bits_well_formed f
    (round_rational_to_format_bits f rm negative n d)"
  unfolding round_rational_to_format_bits_def
  by (rule encode_rounded_core_well_formed[OF assms])

lemma round_rational_to_format_bits_well_formed:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
  shows "bits_well_formed f
    (round_rational_to_format_bits f rm negative n d)"
proof -
  have invariant:
    "core_encoding_invariant f (round_rational_core f rm negative n d)"
    by (rule round_rational_core_invariant
        [OF valid numerator denominator])
  show ?thesis
    by (rule round_rational_to_format_bits_well_formed_from_invariant
        [OF valid invariant])
qed

lemma decode_round_rational_to_format_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
  shows "decode_bits f
      (round_rational_to_format_bits f rm negative n d) =
    (let c = round_rational_core f rm negative n d in
      if core_is_subnormal c then
        Dynamic_Finite negative
          (of_nat (core_significand c) *
            pow2_rat (format_emin f - int (fraction_bits f)))
      else if format_emax f < core_exponent c then
        decode_bits f (overflow_bits f rm negative)
      else
        Dynamic_Finite negative
          (of_nat (core_significand c) *
            pow2_rat (core_exponent c - int (fraction_bits f))))"
proof -
  have invariant:
    "core_encoding_invariant f (round_rational_core f rm negative n d)"
    by (rule round_rational_core_invariant[OF valid numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def Let_def
    by (rule decode_encode_rounded_core[OF valid invariant])
qed

lemma encode_rounded_core_subnormal [simp]:
  assumes "core_is_subnormal c"
  shows "encode_rounded_core f rm negative c =
    subnormal_result_bits f negative (core_significand c)"
  using assms by (simp add: encode_rounded_core_def)

lemma encode_rounded_core_overflow [simp]:
  assumes "\<not> core_is_subnormal c" "format_emax f < core_exponent c"
  shows "encode_rounded_core f rm negative c = overflow_bits f rm negative"
  using assms by (simp add: encode_rounded_core_def)

lemma encode_rounded_core_normal [simp]:
  assumes "\<not> core_is_subnormal c" "core_exponent c \<le> format_emax f"
  shows "encode_rounded_core f rm negative c =
    normal_result_bits f negative (core_significand c) (core_exponent c)"
  using assms by (simp add: encode_rounded_core_def)

end

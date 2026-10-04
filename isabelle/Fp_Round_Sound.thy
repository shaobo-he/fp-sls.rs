(* SPDX-License-Identifier: MIT *)

section \<open>Sound directed rational conversion\<close>

theory Fp_Round_Sound
  imports Fp_Round_Directed_IEEE Fp_Round_Ties Fp_IEEE_Exact
begin

fun ieee_round_mode :: "fp_round_mode \<Rightarrow> roundmode" where
  "ieee_round_mode Fp_Round_Int.RNE = IEEE.RNE"
| "ieee_round_mode Fp_Round_Int.RNA = IEEE.RNA"
| "ieee_round_mode Fp_Round_Int.RTZ = IEEE.RTZ"
| "ieee_round_mode Fp_Round_Int.RTP = IEEE.RTP"
| "ieee_round_mode Fp_Round_Int.RTN = IEEE.RTN"

lemma single_nan_of_float_zero [simp]:
  "single_nan_of_float (0 :: ('e::len, 'f::len) float) =
    (0 :: ('e, 'f) floatSingleNaN)"
  unfolding single_nan_of_float_def by (rule zero_floatSingleNaN.abs_eq[symmetric])

lemma single_nan_of_float_minus_zero [simp]:
  "single_nan_of_float (IEEE.minus_zero :: ('e::len, 'f::len) float) =
    (minus_zero :: ('e, 'f) floatSingleNaN)"
  unfolding single_nan_of_float_def by (rule minus_zero.abs_eq[symmetric])

lemma afp_rational_result_zero_sign:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
  assumes width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and zero:
        "is_zero (afp_rational_result rm negative n d ::
          ('e, 'f::len) floatSingleNaN)"
  shows
    "(afp_rational_result rm negative n d ::
      ('e, 'f) floatSingleNaN) = fp_zero_with_sign negative"
proof -
  let ?raw = "afp_round_rational rm negative n d :: ('e, 'f) float"
  have quotient_zero:
    "is_zero (single_nan_of_float ?raw)"
    using zero by (simp add: afp_rational_result_def)
  have raw_zero: "IEEE.is_zero ?raw"
    using quotient_zero unfolding single_nan_of_float_def by transfer
  have raw_sign: "IEEE.sign ?raw = (if negative then 1 else 0)"
    by (rule afp_round_rational_sign[OF width numerator denominator])
  from raw_zero consider (positive) "?raw = 0"
    | (negative) "?raw = IEEE.minus_zero"
    by (rule is_zero_cases)
  then show ?thesis
  proof cases
    case positive
    then have "negative = False"
      using raw_sign by (cases negative) (simp_all add: zero_simps)
    with positive show ?thesis
      by (simp add: afp_rational_result_def fp_zero_with_sign_def)
  next
    case negative
    then have "negative = True"
      using raw_sign by (cases negative) (simp_all add: zero_simps)
    with negative show ?thesis
      by (simp add: afp_rational_result_def fp_zero_with_sign_def)
  qed
qed

theorem afp_round_rational_RTP_sound:
  fixes negative :: bool and n d :: nat
    and f :: binary_format and result :: "('e::len, 'f::len) floatSingleNaN"
    and exact :: real
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and result: "result \<equiv>
        (afp_rational_result Fp_Round_Int.RTP negative n d ::
          ('e, 'f) floatSingleNaN)"
      and exact: "exact \<equiv> of_rat (exact_input_value negative n d)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal
          (round_rational_core f Fp_Round_Int.RTP negative n d) \<or>
         core_exponent
          (round_rational_core f Fp_Round_Int.RTP negative n d) \<le>
           format_emax f"
  shows "fp_round_rel IEEE.RTP exact result"
proof -
  have least: "fp_least_finite_above exact result"
    unfolding f result exact
    by (rule afp_round_rational_RTP_least_finite_above[
          OF width numerator denominator no_overflow[unfolded f]])
  have finite: "is_finite result"
    using least by (simp add: fp_least_finite_above_def)
  have direction: "exact \<le> valof result"
    using least by (simp add: fp_least_finite_above_def)
  have result_bound:
    "valof result \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_finite_le_largest)
      (use width finite in simp_all)
  have not_overflow:
    "\<not> exact > fp_largest TYPE(('e, 'f) floatSingleNaN)"
    using direction result_bound by linarith
  show ?thesis
    using least not_overflow by simp
qed

theorem afp_round_rational_RTN_sound:
  fixes negative :: bool and n d :: nat
    and f :: binary_format and result :: "('e::len, 'f::len) floatSingleNaN"
    and exact :: real
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and result: "result \<equiv>
        (afp_rational_result Fp_Round_Int.RTN negative n d ::
          ('e, 'f) floatSingleNaN)"
      and exact: "exact \<equiv> of_rat (exact_input_value negative n d)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal
          (round_rational_core f Fp_Round_Int.RTN negative n d) \<or>
         core_exponent
          (round_rational_core f Fp_Round_Int.RTN negative n d) \<le>
           format_emax f"
  shows "fp_round_rel IEEE.RTN exact result"
proof -
  have greatest: "fp_greatest_finite_below exact result"
    unfolding f result exact
    by (rule afp_round_rational_RTN_greatest_finite_below[
          OF width numerator denominator no_overflow[unfolded f]])
  have finite: "is_finite result"
    using greatest by (simp add: fp_greatest_finite_below_def)
  have direction: "valof result \<le> exact"
    using greatest by (simp add: fp_greatest_finite_below_def)
  have result_bound:
    "- fp_largest TYPE(('e, 'f) floatSingleNaN) \<le> valof result"
    by (rule fp_finite_ge_minus_largest)
      (use width finite in simp_all)
  have not_overflow:
    "\<not> exact < - fp_largest TYPE(('e, 'f) floatSingleNaN)"
    using direction result_bound by linarith
  show ?thesis
    using greatest not_overflow by simp
qed

theorem afp_round_rational_RTZ_sound:
  fixes negative :: bool and n d :: nat
    and f :: binary_format and result :: "('e::len, 'f::len) floatSingleNaN"
    and exact :: real
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and result: "result \<equiv>
        (afp_rational_result Fp_Round_Int.RTZ negative n d ::
          ('e, 'f) floatSingleNaN)"
      and exact: "exact \<equiv> of_rat (exact_input_value negative n d)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal
          (round_rational_core f Fp_Round_Int.RTZ negative n d) \<or>
         core_exponent
          (round_rational_core f Fp_Round_Int.RTZ negative n d) \<le>
           format_emax f"
  shows "fp_round_rel IEEE.RTZ exact result"
proof -
  have extremal:
    "if negative then fp_least_finite_above exact result
     else fp_greatest_finite_below exact result"
    unfolding f result exact
    by (rule afp_round_rational_RTZ_extremal[
          OF width numerator denominator no_overflow[unfolded f]])
  show ?thesis
  proof (cases negative)
    case True
    have input_negative: "exact < 0"
      using numerator denominator True
      by (simp add: exact exact_input_value_def signed_rat_def)
    show ?thesis using extremal True input_negative by simp
  next
    case False
    have input_nonnegative: "0 \<le> exact"
      using denominator False
      by (simp add: exact exact_input_value_def signed_rat_def)
    show ?thesis using extremal False input_nonnegative by simp
  qed
qed

corollary afp_round_rational_RTP_signed_sound:
  assumes sound: "fp_round_rel IEEE.RTP exact result"
      and zero_sign:
        "is_zero result \<Longrightarrow> result = fp_zero_with_sign negative"
  shows "fp_signed_round_rel IEEE.RTP negative exact result"
  using sound zero_sign unfolding fp_signed_round_rel_def by blast

corollary afp_round_rational_RTN_signed_sound:
  assumes sound: "fp_round_rel IEEE.RTN exact result"
      and zero_sign:
        "is_zero result \<Longrightarrow> result = fp_zero_with_sign negative"
  shows "fp_signed_round_rel IEEE.RTN negative exact result"
  using sound zero_sign unfolding fp_signed_round_rel_def by blast

corollary afp_round_rational_RTZ_signed_sound:
  assumes sound: "fp_round_rel IEEE.RTZ exact result"
      and zero_sign:
        "is_zero result \<Longrightarrow> result = fp_zero_with_sign negative"
  shows "fp_signed_round_rel IEEE.RTZ negative exact result"
  using sound zero_sign unfolding fp_signed_round_rel_def by blast

end

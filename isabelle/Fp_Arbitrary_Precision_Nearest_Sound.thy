(* SPDX-License-Identifier: MIT *)

section \<open>Nearest and overflow soundness for arbitrary-precision binary sources\<close>

theory Fp_Arbitrary_Precision_Nearest_Sound
  imports Fp_Arbitrary_Precision_Sound Fp_Round_Nearest_Sound
begin

theorem round_ap_binary_subnormal_nearest_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and subnormal:
        "floor_log2_spec (ap_numerator x) (ap_denominator x) <
          format_emin (runtime_format TYPE(('e, 'f::len) float))"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (exact_input_value (ap_negative x)
          (ap_numerator x) (ap_denominator x)))
        (afp_rational_result rm (ap_negative x)
          (ap_numerator x) (ap_denominator x) ::
            ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_subnormal_nearest_sound[
          OF width numerator denominator nearest subnormal])
  have ap_sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (ap_binary_value x))
        (ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
    using sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
  have zero_sign:
      "is_zero (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) \<Longrightarrow>
       (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
         fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  have total:
      "(total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
        ap_afp_result rm x"
    by (rule total_ap_afp_result_nonzero[OF nonzero])
  show ?thesis
    unfolding fp_signed_round_rel_def total
    using ap_sound zero_sign by blast
qed

theorem round_ap_binary_nearest_overflow_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and threshold:
        "format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f::len) float)) \<le>
         exact_magnitude (ap_numerator x) (ap_denominator x)"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (exact_input_value (ap_negative x)
          (ap_numerator x) (ap_denominator x)))
        (afp_rational_result rm (ap_negative x)
          (ap_numerator x) (ap_denominator x) ::
            ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_nearest_overflow_sound[
          OF width numerator denominator nearest threshold])
  have ap_sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (ap_binary_value x))
        (ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
    using sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
  have zero_sign:
      "is_zero (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) \<Longrightarrow>
       (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
         fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  have total:
      "(total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
        ap_afp_result rm x"
    by (rule total_ap_afp_result_nonzero[OF nonzero])
  show ?thesis
    unfolding fp_signed_round_rel_def total
    using ap_sound zero_sign by blast
qed

theorem round_ap_binary_directed_above_maximum_signed_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and above:
        "format_maximum_finite_magnitude
          (runtime_format TYPE(('e, 'f::len) float)) <
         exact_magnitude (ap_numerator x) (ap_denominator x)"
  shows
    "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
    "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
    "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  note sound = afp_round_rational_directed_above_maximum_sound[
    OF width numerator denominator above,
    of "ap_negative x"]
  have zero_sign:
      "\<And>rm. is_zero (ap_afp_result rm x ::
          ('e, 'f) floatSingleNaN) \<Longrightarrow>
       (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
         fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  have total:
      "\<And>rm. (total_ap_afp_result rm x ::
          ('e, 'f) floatSingleNaN) = ap_afp_result rm x"
    by (rule total_ap_afp_result_nonzero[OF nonzero])
  show "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
    unfolding fp_signed_round_rel_def total
    using sound(1) zero_sign[of Fp_Round_Int.RTP]
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result;
        blast)
  show "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
    unfolding fp_signed_round_rel_def total
    using sound(2) zero_sign[of Fp_Round_Int.RTN]
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result;
        blast)
  show "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
    unfolding fp_signed_round_rel_def total
    using sound(3) zero_sign[of Fp_Round_Int.RTZ]
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result;
        blast)
qed


theorem round_ap_binary_normal_nearest_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and normal:
        "format_emin (runtime_format TYPE(('e, 'f::len) float)) \<le>
          floor_log2_spec (ap_numerator x) (ap_denominator x)"
      and no_overflow:
        "core_exponent
          (round_rational_core
            (runtime_format TYPE(('e, 'f) float)) rm
            (ap_negative x) (ap_numerator x) (ap_denominator x)) \<le>
          format_emax (runtime_format TYPE(('e, 'f) float))"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (exact_input_value (ap_negative x)
          (ap_numerator x) (ap_denominator x)))
        (afp_rational_result rm (ap_negative x)
          (ap_numerator x) (ap_denominator x) ::
            ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_normal_nearest_sound[
          OF width numerator denominator nearest normal no_overflow])
  have ap_sound:
      "fp_round_rel (ieee_round_mode rm)
        (of_rat (ap_binary_value x))
        (ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
    using sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
  have zero_sign:
      "is_zero (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) \<Longrightarrow>
       (ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
         fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  have total:
      "(total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
        ap_afp_result rm x"
    by (rule total_ap_afp_result_nonzero[OF nonzero])
  show ?thesis
    unfolding fp_signed_round_rel_def total
    using ap_sound zero_sign by blast
qed


theorem round_ap_binary_nearest_below_threshold_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and below:
        "exact_magnitude (ap_numerator x) (ap_denominator x) <
          format_nearest_overflow_threshold
            (runtime_format TYPE(('e, 'f::len) float))"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN)"
proof -
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  have valid: "valid_format ?f"
    by (rule runtime_format_valid[OF width])
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  show ?thesis
  proof (cases
      "floor_log2_spec (ap_numerator x) (ap_denominator x) <
        format_emin ?f")
    case True
    show ?thesis
      by (rule round_ap_binary_subnormal_nearest_signed_sound[
            OF width nonzero nearest True])
  next
    case False
    then have normal:
        "format_emin ?f \<le>
          floor_log2_spec (ap_numerator x) (ap_denominator x)"
      by simp
    have core_bound:
        "core_exponent
          (round_rational_core ?f rm (ap_negative x)
            (ap_numerator x) (ap_denominator x)) \<le>
          format_emax ?f"
      by (rule round_rational_core_normal_nearest_below_threshold[
            OF valid numerator denominator nearest normal below])
    show ?thesis
      by (rule round_ap_binary_normal_nearest_signed_sound[
            OF width nonzero nearest normal core_bound])
  qed
qed

theorem round_ap_binary_directed_at_most_maximum_signed_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and at_most:
        "exact_magnitude (ap_numerator x) (ap_denominator x) \<le>
          format_maximum_finite_magnitude
            (runtime_format TYPE(('e, 'f::len) float))"
  shows
    "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
    "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
    "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
proof -
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  have valid: "valid_format ?f"
    by (rule runtime_format_valid[OF width])
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have no_overflow:
      "\<And>rm. ap_round_no_overflow ?f rm x"
    unfolding ap_round_no_overflow_def
    by (rule round_rational_core_at_most_maximum[
          OF valid numerator denominator at_most])
  have total:
      "\<And>rm. (total_ap_afp_result rm x ::
          ('e, 'f) floatSingleNaN) = ap_afp_result rm x"
    by (rule total_ap_afp_result_nonzero[OF nonzero])
  have rtp:
      "fp_signed_round_rel IEEE.RTP (ap_negative x)
        (of_rat (ap_binary_value x))
        (ap_afp_result Fp_Round_Int.RTP x ::
          ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTP_signed_sound[
          OF width nonzero no_overflow])
  have rtn:
      "fp_signed_round_rel IEEE.RTN (ap_negative x)
        (of_rat (ap_binary_value x))
        (ap_afp_result Fp_Round_Int.RTN x ::
          ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTN_signed_sound[
          OF width nonzero no_overflow])
  have rtz:
      "fp_signed_round_rel IEEE.RTZ (ap_negative x)
        (of_rat (ap_binary_value x))
        (ap_afp_result Fp_Round_Int.RTZ x ::
          ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTZ_signed_sound[
          OF width nonzero no_overflow])
  show
    "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
    using rtp total[of Fp_Round_Int.RTP] by simp
  show
    "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
    using rtn total[of Fp_Round_Int.RTN] by simp
  show
    "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
    using rtz total[of Fp_Round_Int.RTZ] by simp
qed

theorem round_ap_binary_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x ::
        ('e, 'f::len) floatSingleNaN)"
proof (cases "ap_is_zero x")
  case True
  show ?thesis
    by (rule round_zero_ap_binary_signed_sound[OF width True])
next
  case False
  have nonzero: "\<not> ap_is_zero x" by (rule False)
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  show ?thesis
  proof (cases rm)
    case RNE
    show ?thesis
    proof (cases
        "format_nearest_overflow_threshold ?f \<le>
          exact_magnitude (ap_numerator x) (ap_denominator x)")
      case True
      show ?thesis
        using round_ap_binary_nearest_overflow_signed_sound[
          OF width nonzero disjI1[OF refl] True]
          RNE by simp
    next
      case False
      then have below:
          "exact_magnitude (ap_numerator x) (ap_denominator x) <
            format_nearest_overflow_threshold ?f"
        by simp
      show ?thesis
        using round_ap_binary_nearest_below_threshold_signed_sound[
          OF width nonzero disjI1[OF refl] below]
          RNE by simp
    qed
  next
    case RNA
    show ?thesis
    proof (cases
        "format_nearest_overflow_threshold ?f \<le>
          exact_magnitude (ap_numerator x) (ap_denominator x)")
      case True
      show ?thesis
        using round_ap_binary_nearest_overflow_signed_sound[
          OF width nonzero disjI2[OF refl] True]
          RNA by simp
    next
      case False
      then have below:
          "exact_magnitude (ap_numerator x) (ap_denominator x) <
            format_nearest_overflow_threshold ?f"
        by simp
      show ?thesis
        using round_ap_binary_nearest_below_threshold_signed_sound[
          OF width nonzero disjI2[OF refl] below]
          RNA by simp
    qed
  next
    case RTZ
    show ?thesis
    proof (cases
        "format_maximum_finite_magnitude ?f <
          exact_magnitude (ap_numerator x) (ap_denominator x)")
      case True
      note sound =
        round_ap_binary_directed_above_maximum_signed_sound[
          OF width nonzero True]
      show ?thesis using sound(3) RTZ by simp
    next
      case False
      then have at_most:
          "exact_magnitude (ap_numerator x) (ap_denominator x) \<le>
            format_maximum_finite_magnitude ?f"
        by simp
      note sound =
        round_ap_binary_directed_at_most_maximum_signed_sound[
          OF width nonzero at_most]
      show ?thesis using sound(3) RTZ by simp
    qed
  next
    case RTP
    show ?thesis
    proof (cases
        "format_maximum_finite_magnitude ?f <
          exact_magnitude (ap_numerator x) (ap_denominator x)")
      case True
      note sound =
        round_ap_binary_directed_above_maximum_signed_sound[
          OF width nonzero True]
      show ?thesis using sound(1) RTP by simp
    next
      case False
      then have at_most:
          "exact_magnitude (ap_numerator x) (ap_denominator x) \<le>
            format_maximum_finite_magnitude ?f"
        by simp
      note sound =
        round_ap_binary_directed_at_most_maximum_signed_sound[
          OF width nonzero at_most]
      show ?thesis using sound(1) RTP by simp
    qed
  next
    case RTN
    show ?thesis
    proof (cases
        "format_maximum_finite_magnitude ?f <
          exact_magnitude (ap_numerator x) (ap_denominator x)")
      case True
      note sound =
        round_ap_binary_directed_above_maximum_signed_sound[
          OF width nonzero True]
      show ?thesis using sound(2) RTN by simp
    next
      case False
      then have at_most:
          "exact_magnitude (ap_numerator x) (ap_denominator x) \<le>
            format_maximum_finite_magnitude ?f"
        by simp
      note sound =
        round_ap_binary_directed_at_most_maximum_signed_sound[
          OF width nonzero at_most]
      show ?thesis using sound(2) RTN by simp
    qed
  qed
qed
end

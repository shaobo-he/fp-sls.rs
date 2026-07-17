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

end

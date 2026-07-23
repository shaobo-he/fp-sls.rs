(* SPDX-License-Identifier: MIT *)

section \<open>Sound directed rounding of arbitrary-precision binary values\<close>

theory Fp_Arbitrary_Precision_Sound
  imports Fp_Arbitrary_Precision Fp_Round_Sound
begin

text \<open>
  The AFP result below is constructed from exactly the run-time fields produced
  by @{const round_ap_binary_to_format_bits}.  The quotient removes the many
  NaN payloads; finite results, including signed zero, retain their IEEE value
  and sign.
\<close>

definition ap_afp_result ::
    "fp_round_mode \<Rightarrow> ap_binary_float \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN" where
  "ap_afp_result rm x = single_nan_of_float
    (runtime_float_of_bits
      (round_ap_binary_to_format_bits
        (runtime_format TYPE(('e, 'f) float)) rm x) :: ('e, 'f) float)"

lemma ap_afp_result_eq_rational_result:
  "(ap_afp_result rm x :: ('e::len, 'f::len) floatSingleNaN) =
    afp_rational_result rm (ap_negative x)
      (ap_numerator x) (ap_denominator x)"
  by (simp add: ap_afp_result_def afp_rational_result_def
      afp_round_rational_def round_ap_binary_to_format_bits_def)

definition ap_round_no_overflow ::
    "binary_format \<Rightarrow> fp_round_mode \<Rightarrow> ap_binary_float \<Rightarrow> bool" where
  "ap_round_no_overflow f rm x \<longleftrightarrow>
    core_is_subnormal
      (round_rational_core f rm (ap_negative x)
        (ap_numerator x) (ap_denominator x)) \<or>
    core_exponent
      (round_rational_core f rm (ap_negative x)
        (ap_numerator x) (ap_denominator x)) \<le> format_emax f"

lemma ap_afp_result_zero_sign:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and zero:
        "is_zero (ap_afp_result rm x ::
          ('e, 'f::len) floatSingleNaN)"
  shows
    "(ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
      fp_zero_with_sign (ap_negative x)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have rational_zero:
    "is_zero (afp_rational_result rm (ap_negative x)
      (ap_numerator x) (ap_denominator x) ::
        ('e, 'f) floatSingleNaN)"
    using zero by (simp only: ap_afp_result_eq_rational_result)
  have rational_sign:
    "(afp_rational_result rm (ap_negative x)
      (ap_numerator x) (ap_denominator x) ::
        ('e, 'f) floatSingleNaN) = fp_zero_with_sign (ap_negative x)"
    by (rule afp_rational_result_zero_sign[
          OF width numerator denominator rational_zero])
  show ?thesis
    using rational_sign by (simp only: ap_afp_result_eq_rational_result)
qed

theorem round_ap_binary_RTP_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTP x"
  shows
    "fp_round_rel IEEE.RTP (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have core_bound:
    "core_is_subnormal
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTP
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<or>
     core_exponent
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTP
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow by (simp add: ap_round_no_overflow_def)
  have rational_sound:
    "fp_round_rel IEEE.RTP
      (of_rat (exact_input_value (ap_negative x)
        (ap_numerator x) (ap_denominator x)))
      (afp_rational_result Fp_Round_Int.RTP (ap_negative x)
        (ap_numerator x) (ap_denominator x) ::
          ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_RTP_sound[
          OF width numerator denominator core_bound])
  show ?thesis
    using rational_sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
qed

theorem round_ap_binary_RTN_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTN x"
  shows
    "fp_round_rel IEEE.RTN (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have core_bound:
    "core_is_subnormal
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTN
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<or>
     core_exponent
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTN
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow by (simp add: ap_round_no_overflow_def)
  have rational_sound:
    "fp_round_rel IEEE.RTN
      (of_rat (exact_input_value (ap_negative x)
        (ap_numerator x) (ap_denominator x)))
      (afp_rational_result Fp_Round_Int.RTN (ap_negative x)
        (ap_numerator x) (ap_denominator x) ::
          ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_RTN_sound[
          OF width numerator denominator core_bound])
  show ?thesis
    using rational_sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
qed

theorem round_ap_binary_RTZ_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTZ x"
  shows
    "fp_round_rel IEEE.RTZ (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have numerator: "0 < ap_numerator x"
    by (rule ap_nonzero_numerator_pos[OF nonzero])
  have denominator: "0 < ap_denominator x" by simp
  have core_bound:
    "core_is_subnormal
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTZ
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<or>
     core_exponent
      (round_rational_core
        (runtime_format TYPE(('e, 'f) float)) Fp_Round_Int.RTZ
        (ap_negative x) (ap_numerator x) (ap_denominator x)) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow by (simp add: ap_round_no_overflow_def)
  have rational_sound:
    "fp_round_rel IEEE.RTZ
      (of_rat (exact_input_value (ap_negative x)
        (ap_numerator x) (ap_denominator x)))
      (afp_rational_result Fp_Round_Int.RTZ (ap_negative x)
        (ap_numerator x) (ap_denominator x) ::
          ('e, 'f) floatSingleNaN)"
    by (rule afp_round_rational_RTZ_sound[
          OF width numerator denominator core_bound])
  show ?thesis
    using rational_sound
    by (simp only: ap_exact_input_value ap_afp_result_eq_rational_result)
qed

corollary round_ap_binary_RTP_signed_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTP x"
  shows
    "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have sound:
    "fp_round_rel IEEE.RTP (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTP_sound[OF assms])
  have zero_sign:
    "is_zero (ap_afp_result Fp_Round_Int.RTP x ::
       ('e, 'f) floatSingleNaN) \<Longrightarrow>
     (ap_afp_result Fp_Round_Int.RTP x ::
       ('e, 'f) floatSingleNaN) = fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  show ?thesis
    by (rule afp_round_rational_RTP_signed_sound[OF sound zero_sign])
qed

corollary round_ap_binary_RTN_signed_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTN x"
  shows
    "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have sound:
    "fp_round_rel IEEE.RTN (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTN_sound[OF assms])
  have zero_sign:
    "is_zero (ap_afp_result Fp_Round_Int.RTN x ::
       ('e, 'f) floatSingleNaN) \<Longrightarrow>
     (ap_afp_result Fp_Round_Int.RTN x ::
       ('e, 'f) floatSingleNaN) = fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  show ?thesis
    by (rule afp_round_rational_RTN_signed_sound[OF sound zero_sign])
qed

corollary round_ap_binary_RTZ_signed_sound:
  fixes x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and nonzero: "\<not> ap_is_zero x"
      and no_overflow:
        "ap_round_no_overflow
          (runtime_format TYPE(('e, 'f::len) float))
          Fp_Round_Int.RTZ x"
  shows
    "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
proof -
  have sound:
    "fp_round_rel IEEE.RTZ (of_rat (ap_binary_value x))
      (ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f) floatSingleNaN)"
    by (rule round_ap_binary_RTZ_sound[OF assms])
  have zero_sign:
    "is_zero (ap_afp_result Fp_Round_Int.RTZ x ::
       ('e, 'f) floatSingleNaN) \<Longrightarrow>
     (ap_afp_result Fp_Round_Int.RTZ x ::
       ('e, 'f) floatSingleNaN) = fp_zero_with_sign (ap_negative x)"
    by (rule ap_afp_result_zero_sign[OF width nonzero])
  show ?thesis
    by (rule afp_round_rational_RTZ_signed_sound[OF sound zero_sign])
qed

section \<open>Total finite-source conversion, including signed zero\<close>

text \<open>
  The positive-numerator rounding path is intentionally not invoked for zero.
  Instead, a total finite-source result preserves the source zero sign
  explicitly and delegates every nonzero value to @{const ap_afp_result}.
\<close>

definition total_ap_afp_result ::
    "fp_round_mode \<Rightarrow> ap_binary_float \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN" where
  "total_ap_afp_result rm x =
    (if ap_is_zero x then fp_zero_with_sign (ap_negative x)
     else ap_afp_result rm x)"

lemma total_ap_afp_result_zero:
  assumes "ap_is_zero x"
  shows
    "(total_ap_afp_result rm x :: ('e::len, 'f::len) floatSingleNaN) =
      fp_zero_with_sign (ap_negative x)"
  using assms by (simp add: total_ap_afp_result_def)

lemma total_ap_afp_result_nonzero:
  assumes "\<not> ap_is_zero x"
  shows
    "(total_ap_afp_result rm x :: ('e::len, 'f::len) floatSingleNaN) =
      ap_afp_result rm x"
  using assms by (simp add: total_ap_afp_result_def)

lemma single_nan_of_float_is_zero [simp]:
  "is_zero (single_nan_of_float x) \<longleftrightarrow> IEEE.is_zero x"
  unfolding single_nan_of_float_def by transfer simp

lemma fp_zero_with_sign_finite [simp]:
  "is_finite (fp_zero_with_sign negative ::
    ('e::len, 'f::len) floatSingleNaN)"
proof (cases negative)
  case True
  have raw_finite:
    "IEEE.is_finite (IEEE.minus_zero :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have quotient_finite:
    "is_finite (single_nan_of_float
      (IEEE.minus_zero :: ('e, 'f) float))"
    using single_nan_of_float_is_finite[
      of "IEEE.minus_zero :: ('e, 'f) float"] raw_finite by blast
  show ?thesis
    using True quotient_finite
    by (simp only: fp_zero_with_sign_def if_True
        single_nan_of_float_minus_zero)
next
  case False
  have raw_finite: "IEEE.is_finite (0 :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have quotient_finite:
    "is_finite (single_nan_of_float (0 :: ('e, 'f) float))"
    using single_nan_of_float_is_finite[
      of "0 :: ('e, 'f) float"] raw_finite by blast
  show ?thesis
    using False quotient_finite
    by (simp only: fp_zero_with_sign_def if_False
        single_nan_of_float_zero)
qed

lemma fp_zero_with_sign_value [simp]:
  "valof (fp_zero_with_sign negative ::
    ('e::len, 'f::len) floatSingleNaN) = 0"
proof (cases negative)
  case True
  have raw_finite:
    "IEEE.is_finite (IEEE.minus_zero :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have quotient_value:
    "valof (single_nan_of_float
      (IEEE.minus_zero :: ('e, 'f) float)) = 0"
  proof -
    have bridge:
      "valof (single_nan_of_float
          (IEEE.minus_zero :: ('e, 'f) float)) =
        IEEE.valof (IEEE.minus_zero :: ('e, 'f) float)"
      by (rule single_nan_of_float_valof[OF raw_finite])
    show ?thesis using bridge by simp
  qed
  show ?thesis
    using True quotient_value
    by (simp only: fp_zero_with_sign_def if_True
        single_nan_of_float_minus_zero)
next
  case False
  have raw_finite: "IEEE.is_finite (0 :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have quotient_value:
    "valof (single_nan_of_float (0 :: ('e, 'f) float)) = 0"
  proof -
    have bridge:
      "valof (single_nan_of_float (0 :: ('e, 'f) float)) =
        IEEE.valof (0 :: ('e, 'f) float)"
      by (rule single_nan_of_float_valof[OF raw_finite])
    show ?thesis using bridge by simp
  qed
  show ?thesis
    using False quotient_value
    by (simp only: fp_zero_with_sign_def if_False
        single_nan_of_float_zero)
qed

lemma fp_zero_with_sign_is_zero [simp]:
  "is_zero (fp_zero_with_sign negative ::
    ('e::len, 'f::len) floatSingleNaN)"
proof (cases negative)
  case True
  have raw_zero:
    "IEEE.is_zero (IEEE.minus_zero :: ('e, 'f) float)" by simp
  have quotient_zero:
    "is_zero (single_nan_of_float
      (IEEE.minus_zero :: ('e, 'f) float))"
    using single_nan_of_float_is_zero[
      of "IEEE.minus_zero :: ('e, 'f) float"] raw_zero by blast
  show ?thesis
    using True quotient_zero
    by (simp only: fp_zero_with_sign_def if_True
        single_nan_of_float_minus_zero)
next
  case False
  have raw_zero: "IEEE.is_zero (0 :: ('e, 'f) float)" by simp
  have quotient_zero:
    "is_zero (single_nan_of_float (0 :: ('e, 'f) float))"
    using single_nan_of_float_is_zero[
      of "0 :: ('e, 'f) float"] raw_zero by blast
  show ?thesis
    using False quotient_zero
    by (simp only: fp_zero_with_sign_def if_False
        single_nan_of_float_zero)
qed

lemma fp_zero_with_sign_even_lsb [simp]:
  "fp_even_lsb (fp_zero_with_sign negative ::
    ('e::len, 'f::len) floatSingleNaN)"
proof (cases negative)
  case True
  have raw_finite:
    "IEEE.is_finite (IEEE.minus_zero :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have parity:
    "fp_even_lsb (single_nan_of_float
        (IEEE.minus_zero :: ('e, 'f) float)) \<longleftrightarrow>
      even (IEEE.fraction (IEEE.minus_zero :: ('e, 'f) float))"
    by (rule single_nan_of_float_even_lsb[OF raw_finite])
  have raw_even:
    "even (IEEE.fraction (IEEE.minus_zero :: ('e, 'f) float))"
    by (simp add: zero_simps)
  have quotient_even:
    "fp_even_lsb (single_nan_of_float
      (IEEE.minus_zero :: ('e, 'f) float))"
    using parity raw_even by blast
  show ?thesis
    using True quotient_even
    by (simp only: fp_zero_with_sign_def if_True
        single_nan_of_float_minus_zero)
next
  case False
  have raw_finite: "IEEE.is_finite (0 :: ('e, 'f) float)"
    by (simp add: IEEE.is_finite_def)
  have parity:
    "fp_even_lsb (single_nan_of_float (0 :: ('e, 'f) float)) \<longleftrightarrow>
      even (IEEE.fraction (0 :: ('e, 'f) float))"
    by (rule single_nan_of_float_even_lsb[OF raw_finite])
  have raw_even: "even (IEEE.fraction (0 :: ('e, 'f) float))"
    by (simp add: zero_simps)
  have quotient_even:
    "fp_even_lsb (single_nan_of_float (0 :: ('e, 'f) float))"
    using parity raw_even by blast
  show ?thesis
    using False quotient_even
    by (simp only: fp_zero_with_sign_def if_False
        single_nan_of_float_zero)
qed

lemma fp_round_zero_with_sign:
  fixes rm :: fp_round_mode
  assumes width: "2 \<le> LENGTH('e::len)"
  shows
    "fp_round_rel (ieee_round_mode rm) 0
      (fp_zero_with_sign negative ::
        ('e, 'f::len) floatSingleNaN)"
proof -
  have strict_width: "1 < LENGTH('e)" using width by simp
  let ?zero =
    "fp_zero_with_sign negative :: ('e, 'f) floatSingleNaN"
  have finite: "is_finite ?zero" by simp
  have exact: "valof ?zero = 0" by simp
  have even: "fp_even_lsb ?zero" by simp
  show ?thesis
  proof (cases rm)
    case RNE
    have "fp_round_rel IEEE.RNE (valof ?zero) ?zero"
      by (rule fp_round_RNE_exact_even[OF strict_width finite even])
    with exact RNE show ?thesis by simp
  next
    case RNA
    have "fp_round_rel IEEE.RNA (valof ?zero) ?zero"
      by (rule fp_round_RNA_exact[OF strict_width finite])
    with exact RNA show ?thesis by simp
  next
    case RTZ
    have "fp_round_rel IEEE.RTZ (valof ?zero) ?zero"
      by (rule fp_round_RTZ_exact[OF finite])
    with exact RTZ show ?thesis by simp
  next
    case RTP
    have "fp_round_rel IEEE.RTP (valof ?zero) ?zero"
      by (rule fp_round_RTP_exact[OF strict_width finite])
    with exact RTP show ?thesis by simp
  next
    case RTN
    have "fp_round_rel IEEE.RTN (valof ?zero) ?zero"
      by (rule fp_round_RTN_exact[OF strict_width finite])
    with exact RTN show ?thesis by simp
  qed
qed

theorem round_zero_ap_binary_signed_sound:
  fixes rm :: fp_round_mode and x :: ap_binary_float
  assumes width: "2 \<le> LENGTH('e::len)"
      and zero: "ap_is_zero x"
  shows
    "fp_signed_round_rel (ieee_round_mode rm) (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result rm x ::
        ('e, 'f::len) floatSingleNaN)"
proof -
  have source_zero: "of_rat (ap_binary_value x) = (0 :: real)"
    using zero by simp
  have result_zero:
    "(total_ap_afp_result rm x :: ('e, 'f) floatSingleNaN) =
      fp_zero_with_sign (ap_negative x)"
    by (rule total_ap_afp_result_zero[OF zero])
  have rounded:
    "fp_round_rel (ieee_round_mode rm) 0
      (fp_zero_with_sign (ap_negative x) ::
        ('e, 'f) floatSingleNaN)"
    by (rule fp_round_zero_with_sign[OF width])
  show ?thesis
    unfolding fp_signed_round_rel_def source_zero result_zero
    using rounded by simp
qed

corollary round_zero_ap_binary_RNE_signed_sound:
  assumes "2 \<le> LENGTH('e::len)" "ap_is_zero x"
  shows
    "fp_signed_round_rel IEEE.RNE (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RNE x ::
        ('e, 'f::len) floatSingleNaN)"
  using round_zero_ap_binary_signed_sound[
    of x Fp_Round_Int.RNE, OF assms] by simp

corollary round_zero_ap_binary_RNA_signed_sound:
  assumes "2 \<le> LENGTH('e::len)" "ap_is_zero x"
  shows
    "fp_signed_round_rel IEEE.RNA (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RNA x ::
        ('e, 'f::len) floatSingleNaN)"
  using round_zero_ap_binary_signed_sound[
    of x Fp_Round_Int.RNA, OF assms] by simp

corollary round_zero_ap_binary_RTZ_signed_sound:
  assumes "2 \<le> LENGTH('e::len)" "ap_is_zero x"
  shows
    "fp_signed_round_rel IEEE.RTZ (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTZ x ::
        ('e, 'f::len) floatSingleNaN)"
  using round_zero_ap_binary_signed_sound[
    of x Fp_Round_Int.RTZ, OF assms] by simp

corollary round_zero_ap_binary_RTP_signed_sound:
  assumes "2 \<le> LENGTH('e::len)" "ap_is_zero x"
  shows
    "fp_signed_round_rel IEEE.RTP (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTP x ::
        ('e, 'f::len) floatSingleNaN)"
  using round_zero_ap_binary_signed_sound[
    of x Fp_Round_Int.RTP, OF assms] by simp

corollary round_zero_ap_binary_RTN_signed_sound:
  assumes "2 \<le> LENGTH('e::len)" "ap_is_zero x"
  shows
    "fp_signed_round_rel IEEE.RTN (ap_negative x)
      (of_rat (ap_binary_value x))
      (total_ap_afp_result Fp_Round_Int.RTN x ::
        ('e, 'f::len) floatSingleNaN)"
  using round_zero_ap_binary_signed_sound[
    of x Fp_Round_Int.RTN, OF assms] by simp

section \<open>Mathematical source special values\<close>

text \<open>
  This datatype adds the three non-finite source classes without choosing a
  NaN payload.  That matches the AFP destination quotient, where all NaN
  encodings are identified.  It is not a model of any particular Rust or MPFR
  object representation.
\<close>

datatype ap_binary_source =
    AP_Finite ap_binary_float
  | AP_Infinity bool
  | AP_NaN

fun total_ap_source_result ::
    "fp_round_mode \<Rightarrow> ap_binary_source \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN" where
  "total_ap_source_result rm (AP_Finite x) = total_ap_afp_result rm x"
| "total_ap_source_result rm (AP_Infinity False) = plus_infinity"
| "total_ap_source_result rm (AP_Infinity True) = minus_infinity"
| "total_ap_source_result rm AP_NaN = NaN"

lemma total_ap_source_result_nan:
  "(total_ap_source_result rm AP_NaN ::
    ('e::len, 'f::len) floatSingleNaN) = NaN"
  by simp

lemma total_ap_source_result_plus_infinity:
  "(total_ap_source_result rm (AP_Infinity False) ::
    ('e::len, 'f::len) floatSingleNaN) = plus_infinity"
  by simp

lemma total_ap_source_result_minus_infinity:
  "(total_ap_source_result rm (AP_Infinity True) ::
    ('e::len, 'f::len) floatSingleNaN) = minus_infinity"
  by simp

end

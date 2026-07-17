(* SPDX-License-Identifier: MIT *)

section \<open>Sound rounding at finite and overflow boundaries\<close>

theory Fp_Round_Nearest_Sound
  imports Fp_Round_Overflow Fp_Round_Preference Fp_Round_Sound
begin

lemma runtime_float_of_runtime_bits [simp]:
  "runtime_float_of_bits (runtime_bits x) = x"
proof (cases x)
  case (Abs_float y)
  then obtain s e frac where y: "y = (s, e, frac)"
    by (cases y) auto
  have sign_cases: "s = 0 \<or> s = 1"
    by (rule degenerate_word) simp
  show ?thesis
    unfolding Abs_float y runtime_float_of_bits_def runtime_bits_def
    using sign_cases
    by (elim disjE;
        simp add: IEEE.sign.rep_eq IEEE.exponent.rep_eq IEEE.fraction.rep_eq
          IEEE.Abs_float_inverse)
qed

lemma runtime_float_of_infinity_bits:
  "(runtime_float_of_bits
      (infinity_bits (runtime_format TYPE(('e::len, 'f::len) float)) negative) ::
      ('e, 'f) float) =
    (if negative then IEEE.minus_infinity else IEEE.plus_infinity)"
proof (cases negative)
  case True
  have "infinity_bits (runtime_format TYPE(('e, 'f) float)) True =
      runtime_bits (IEEE.minus_infinity :: ('e, 'f) float)"
    using runtime_bits_minus_infinity[where 'e='e and 'f='f] by simp
  with True show ?thesis by simp
next
  case False
  have "infinity_bits (runtime_format TYPE(('e, 'f) float)) False =
      runtime_bits (IEEE.plus_infinity :: ('e, 'f) float)"
    using runtime_bits_plus_infinity[where 'e='e and 'f='f] by simp
  with False show ?thesis by simp
qed

lemma runtime_float_of_maximum_finite_bits:
  "(runtime_float_of_bits
      (maximum_finite_bits
        (runtime_format TYPE(('e::len, 'f::len) float)) negative) ::
      ('e, 'f) float) =
    (if negative then IEEE.bottomfloat else IEEE.topfloat)"
proof (cases negative)
  case True
  have "maximum_finite_bits
      (runtime_format TYPE(('e, 'f) float)) True =
      runtime_bits (IEEE.bottomfloat :: ('e, 'f) float)"
    using runtime_bits_bottomfloat[where 'e='e and 'f='f] by simp
  with True show ?thesis by simp
next
  case False
  have "maximum_finite_bits
      (runtime_format TYPE(('e, 'f) float)) False =
      runtime_bits (IEEE.topfloat :: ('e, 'f) float)"
    using runtime_bits_topfloat[where 'e='e and 'f='f] by simp
  with False show ?thesis by simp
qed

lemma single_nan_of_float_plus_infinity [simp]:
  "single_nan_of_float
      (IEEE.plus_infinity :: ('e::len, 'f::len) float) =
    (plus_infinity :: ('e, 'f) floatSingleNaN)"
  unfolding single_nan_of_float_def
  by (rule plus_infinity.abs_eq[symmetric])

lemma single_nan_of_float_minus_infinity [simp]:
  "single_nan_of_float
      (IEEE.minus_infinity :: ('e::len, 'f::len) float) =
    (minus_infinity :: ('e, 'f) floatSingleNaN)"
  unfolding single_nan_of_float_def
  by (rule minus_infinity.abs_eq[symmetric])

lemma fp_plus_infinity_not_finite [simp]:
  "\<not> is_finite
    (plus_infinity :: ('e::len, 'f::len) floatSingleNaN)"
  by transfer simp

lemma fp_minus_infinity_not_finite [simp]:
  "\<not> is_finite
    (minus_infinity :: ('e::len, 'f::len) floatSingleNaN)"
  by transfer simp

lemma afp_rational_result_nearest_overflow:
  fixes rm :: fp_round_mode
  assumes width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and threshold:
        "format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f::len) float)) \<le>
         exact_magnitude n d"
  shows
    "(afp_rational_result rm negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then minus_infinity else plus_infinity)"
proof -
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  have valid: "valid_format ?f"
    by (rule runtime_format_valid[OF width])
  have bits:
      "round_rational_to_format_bits ?f rm negative n d =
        infinity_bits ?f negative"
    by (rule round_rational_to_format_bits_nearest_overflow[
          OF valid numerator denominator nearest threshold])
  have raw:
      "(afp_round_rational rm negative n d :: ('e, 'f) float) =
        (if negative then IEEE.minus_infinity else IEEE.plus_infinity)"
    unfolding afp_round_rational_def
    using bits runtime_float_of_infinity_bits[where 'e='e and 'f='f]
    by simp
  show ?thesis
    unfolding afp_rational_result_def raw by simp
qed

lemma afp_rational_result_directed_above_maximum:
  assumes width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and above:
        "format_maximum_finite_magnitude
          (runtime_format TYPE(('e, 'f::len) float)) <
         exact_magnitude n d"
  shows
    "(afp_rational_result Fp_Round_Int.RTP negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then fp_bottom_finite else plus_infinity)"
    "(afp_rational_result Fp_Round_Int.RTN negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then minus_infinity else fp_top_finite)"
    "(afp_rational_result Fp_Round_Int.RTZ negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then fp_bottom_finite else fp_top_finite)"
proof -
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  have valid: "valid_format ?f"
    by (rule runtime_format_valid[OF width])
  note bits = round_rational_to_format_bits_directed_above_maximum[
    OF valid numerator denominator above]
  show "(afp_rational_result Fp_Round_Int.RTP negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then fp_bottom_finite else plus_infinity)"
    unfolding afp_rational_result_def afp_round_rational_def
    using bits(1)
    by (cases negative)
      (simp_all add: runtime_float_of_maximum_finite_bits
        runtime_float_of_infinity_bits fp_bottom_finite_def)
  show "(afp_rational_result Fp_Round_Int.RTN negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then minus_infinity else fp_top_finite)"
    unfolding afp_rational_result_def afp_round_rational_def
    using bits(2)
    by (cases negative)
      (simp_all add: runtime_float_of_maximum_finite_bits
        runtime_float_of_infinity_bits fp_top_finite_def)
  show "(afp_rational_result Fp_Round_Int.RTZ negative n d ::
        ('e, 'f) floatSingleNaN) =
      (if negative then fp_bottom_finite else fp_top_finite)"
    unfolding afp_rational_result_def afp_round_rational_def
    using bits(3)
    by (cases negative)
      (simp_all add: runtime_float_of_maximum_finite_bits
        fp_bottom_finite_def fp_top_finite_def)
qed

theorem afp_round_rational_directed_above_maximum_sound:
  assumes width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and above:
        "format_maximum_finite_magnitude
          (runtime_format TYPE(('e, 'f::len) float)) <
         exact_magnitude n d"
  shows
    "fp_round_rel IEEE.RTP
      (of_rat (exact_input_value negative n d))
      (afp_rational_result Fp_Round_Int.RTP negative n d ::
        ('e, 'f) floatSingleNaN)"
    "fp_round_rel IEEE.RTN
      (of_rat (exact_input_value negative n d))
      (afp_rational_result Fp_Round_Int.RTN negative n d ::
        ('e, 'f) floatSingleNaN)"
    "fp_round_rel IEEE.RTZ
      (of_rat (exact_input_value negative n d))
      (afp_rational_result Fp_Round_Int.RTZ negative n d ::
        ('e, 'f) floatSingleNaN)"
proof -
  let ?exact = "(of_rat (exact_input_value negative n d) :: real)"
  let ?largest = "fp_largest TYPE(('e, 'f) floatSingleNaN)"
  have cast_above:
      "?largest < (of_rat (exact_magnitude n d) :: real)"
  proof -
    have "(of_rat (format_maximum_finite_magnitude
        (runtime_format TYPE(('e, 'f) float))) :: real) <
      of_rat (exact_magnitude n d)"
      using above by (simp only: of_rat_less)
    moreover have "(of_rat (format_maximum_finite_magnitude
        (runtime_format TYPE(('e, 'f) float))) :: real) = ?largest"
      by (rule runtime_format_maximum_finite_magnitude)
        (use width in simp)
    ultimately show ?thesis by simp
  qed
  note results = afp_rational_result_directed_above_maximum[
    OF width numerator denominator above]
  show "fp_round_rel IEEE.RTP ?exact
      (afp_rational_result Fp_Round_Int.RTP negative n d ::
        ('e, 'f) floatSingleNaN)"
  proof (cases negative)
    case True
    have below: "?exact < - ?largest"
      using cast_above True
      by (simp add: exact_input_value_as_magnitude signed_rat_def
          of_rat_minus)
    show ?thesis
      using fp_round_RTP_below_minus_largest[OF _ below]
        width results(1) True by simp
  next
    case False
    have above_real: "?largest < ?exact"
      using cast_above False
      by (simp add: exact_input_value_as_magnitude signed_rat_def)
    show ?thesis using fp_round_RTP_above_largest[OF above_real]
      results(1) False by simp
  qed
  show "fp_round_rel IEEE.RTN ?exact
      (afp_rational_result Fp_Round_Int.RTN negative n d ::
        ('e, 'f) floatSingleNaN)"
  proof (cases negative)
    case True
    have below: "?exact < - ?largest"
      using cast_above True
      by (simp add: exact_input_value_as_magnitude signed_rat_def
          of_rat_minus)
    show ?thesis using fp_round_RTN_below_minus_largest[OF below]
      results(2) True by simp
  next
    case False
    have above_real: "?largest < ?exact"
      using cast_above False
      by (simp add: exact_input_value_as_magnitude signed_rat_def)
    show ?thesis
      using fp_round_RTN_above_largest[OF _ above_real]
        width results(2) False by simp
  qed
  show "fp_round_rel IEEE.RTZ ?exact
      (afp_rational_result Fp_Round_Int.RTZ negative n d ::
        ('e, 'f) floatSingleNaN)"
  proof (cases negative)
    case True
    have below: "?exact < - ?largest"
      using cast_above True
      by (simp add: exact_input_value_as_magnitude signed_rat_def
          of_rat_minus)
    show ?thesis
      using fp_round_RTZ_below_minus_largest[OF _ below]
        width results(3) True by simp
  next
    case False
    have above_real: "?largest < ?exact"
      using cast_above False
      by (simp add: exact_input_value_as_magnitude signed_rat_def)
    show ?thesis
      using fp_round_RTZ_above_largest[OF _ above_real]
        width results(3) False by simp
  qed
qed

theorem afp_round_rational_nearest_overflow_sound:
  fixes rm :: fp_round_mode
    and negative :: bool and n d :: nat
    and result :: "('e::len, 'f::len) floatSingleNaN"
    and exact :: real
  defines result: "result \<equiv>
      (afp_rational_result rm negative n d ::
        ('e, 'f) floatSingleNaN)"
      and exact: "exact \<equiv>
        of_rat (exact_input_value negative n d)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and threshold:
        "format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f) float)) \<le>
         exact_magnitude n d"
  shows "fp_round_rel (ieee_round_mode rm) exact result"
proof -
  have result_infinity:
      "result = (if negative then minus_infinity else plus_infinity)"
    unfolding result
    by (rule afp_rational_result_nearest_overflow[
          OF width numerator denominator nearest threshold])
  have cast_threshold:
      "(of_rat (format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f) float))) :: real) \<le>
       of_rat (exact_magnitude n d)"
    using threshold by (simp only: of_rat_less_eq)
  have threshold_bound:
      "fp_threshold TYPE(('e, 'f) floatSingleNaN) \<le>
       of_rat (exact_magnitude n d)"
    using cast_threshold
    by (simp only: runtime_format_nearest_overflow_threshold)
  have exact_signed:
      "exact = of_rat (signed_rat negative (exact_magnitude n d))"
    unfolding exact exact_input_value_as_magnitude by simp
  have threshold_pos:
      "0 < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_threshold_pos) (use width in simp)
  consider (RNE) "rm = Fp_Round_Int.RNE"
    | (RNA) "rm = Fp_Round_Int.RNA"
    using nearest by blast
  then show ?thesis
  proof cases
    case RNE
    show ?thesis
    proof (cases negative)
      case True
      have below:
          "exact \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)"
        using threshold_bound exact_signed True
        by (simp add: signed_rat_def of_rat_minus; linarith)
      show ?thesis using RNE True result_infinity below by simp
    next
      case False
      have above:
          "fp_threshold TYPE(('e, 'f) floatSingleNaN) \<le> exact"
        using threshold_bound exact_signed False
        by (simp add: signed_rat_def of_rat_minus)
      have not_below:
          "\<not> exact \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)"
        using threshold_pos above by linarith
      show ?thesis
        using RNE False result_infinity above not_below by simp
    qed
  next
    case RNA
    show ?thesis
    proof (cases negative)
      case True
      have below:
          "exact \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)"
        using threshold_bound exact_signed True
        by (simp add: signed_rat_def of_rat_minus; linarith)
      show ?thesis using RNA True result_infinity below by simp
    next
      case False
      have above:
          "fp_threshold TYPE(('e, 'f) floatSingleNaN) \<le> exact"
        using threshold_bound exact_signed False
        by (simp add: signed_rat_def of_rat_minus)
      have not_below:
          "\<not> exact \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)"
        using threshold_pos above by linarith
      show ?thesis
        using RNA False result_infinity above not_below by simp
    qed
  qed
qed

lemma afp_rational_result_finite_below_nearest_threshold:
  fixes rm :: fp_round_mode
  assumes width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and finite:
        "is_finite (afp_rational_result rm negative n d ::
          ('e, 'f::len) floatSingleNaN)"
  shows
    "exact_magnitude n d <
      format_nearest_overflow_threshold
        (runtime_format TYPE(('e, 'f) float))"
proof (rule ccontr)
  assume not_below: "\<not> exact_magnitude n d <
      format_nearest_overflow_threshold
        (runtime_format TYPE(('e, 'f) float))"
  have threshold:
      "format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f) float)) \<le>
       exact_magnitude n d"
    using not_below by simp
  have infinity:
      "(afp_rational_result rm negative n d ::
          ('e, 'f) floatSingleNaN) =
       (if negative then minus_infinity else plus_infinity)"
    by (rule afp_rational_result_nearest_overflow[
          OF width numerator denominator nearest threshold])
  show False using finite infinity by (cases negative) simp_all
qed

theorem afp_round_rational_subnormal_nearest_sound:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
    and exact :: real
  defines f: "f \<equiv> runtime_format TYPE(('e, 'f) float)"
      and result: "result \<equiv>
        (afp_rational_result rm negative n d ::
          ('e, 'f) floatSingleNaN)"
      and exact: "exact \<equiv>
        of_rat (exact_input_value negative n d)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and nearest:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and subnormal: "floor_log2_spec n d < format_emin f"
  shows "fp_round_rel (ieee_round_mode rm) exact result"
proof -
  have preferred:
      "if rm = Fp_Round_Int.RNE then
         fp_preferred_nearest fp_even_lsb exact result
       else
         fp_preferred_nearest
           (\<lambda>b. \<bar>valof b\<bar> \<ge> \<bar>exact\<bar>) exact result"
  proof (cases "rm = Fp_Round_Int.RNE")
    case True
    have rne:
        "fp_preferred_nearest fp_even_lsb
          (of_rat (exact_input_value negative n d))
          (afp_rational_result Fp_Round_Int.RNE negative n d ::
            ('e, 'f) floatSingleNaN)"
      unfolding f afp_rational_result_def
      by (rule afp_round_rational_subnormal_RNE_preferred_nearest[
            OF width numerator denominator subnormal[unfolded f]])
    show ?thesis using True rne by (simp add: result exact)
  next
    case False
    with nearest have mode: "rm = Fp_Round_Int.RNA" by blast
    have rna:
        "fp_preferred_nearest
          (\<lambda>b. \<bar>valof b\<bar> \<ge>
            \<bar>of_rat (exact_input_value negative n d)\<bar>)
          (of_rat (exact_input_value negative n d))
          (afp_rational_result Fp_Round_Int.RNA negative n d ::
            ('e, 'f) floatSingleNaN)"
      unfolding f afp_rational_result_def
      by (rule afp_round_rational_subnormal_RNA_preferred_nearest[
            OF width numerator denominator subnormal[unfolded f]])
    show ?thesis using False mode rna by (simp add: result exact)
  qed
  have finite: "is_finite result"
    using preferred
    by (auto simp: fp_preferred_nearest_def fp_nearest_finite_def
        split: if_splits)
  have magnitude_below:
      "exact_magnitude n d < format_nearest_overflow_threshold f"
    unfolding f
    by (rule afp_rational_result_finite_below_nearest_threshold[
          OF width numerator denominator nearest finite[unfolded result]])
  have cast_below:
      "(of_rat (exact_magnitude n d) :: real) <
        fp_threshold TYPE(('e, 'f) floatSingleNaN)"
  proof -
    have "(of_rat (exact_magnitude n d) :: real) <
        of_rat (format_nearest_overflow_threshold
          (runtime_format TYPE(('e, 'f) float)))"
      using magnitude_below[unfolded f] by (simp only: of_rat_less)
    then show ?thesis
      by (simp only: runtime_format_nearest_overflow_threshold)
  qed
  have threshold_pos:
      "0 < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
    by (rule fp_threshold_pos) (use width in simp)
  have magnitude_nonnegative:
      "0 \<le> (of_rat (exact_magnitude n d) :: real)"
    using denominator by (simp add: exact_magnitude_def)
  have exact_signed:
      "exact = of_rat (signed_rat negative (exact_magnitude n d))"
    unfolding exact exact_input_value_as_magnitude by simp
  have lower:
      "- fp_threshold TYPE(('e, 'f) floatSingleNaN) < exact"
  proof (cases negative)
    case True
    show ?thesis
      using cast_below exact_signed True
      by (simp add: signed_rat_def of_rat_minus)
  next
    case False
    show ?thesis
      using threshold_pos magnitude_nonnegative exact_signed False
      by (simp add: signed_rat_def of_rat_minus; linarith)
  qed
  have upper:
      "exact < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
  proof (cases negative)
    case True
    show ?thesis
      using threshold_pos magnitude_nonnegative exact_signed True
      by (simp add: signed_rat_def of_rat_minus; linarith)
  next
    case False
    show ?thesis
      using cast_below exact_signed False
      by (simp add: signed_rat_def of_rat_minus)
  qed
  show ?thesis
    using nearest preferred lower upper
    by (elim disjE; simp)
qed

end

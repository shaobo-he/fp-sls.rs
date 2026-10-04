(* SPDX-License-Identifier: MIT *)

section \<open>Directed rounding of the AFP encoding\<close>

theory Fp_Round_Directed_IEEE
  imports Fp_Round_Nearest_IEEE Fp_Round_Directed
begin

definition afp_rational_result ::
    "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN" where
  "afp_rational_result rm negative n d = single_nan_of_float
    (afp_round_rational rm negative n d :: ('e, 'f) float)"

lemma afp_rational_result_finite_and_value:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f rm negative n d) \<or>
         core_exponent (round_rational_core f rm negative n d) \<le>
           format_emax f"
  shows "is_finite
      (afp_rational_result rm negative n d :: ('e, 'f) floatSingleNaN)"
    and "valof (afp_rational_result rm negative n d ::
          ('e, 'f) floatSingleNaN) =
      of_rat (signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)))"
proof -
  let ?bits = "round_rational_to_format_bits f rm negative n d"
  let ?core = "round_rational_core f rm negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have decoded_core:
    "decode_bits f ?bits =
      Dynamic_Finite negative (rounded_core_magnitude f ?core)"
    by (rule decode_round_rational_to_format_bits_finite[
          OF valid numerator denominator no_overflow])
  have magnitude:
    "finite_magnitude f ?bits = rounded_core_magnitude f ?core"
    using decoded_core
    by (auto simp: decode_bits_def split: if_splits)
  have decoded:
    "decode_bits f ?bits =
      Dynamic_Finite negative (finite_magnitude f ?bits)"
    using decoded_core magnitude by simp
  have decoded_runtime:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
        (round_rational_to_format_bits
          (runtime_format TYPE(('e, 'f) float)) rm negative n d) =
      Dynamic_Finite negative
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (round_rational_to_format_bits
            (runtime_format TYPE(('e, 'f) float)) rm negative n d))"
    using decoded unfolding f .
  show "is_finite
      (afp_rational_result rm negative n d :: ('e, 'f) floatSingleNaN)"
    unfolding afp_rational_result_def
    by (rule afp_round_rational_finite_and_valueI(1)[
          OF width numerator denominator decoded_runtime])
  show "valof (afp_rational_result rm negative n d ::
          ('e, 'f) floatSingleNaN) =
      of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding afp_rational_result_def f
    by (rule afp_round_rational_finite_and_valueI(2)[
          OF width numerator denominator decoded_runtime])
qed

lemma finite_raw_runtime_value:
  fixes y :: "('e::len, 'f::len) float"
  assumes finite: "IEEE.is_finite y"
  shows
    "IEEE.valof y =
      of_rat (signed_rat (IEEE.sign y = 1)
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (runtime_bits y)))"
  using runtime_value_eq_signed_magnitude[of y] by simp

theorem afp_round_rational_RTP_least_finite_above:
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
  shows "fp_least_finite_above exact result"
proof -
  let ?bits = "round_rational_to_format_bits
    f Fp_Round_Int.RTP negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have no_overflow_runtime:
    "core_is_subnormal
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTP negative n d) \<or>
     core_exponent
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTP negative n d) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow unfolding f .
  have finite_result: "is_finite result"
    unfolding result
    by (rule afp_rational_result_finite_and_value(1)[
          OF width numerator denominator no_overflow_runtime])
  have result_value:
    "valof result =
      of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding result f
    by (rule afp_rational_result_finite_and_value(2)[
          OF width numerator denominator no_overflow_runtime])
  have directed_rat:
    "exact_input_value negative n d \<le>
      signed_rat negative (finite_magnitude f ?bits)"
    by (rule round_rational_to_format_bits_RTP_directed_finite[
          OF valid numerator denominator no_overflow])
  have directed_real:
    "exact \<le> valof result"
    unfolding exact result_value
    using directed_rat by (simp only: of_rat_less_eq)
  show ?thesis
    unfolding fp_least_finite_above_def
  proof (intro conjI allI impI)
    show "is_finite result" by (rule finite_result)
    show "exact \<le> valof result" by (rule directed_real)
    fix competitor :: "('e, 'f) floatSingleNaN"
    assume competitor:
      "is_finite competitor \<and> exact \<le> valof competitor"
    from competitor have competitor_finite: "is_finite competitor" by simp
    from competitor have competitor_above: "exact \<le> valof competitor" by simp
    obtain y :: "('e, 'f) float"
      where competitor_rep: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using competitor_finite by (rule finite_single_nan_representation)
    have competitor_value: "valof competitor = IEEE.valof y"
      unfolding competitor_rep by (rule single_nan_of_float_valof[OF y_finite])
    have y_value:
      "IEEE.valof y =
        of_rat (signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)))"
      using finite_raw_runtime_value[OF y_finite] unfolding f .
    have y_well_formed: "bits_well_formed f (runtime_bits y)"
      unfolding f by simp
    have y_exponent:
      "exponent_field (runtime_bits y) < exponent_all_ones f"
      unfolding f by (rule finite_runtime_bits_exponent[OF width y_finite])
    show "valof result \<le> valof competitor"
    proof (cases negative)
      case source_positive: False
      show ?thesis
      proof (cases y rule: sign_cases)
        case pos
        have sign: "(IEEE.sign y = 1) = False"
          using pos by simp
        have competitor_rat:
          "exact_input_value False n d \<le>
            signed_rat False (finite_magnitude f (runtime_bits y))"
          using competitor_above competitor_value y_value source_positive sign
          unfolding exact by (simp only: of_rat_less_eq)
        have no_overflow_false:
          "core_is_subnormal
              (round_rational_core f Fp_Round_Int.RTP False n d) \<or>
           core_exponent
              (round_rational_core f Fp_Round_Int.RTP False n d) \<le>
             format_emax f"
          using no_overflow source_positive by simp
        have least_rat:
          "signed_rat False (finite_magnitude f ?bits) \<le>
            signed_rat False (finite_magnitude f (runtime_bits y))"
        proof -
          have least_false:
            "signed_rat False
                (finite_magnitude f
                  (round_rational_to_format_bits
                    f Fp_Round_Int.RTP False n d)) \<le>
              signed_rat False (finite_magnitude f (runtime_bits y))"
            by (rule round_rational_to_format_bits_RTP_least_finite[
                  OF valid numerator denominator no_overflow_false
                    y_well_formed y_exponent competitor_rat])
          show ?thesis using least_false source_positive by simp
        qed
        have least_real:
          "of_rat (signed_rat False (finite_magnitude f ?bits)) \<le>
            (of_rat (signed_rat False
              (finite_magnitude f (runtime_bits y))) :: real)"
          using least_rat by (simp only: of_rat_less_eq)
        show ?thesis
          using least_real competitor_value y_value source_positive sign
          unfolding result_value by simp
      next
        case neg
        have y_nonpositive: "IEEE.valof y \<le> 0"
          by (rule valof_nonpos[OF neg])
        have input_positive: "0 < exact"
          using numerator denominator source_positive
          by (simp add: exact exact_input_value_def signed_rat_def)
        show ?thesis
          using competitor_above competitor_value input_positive y_nonpositive
          by linarith
      qed
    next
      case source_negative: True
      show ?thesis
      proof (cases y rule: sign_cases)
        case pos
        have result_nonpositive: "valof result \<le> 0"
          using source_negative result_value by (simp add: signed_rat_def)
        have y_nonnegative: "0 \<le> IEEE.valof y"
          by (rule valof_nonneg[OF pos])
        show ?thesis
          using result_nonpositive y_nonnegative competitor_value by linarith
      next
        case neg
        have sign: "(IEEE.sign y = 1) = True"
          using neg by simp
        have competitor_rat:
          "exact_input_value True n d \<le>
            signed_rat True (finite_magnitude f (runtime_bits y))"
          using competitor_above competitor_value y_value source_negative sign
          unfolding exact by (simp only: of_rat_less_eq)
        have no_overflow_true:
          "core_is_subnormal
              (round_rational_core f Fp_Round_Int.RTP True n d) \<or>
           core_exponent
              (round_rational_core f Fp_Round_Int.RTP True n d) \<le>
             format_emax f"
          using no_overflow source_negative by simp
        have least_rat:
          "signed_rat True (finite_magnitude f ?bits) \<le>
            signed_rat True (finite_magnitude f (runtime_bits y))"
        proof -
          have least_true:
            "signed_rat True
                (finite_magnitude f
                  (round_rational_to_format_bits
                    f Fp_Round_Int.RTP True n d)) \<le>
              signed_rat True (finite_magnitude f (runtime_bits y))"
            by (rule round_rational_to_format_bits_RTP_least_finite[
                  OF valid numerator denominator no_overflow_true
                    y_well_formed y_exponent competitor_rat])
          show ?thesis using least_true source_negative by simp
        qed
        have least_real:
          "of_rat (signed_rat True (finite_magnitude f ?bits)) \<le>
            (of_rat (signed_rat True
              (finite_magnitude f (runtime_bits y))) :: real)"
          using least_rat by (simp only: of_rat_less_eq)
        show ?thesis
          using least_real competitor_value y_value source_negative sign
          unfolding result_value by simp
      qed
    qed
  qed
qed

theorem afp_round_rational_RTN_greatest_finite_below:
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
  shows "fp_greatest_finite_below exact result"
proof -
  let ?bits = "round_rational_to_format_bits
    f Fp_Round_Int.RTN negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have no_overflow_runtime:
    "core_is_subnormal
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTN negative n d) \<or>
     core_exponent
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTN negative n d) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow unfolding f .
  have finite_result: "is_finite result"
    unfolding result
    by (rule afp_rational_result_finite_and_value(1)[
          OF width numerator denominator no_overflow_runtime])
  have result_value:
    "valof result =
      of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding result f
    by (rule afp_rational_result_finite_and_value(2)[
          OF width numerator denominator no_overflow_runtime])
  have directed_rat:
    "signed_rat negative (finite_magnitude f ?bits) \<le>
      exact_input_value negative n d"
    by (rule round_rational_to_format_bits_RTN_directed_finite[
          OF valid numerator denominator no_overflow])
  have directed_real: "valof result \<le> exact"
    unfolding exact result_value
    using directed_rat by (simp only: of_rat_less_eq)
  show ?thesis
    unfolding fp_greatest_finite_below_def
  proof (intro conjI allI impI)
    show "is_finite result" by (rule finite_result)
    show "valof result \<le> exact" by (rule directed_real)
    fix competitor :: "('e, 'f) floatSingleNaN"
    assume competitor:
      "is_finite competitor \<and> valof competitor \<le> exact"
    from competitor have competitor_finite: "is_finite competitor" by simp
    from competitor have competitor_below: "valof competitor \<le> exact" by simp
    obtain y :: "('e, 'f) float"
      where competitor_rep: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using competitor_finite by (rule finite_single_nan_representation)
    have competitor_value: "valof competitor = IEEE.valof y"
      unfolding competitor_rep by (rule single_nan_of_float_valof[OF y_finite])
    have y_value:
      "IEEE.valof y =
        of_rat (signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)))"
      using finite_raw_runtime_value[OF y_finite] unfolding f .
    have y_well_formed: "bits_well_formed f (runtime_bits y)"
      unfolding f by simp
    have y_exponent:
      "exponent_field (runtime_bits y) < exponent_all_ones f"
      unfolding f by (rule finite_runtime_bits_exponent[OF width y_finite])
    show "valof competitor \<le> valof result"
    proof (cases negative)
      case source_positive: False
      show ?thesis
      proof (cases y rule: sign_cases)
        case pos
        have sign: "(IEEE.sign y = 1) = False"
          using pos by simp
        have competitor_rat:
          "signed_rat False (finite_magnitude f (runtime_bits y)) \<le>
            exact_input_value False n d"
          using competitor_below competitor_value y_value source_positive sign
          unfolding exact by (simp only: of_rat_less_eq)
        have no_overflow_false:
          "core_is_subnormal
              (round_rational_core f Fp_Round_Int.RTN False n d) \<or>
           core_exponent
              (round_rational_core f Fp_Round_Int.RTN False n d) \<le>
             format_emax f"
          using no_overflow source_positive by simp
        have greatest_rat:
          "signed_rat False (finite_magnitude f (runtime_bits y)) \<le>
            signed_rat False (finite_magnitude f ?bits)"
        proof -
          have greatest_false:
            "signed_rat False (finite_magnitude f (runtime_bits y)) \<le>
              signed_rat False
                (finite_magnitude f
                  (round_rational_to_format_bits
                    f Fp_Round_Int.RTN False n d))"
            by (rule round_rational_to_format_bits_RTN_greatest_finite[
                  OF valid numerator denominator no_overflow_false
                    y_well_formed y_exponent competitor_rat])
          show ?thesis using greatest_false source_positive by simp
        qed
        have greatest_real:
          "of_rat (signed_rat False
              (finite_magnitude f (runtime_bits y))) \<le>
            (of_rat (signed_rat False (finite_magnitude f ?bits)) :: real)"
          using greatest_rat by (simp only: of_rat_less_eq)
        show ?thesis
          using greatest_real competitor_value y_value source_positive sign
          unfolding result_value by simp
      next
        case neg
        have y_nonpositive: "IEEE.valof y \<le> 0"
          by (rule valof_nonpos[OF neg])
        have result_nonnegative: "0 \<le> valof result"
          using source_positive result_value by (simp add: signed_rat_def)
        show ?thesis
          using y_nonpositive result_nonnegative competitor_value by linarith
      qed
    next
      case source_negative: True
      show ?thesis
      proof (cases y rule: sign_cases)
        case pos
        have y_nonnegative: "0 \<le> IEEE.valof y"
          by (rule valof_nonneg[OF pos])
        have input_negative: "exact < 0"
          using numerator denominator source_negative
          by (simp add: exact exact_input_value_def signed_rat_def)
        show ?thesis
          using competitor_below competitor_value input_negative y_nonnegative
          by linarith
      next
        case neg
        have sign: "(IEEE.sign y = 1) = True"
          using neg by simp
        have competitor_rat:
          "signed_rat True (finite_magnitude f (runtime_bits y)) \<le>
            exact_input_value True n d"
          using competitor_below competitor_value y_value source_negative sign
          unfolding exact by (simp only: of_rat_less_eq)
        have no_overflow_true:
          "core_is_subnormal
              (round_rational_core f Fp_Round_Int.RTN True n d) \<or>
           core_exponent
              (round_rational_core f Fp_Round_Int.RTN True n d) \<le>
             format_emax f"
          using no_overflow source_negative by simp
        have greatest_rat:
          "signed_rat True (finite_magnitude f (runtime_bits y)) \<le>
            signed_rat True (finite_magnitude f ?bits)"
        proof -
          have greatest_true:
            "signed_rat True (finite_magnitude f (runtime_bits y)) \<le>
              signed_rat True
                (finite_magnitude f
                  (round_rational_to_format_bits
                    f Fp_Round_Int.RTN True n d))"
            by (rule round_rational_to_format_bits_RTN_greatest_finite[
                  OF valid numerator denominator no_overflow_true
                    y_well_formed y_exponent competitor_rat])
          show ?thesis using greatest_true source_negative by simp
        qed
        have greatest_real:
          "of_rat (signed_rat True
              (finite_magnitude f (runtime_bits y))) \<le>
            (of_rat (signed_rat True (finite_magnitude f ?bits)) :: real)"
          using greatest_rat by (simp only: of_rat_less_eq)
        show ?thesis
          using greatest_real competitor_value y_value source_negative sign
          unfolding result_value by simp
      qed
    qed
  qed
qed

theorem afp_round_rational_RTZ_extremal:
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
  shows
    "if negative then fp_least_finite_above exact result
     else fp_greatest_finite_below exact result"
proof -
  let ?bits = "round_rational_to_format_bits
    f Fp_Round_Int.RTZ negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have no_overflow_runtime:
    "core_is_subnormal
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTZ negative n d) \<or>
     core_exponent
        (round_rational_core
          (runtime_format TYPE(('e, 'f) float))
          Fp_Round_Int.RTZ negative n d) \<le>
       format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow unfolding f .
  have finite_result: "is_finite result"
    unfolding result
    by (rule afp_rational_result_finite_and_value(1)[
          OF width numerator denominator no_overflow_runtime])
  have result_value:
    "valof result =
      of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding result f
    by (rule afp_rational_result_finite_and_value(2)[
          OF width numerator denominator no_overflow_runtime])
  have directed_rat:
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat negative (finite_magnitude f ?bits)
     else
       signed_rat negative (finite_magnitude f ?bits) \<le>
         exact_input_value negative n d"
    by (rule round_rational_to_format_bits_RTZ_directed_finite[
          OF valid numerator denominator no_overflow])
  show ?thesis
  proof (cases negative)
    case source_negative: True
    have negative_eq: "negative = True"
      using source_negative by simp
    have directed_true:
      "exact \<le> valof result"
      using directed_rat source_negative
      unfolding exact result_value by (simp only: if_True of_rat_less_eq)
    show ?thesis
      unfolding negative_eq if_True fp_least_finite_above_def
    proof (intro conjI allI impI)
      show "is_finite result" by (rule finite_result)
      show "exact \<le> valof result" by (rule directed_true)
      fix competitor :: "('e, 'f) floatSingleNaN"
      assume competitor:
        "is_finite competitor \<and> exact \<le> valof competitor"
      from competitor have competitor_finite: "is_finite competitor" by simp
      from competitor have competitor_above: "exact \<le> valof competitor" by simp
      obtain y :: "('e, 'f) float"
        where competitor_rep: "competitor = single_nan_of_float y"
          and y_finite: "IEEE.is_finite y"
        using competitor_finite by (rule finite_single_nan_representation)
      have competitor_value: "valof competitor = IEEE.valof y"
        unfolding competitor_rep
        by (rule single_nan_of_float_valof[OF y_finite])
      have y_value:
        "IEEE.valof y =
          of_rat (signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y)))"
        using finite_raw_runtime_value[OF y_finite]
        unfolding f by simp
      have y_well_formed: "bits_well_formed f (runtime_bits y)"
        unfolding f by simp
      have y_exponent:
        "exponent_field (runtime_bits y) < exponent_all_ones f"
        unfolding f by (rule finite_runtime_bits_exponent[OF width y_finite])
      have competitor_rat:
        "exact_input_value True n d \<le>
          signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y))"
        using competitor_above competitor_value y_value source_negative
        unfolding exact by (simp only: of_rat_less_eq)
      have extremal:
        "signed_rat (negative_bit ?bits) (finite_magnitude f ?bits) \<le>
          signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y))"
        using round_rational_to_format_bits_RTZ_extremal_finite_bits[
            OF valid numerator denominator no_overflow y_well_formed y_exponent]
          competitor_rat source_negative
        by simp
      have extremal_real:
        "of_rat (signed_rat True (finite_magnitude f ?bits)) \<le>
          (of_rat (signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y))) :: real)"
        using extremal source_negative by (simp only:
          round_rational_to_format_bits_negative_bit of_rat_less_eq)
      show "valof result \<le> valof competitor"
        using extremal_real result_value competitor_value y_value
          source_negative by simp
    qed
  next
    case source_positive: False
    have negative_eq: "negative = False"
      using source_positive by simp
    have directed_false:
      "valof result \<le> exact"
      using directed_rat source_positive
      unfolding exact result_value by (simp only: if_False of_rat_less_eq)
    show ?thesis
      unfolding negative_eq if_False fp_greatest_finite_below_def
    proof (intro conjI allI impI)
      show "is_finite result" by (rule finite_result)
      show "valof result \<le> exact" by (rule directed_false)
      fix competitor :: "('e, 'f) floatSingleNaN"
      assume competitor:
        "is_finite competitor \<and> valof competitor \<le> exact"
      from competitor have competitor_finite: "is_finite competitor" by simp
      from competitor have competitor_below: "valof competitor \<le> exact" by simp
      obtain y :: "('e, 'f) float"
        where competitor_rep: "competitor = single_nan_of_float y"
          and y_finite: "IEEE.is_finite y"
        using competitor_finite by (rule finite_single_nan_representation)
      have competitor_value: "valof competitor = IEEE.valof y"
        unfolding competitor_rep
        by (rule single_nan_of_float_valof[OF y_finite])
      have y_value:
        "IEEE.valof y =
          of_rat (signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y)))"
        using finite_raw_runtime_value[OF y_finite]
        unfolding f by simp
      have y_well_formed: "bits_well_formed f (runtime_bits y)"
        unfolding f by simp
      have y_exponent:
        "exponent_field (runtime_bits y) < exponent_all_ones f"
        unfolding f by (rule finite_runtime_bits_exponent[OF width y_finite])
      have competitor_rat:
        "signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y)) \<le>
          exact_input_value False n d"
        using competitor_below competitor_value y_value source_positive
        unfolding exact by (simp only: of_rat_less_eq)
      have extremal:
        "signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y)) \<le>
          signed_rat (negative_bit ?bits) (finite_magnitude f ?bits)"
        using round_rational_to_format_bits_RTZ_extremal_finite_bits[
            OF valid numerator denominator no_overflow y_well_formed y_exponent]
          competitor_rat source_positive
        by simp
      have extremal_real:
        "of_rat (signed_rat (negative_bit (runtime_bits y))
            (finite_magnitude f (runtime_bits y))) \<le>
          (of_rat (signed_rat False (finite_magnitude f ?bits)) :: real)"
        using extremal source_positive by (simp only:
          round_rational_to_format_bits_negative_bit of_rat_less_eq)
      show "valof competitor \<le> valof result"
        using extremal_real result_value competitor_value y_value
          source_positive by simp
    qed
  qed
qed

end

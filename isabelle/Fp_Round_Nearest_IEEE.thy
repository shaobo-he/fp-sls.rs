(* SPDX-License-Identifier: MIT *)

section \<open>Global nearestness of the AFP encoding\<close>

theory Fp_Round_Nearest_IEEE
  imports
    Fp_Round_IEEE
    Fp_Round_Normal
    Fp_Round_Subnormal
    Fp_Signed_Value
begin

text \<open>
  The normal and subnormal developments establish optimality against dynamic
  bit records of the input's sign.  This theory performs the two remaining
  representation-independent steps: finite AFP values are represented by
  well-formed dynamic records, and changing an opposite-sign competitor to
  the input sign cannot make it farther away.
\<close>

lemma finite_runtime_bits_exponent:
  fixes y :: "('e::len, 'f::len) float"
  assumes width: "2 \<le> LENGTH('e)"
      and finite: "IEEE.is_finite y"
  shows
    "exponent_field (runtime_bits y) <
      exponent_all_ones (runtime_format TYPE(('e, 'f) float))"
proof -
  let ?f = "runtime_format TYPE(('e, 'f) float)"
  have valid: "valid_format ?f"
    by (rule runtime_format_valid[OF width])
  have special_positive: "0 < exponent_all_ones ?f"
    by (rule exponent_all_ones_pos)
      (use valid in \<open>simp add: valid_format_def\<close>)
  have exponent_le:
    "IEEE.exponent y \<le> IEEE.emax TYPE(('e, 'f) float) - 1"
    by (rule float_exp_le[OF finite])
  have emax_positive:
    "0 < IEEE.emax TYPE(('e, 'f) float)"
    using special_positive by simp
  have exponent_lt:
    "IEEE.exponent y < IEEE.emax TYPE(('e, 'f) float)"
  proof -
    obtain k where emax:
      "IEEE.emax TYPE(('e, 'f) float) = Suc k"
      using emax_positive by (cases "IEEE.emax TYPE(('e, 'f) float)") auto
    show ?thesis using exponent_le by (simp add: emax)
  qed
  show ?thesis
    using exponent_lt by simp
qed

lemma decoded_runtime_bits_finite:
  fixes y :: "('e::len, 'f::len) float"
  assumes decoded:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
      (runtime_bits y) = Dynamic_Finite negative magnitude"
  shows "IEEE.is_finite y"
proof -
  have not_nan: "\<not> IEEE.is_nan y"
  proof
    assume nan: "IEEE.is_nan y"
    have "decode_bits (runtime_format TYPE(('e, 'f) float))
        (runtime_bits y) = Dynamic_NaN"
      by (rule decode_runtime_bits_nan[OF nan])
    with decoded show False by simp
  qed
  have not_infinity: "\<not> IEEE.is_infinity y"
  proof
    assume infinity: "IEEE.is_infinity y"
    have "decode_bits (runtime_format TYPE(('e, 'f) float))
        (runtime_bits y) = Dynamic_Infinity (IEEE.sign y = 1)"
      by (rule decode_runtime_bits_infinity[OF infinity])
    with decoded show False by simp
  qed
  show ?thesis
    using float_cases_finite[of y] not_nan not_infinity by blast
qed

lemma afp_round_rational_finite_and_valueI:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and bits :: fp_bits
    and raw :: "('e::len, 'f::len) float"
    and result :: "('e, 'f) floatSingleNaN"
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and bits: "bits \<equiv>
        round_rational_to_format_bits f rm negative n d"
      and raw: "raw \<equiv>
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
      and result: "result \<equiv> single_nan_of_float raw"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and decoded:
        "decode_bits f bits =
          Dynamic_Finite negative (finite_magnitude f bits)"
  shows "is_finite result"
    and "valof result =
      of_rat (signed_rat negative (finite_magnitude f bits))"
proof -
  have fields: "runtime_bits raw = bits"
    unfolding raw bits f
    by (rule afp_round_rational_fields[OF width numerator denominator])
  have decoded_raw:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
      (runtime_bits raw) =
      Dynamic_Finite negative (finite_magnitude f bits)"
    using decoded fields unfolding f by simp
  have raw_finite: "IEEE.is_finite raw"
    by (rule decoded_runtime_bits_finite[OF decoded_raw])
  show "is_finite result"
    unfolding result using raw_finite by simp
  have raw_sign:
    "IEEE.sign raw = (if negative then 1 else 0)"
    unfolding raw
    by (rule afp_round_rational_sign[OF width numerator denominator])
  have sign_eq: "(IEEE.sign raw = 1) = negative"
    using raw_sign by (cases negative) simp_all
  have quotient_value: "valof result = IEEE.valof raw"
    unfolding result
    by (rule single_nan_of_float_valof[OF raw_finite])
  have raw_value:
    "IEEE.valof raw =
      of_rat (signed_rat (IEEE.sign raw = 1)
        (finite_magnitude
          (runtime_format TYPE(('e, 'f) float)) (runtime_bits raw)))"
    using runtime_value_eq_signed_magnitude[of raw] by simp
  show "valof result =
      of_rat (signed_rat negative (finite_magnitude f bits))"
    using quotient_value raw_value fields sign_eq unfolding f by simp
qed

theorem afp_round_rational_nearest_finiteI:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and bits :: fp_bits
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and bits: "bits \<equiv>
        round_rational_to_format_bits f rm negative n d"
      and result: "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and decoded:
        "decode_bits f bits =
          Dynamic_Finite negative (finite_magnitude f bits)"
      and nearest:
        "\<And>b. bits_well_formed f b \<Longrightarrow>
          exponent_field b < exponent_all_ones f \<Longrightarrow>
          \<bar>signed_rat negative (finite_magnitude f bits) -
              exact_input_value negative n d\<bar> \<le>
          \<bar>signed_rat negative (finite_magnitude f b) -
              exact_input_value negative n d\<bar>"
  shows
    "fp_nearest_finite
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?raw = "afp_round_rational rm negative n d :: ('e, 'f) float"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have fields: "runtime_bits ?raw = bits"
    unfolding bits f
    by (rule afp_round_rational_fields[OF width numerator denominator])
  have decoded_raw:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
      (runtime_bits ?raw) =
      Dynamic_Finite negative (finite_magnitude f bits)"
    using decoded fields unfolding f by simp
  have raw_finite: "IEEE.is_finite ?raw"
    by (rule decoded_runtime_bits_finite[OF decoded_raw])
  have result_finite: "is_finite result"
    unfolding result using raw_finite by simp
  have raw_sign:
    "IEEE.sign ?raw = (if negative then 1 else 0)"
    by (rule afp_round_rational_sign[OF width numerator denominator])
  have sign_eq: "(IEEE.sign ?raw = 1) = negative"
    using raw_sign by (cases negative) simp_all
  have result_value:
    "valof result =
      of_rat (signed_rat negative (finite_magnitude f bits))"
  proof -
    have quotient_value: "valof result = IEEE.valof ?raw"
      unfolding result
      using single_nan_of_float_valof[OF raw_finite] by simp
    have raw_value:
      "IEEE.valof ?raw =
        of_rat (signed_rat (IEEE.sign ?raw = 1)
          (finite_magnitude
            (runtime_format TYPE(('e, 'f) float)) (runtime_bits ?raw)))"
      using runtime_value_eq_signed_magnitude[of ?raw] by simp
    show ?thesis
      using quotient_value raw_value fields sign_eq unfolding f by simp
  qed
  show ?thesis
    unfolding fp_nearest_finite_def
  proof (intro conjI allI impI)
    show "is_finite result" by (rule result_finite)
    fix competitor :: "('e, 'f) floatSingleNaN"
    assume competitor_finite: "is_finite competitor"
    obtain y :: "('e, 'f) float"
      where competitor: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using competitor_finite by (rule finite_single_nan_representation)
    have y_fields: "bits_well_formed f (runtime_bits y)"
      unfolding f by simp
    have y_exponent:
      "exponent_field (runtime_bits y) < exponent_all_ones f"
      unfolding f by (rule finite_runtime_bits_exponent[OF width y_finite])
    have rational_nearest:
      "\<bar>signed_rat negative (finite_magnitude f bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
      by (rule nearest[OF y_fields y_exponent])
    have real_nearest_same_sign:
      "\<bar>(of_rat (signed_rat negative (finite_magnitude f bits)) :: real) -
          of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>of_rat (signed_rat negative (finite_magnitude f (runtime_bits y))) -
          of_rat (exact_input_value negative n d)\<bar>"
    proof -
      have casted:
        "(of_rat
            \<bar>signed_rat negative (finite_magnitude f bits) -
              exact_input_value negative n d\<bar> :: real) \<le>
         of_rat
            \<bar>signed_rat negative
                (finite_magnitude f (runtime_bits y)) -
              exact_input_value negative n d\<bar>"
        using rational_nearest by (simp only: of_rat_less_eq)
      show ?thesis
        using casted by (simp only: abs_real_of_rat_diff)
    qed
    have magnitude_nonnegative: "0 \<le> exact_magnitude n d"
      using denominator by (simp add: exact_magnitude_def)
    have opposite_sign:
      "\<bar>of_rat (signed_rat negative (finite_magnitude f (runtime_bits y))) -
          of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>IEEE.valof y - of_rat (exact_input_value negative n d)\<bar>"
      unfolding exact_input_value_as_magnitude f
      by (rule same_sign_runtime_competitor_no_farther[
            OF magnitude_nonnegative])
    have competitor_value: "valof competitor = IEEE.valof y"
      unfolding competitor by (rule single_nan_of_float_valof[OF y_finite])
    show
      "\<bar>valof result - of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar>"
      unfolding result_value competitor_value
      using real_nearest_same_sign opposite_sign by (rule order_trans)
  qed
qed

text \<open>The subnormal branch always encodes a finite result, including
  promotion to the smallest normal at its upper boundary.\<close>

theorem afp_round_rational_subnormal_nearest_finite:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and result: "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
  shows
    "fp_nearest_finite
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?e = "floor_log2_spec n d"
  let ?c = "round_rational_core_at f rm negative n d ?e"
  let ?bits = "round_rational_to_format_bits f rm negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have logarithm: "floor_log2_rel n d ?e"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  have invariant: "core_encoding_invariant f ?c"
    by (rule round_rational_core_at_invariant[OF valid denominator logarithm])
  have core_subnormal: "core_is_subnormal ?c"
    using subnormal by (simp add: round_rational_core_at_subnormal)
  have core_decode:
    "decode_bits f (encode_rounded_core f rm negative ?c) =
      Dynamic_Finite negative (rounded_core_magnitude f ?c)"
    by (rule decode_encode_rounded_core_finite[OF
          valid invariant disjI1[OF core_subnormal]])
  have magnitude:
    "finite_magnitude f (encode_rounded_core f rm negative ?c) =
      rounded_core_magnitude f ?c"
    by (rule encode_round_rational_core_at_subnormal_magnitude[
          OF valid denominator logarithm subnormal])
  have bits_unfold:
    "?bits = encode_rounded_core f rm negative ?c"
    by (simp add: round_rational_to_format_bits_def
        round_rational_core_def)
  have decoded:
    "decode_bits f ?bits =
      Dynamic_Finite negative (finite_magnitude f ?bits)"
    using core_decode magnitude unfolding bits_unfold by simp
  have nearest:
    "\<And>b. bits_well_formed f b \<Longrightarrow>
      exponent_field b < exponent_all_ones f \<Longrightarrow>
      \<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f b) -
          exact_input_value negative n d\<bar>"
  proof -
    fix b :: fp_bits
    assume "bits_well_formed f b"
      "exponent_field b < exponent_all_ones f"
    show
      "\<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f b) -
          exact_input_value negative n d\<bar>"
    proof (cases "rm = Fp_Round_Int.RNE")
      case True
      then show ?thesis
        by (simp add:
            round_rational_to_format_bits_subnormal_RNE_nearest_finite[
              OF valid numerator denominator subnormal])
    next
      case False
      with nearest_mode have "rm = Fp_Round_Int.RNA" by blast
      then show ?thesis
        by (simp add:
            round_rational_to_format_bits_subnormal_RNA_nearest_finite[
              OF valid numerator denominator subnormal])
    qed
  qed
  have decoded_runtime:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
        (round_rational_to_format_bits
          (runtime_format TYPE(('e, 'f) float)) rm negative n d) =
      Dynamic_Finite negative
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (round_rational_to_format_bits
            (runtime_format TYPE(('e, 'f) float)) rm negative n d))"
    using decoded unfolding f .
  have nearest_runtime:
    "\<And>b. bits_well_formed
          (runtime_format TYPE(('e, 'f) float)) b \<Longrightarrow>
      exponent_field b < exponent_all_ones
          (runtime_format TYPE(('e, 'f) float)) \<Longrightarrow>
      \<bar>signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float))
            (round_rational_to_format_bits
              (runtime_format TYPE(('e, 'f) float)) rm negative n d)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float)) b) -
          exact_input_value negative n d\<bar>"
    using nearest unfolding f .
  show ?thesis
    unfolding result
    by (rule afp_round_rational_nearest_finiteI[
          OF width numerator denominator decoded_runtime nearest_runtime])
qed

text \<open>In a normal binade the same result holds whenever carry does not
  cross the largest finite exponent.  Overflow is handled separately.\<close>

theorem afp_round_rational_normal_nearest_finite:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and e :: int and c :: rounded_core
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f: "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
      and e: "e \<equiv> floor_log2_spec n d"
      and c: "c \<equiv> round_rational_core_at f rm negative n d e"
      and result: "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> e"
      and no_overflow: "core_exponent c \<le> format_emax f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
  shows
    "fp_nearest_finite
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?bits = "round_rational_to_format_bits f rm negative n d"
  have valid: "valid_format f"
    unfolding f by (rule runtime_format_valid[OF width])
  have logarithm: "floor_log2_rel n d e"
    unfolding e by (rule floor_log2_spec_correct_positive[
          OF numerator denominator])
  have invariant: "core_encoding_invariant f c"
    unfolding c
    by (rule round_rational_core_at_invariant[
          OF valid denominator logarithm])
  have encoded:
    "decode_bits f (encode_rounded_core f rm negative c) =
       Dynamic_Finite negative (rounded_core_magnitude f c)"
    "\<And>b. bits_well_formed f b \<Longrightarrow>
       exponent_field b < exponent_all_ones f \<Longrightarrow>
       \<bar>signed_rat negative (rounded_core_magnitude f c) -
           exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f b) -
           exact_input_value negative n d\<bar>"
  proof -
    show "decode_bits f (encode_rounded_core f rm negative c) =
        Dynamic_Finite negative (rounded_core_magnitude f c)"
      by (rule decode_encode_rounded_core_finite[
            OF valid invariant disjI2[OF no_overflow]])
    fix b :: fp_bits
    assume wf: "bits_well_formed f b"
      and finite_exp: "exponent_field b < exponent_all_ones f"
    show
      "\<bar>signed_rat negative (rounded_core_magnitude f c) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f b) -
          exact_input_value negative n d\<bar>"
    proof -
      have nearest_core:
        "\<bar>rounded_core_value f negative
              (round_rational_core_at f rm negative n d e) -
            exact_input_value negative n d\<bar> \<le>
         \<bar>signed_rat negative (finite_magnitude f b) -
            exact_input_value negative n d\<bar>"
        by (rule round_rational_core_at_normal_nearest_finite[
              OF valid denominator logarithm normal nearest_mode
                wf finite_exp])
      show ?thesis
        using nearest_core
        by (simp add: c rounded_core_value_def)
    qed
  qed
  have bits_unfold: "?bits = encode_rounded_core f rm negative c"
    unfolding c e round_rational_to_format_bits_def
      round_rational_core_def by simp
  have magnitude:
    "finite_magnitude f ?bits = rounded_core_magnitude f c"
  proof -
    have decoded_bits:
      "decode_bits f ?bits =
        Dynamic_Finite negative (rounded_core_magnitude f c)"
      using encoded(1) unfolding bits_unfold .
    show ?thesis
      using decoded_bits
      by (auto simp: decode_bits_def split: if_splits)
  qed
  have decoded:
    "decode_bits f ?bits =
      Dynamic_Finite negative (finite_magnitude f ?bits)"
    using encoded(1) magnitude unfolding bits_unfold by simp
  have nearest:
    "\<And>b. bits_well_formed f b \<Longrightarrow>
      exponent_field b < exponent_all_ones f \<Longrightarrow>
      \<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f b) -
          exact_input_value negative n d\<bar>"
    using encoded(2) magnitude by simp
  have decoded_runtime:
    "decode_bits (runtime_format TYPE(('e, 'f) float))
        (round_rational_to_format_bits
          (runtime_format TYPE(('e, 'f) float)) rm negative n d) =
      Dynamic_Finite negative
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (round_rational_to_format_bits
            (runtime_format TYPE(('e, 'f) float)) rm negative n d))"
    using decoded unfolding f .
  have nearest_runtime:
    "\<And>b. bits_well_formed
          (runtime_format TYPE(('e, 'f) float)) b \<Longrightarrow>
      exponent_field b < exponent_all_ones
          (runtime_format TYPE(('e, 'f) float)) \<Longrightarrow>
      \<bar>signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float))
            (round_rational_to_format_bits
              (runtime_format TYPE(('e, 'f) float)) rm negative n d)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float)) b) -
          exact_input_value negative n d\<bar>"
    using nearest unfolding f .
  show ?thesis
    unfolding result
    by (rule afp_round_rational_nearest_finiteI[
          OF width numerator denominator decoded_runtime nearest_runtime])
qed

end

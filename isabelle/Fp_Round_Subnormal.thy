(* SPDX-License-Identifier: MIT *)

section \<open>Global optimality on the subnormal grid\<close>

theory Fp_Round_Subnormal
  imports Fp_Round_Local Fp_Finite_Grid
begin

text \<open>
  Every finite run-time bit pattern is an integer multiple of the minimum
  subnormal step.  Consequently, when the exact input lies below the normal
  range, optimality of integer rounding on that single grid is already
  optimality against every finite bit pattern of the format.  The statements
  below do not need well-formedness of the competing bit pattern: its decoded
  finite magnitude lies on the grid even without the field bounds.
\<close>

lemma minimum_subnormal_step_as_rounding_step:
  "minimum_subnormal_step f =
    rat_pow2 (-(int (fraction_bits f) - format_emin f))"
  by (simp add: minimum_subnormal_step_def pow2_rat_eq_rat_pow2)

lemma finite_magnitude_as_subnormal_grid_point:
  obtains m :: nat where
    "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
proof -
  obtain m :: nat where magnitude:
      "finite_magnitude f b = of_nat m * minimum_subnormal_step f"
    by (rule finite_magnitude_on_minimum_subnormal_grid)
  show thesis
    by (rule that[of m])
      (simp add: magnitude grid_point_value_def
        minimum_subnormal_step_as_rounding_step)
qed

theorem subnormal_grid_RNE_nearest_finite_magnitude:
  assumes denominator: "0 < d"
  shows
    "\<bar>rounded_grid_value RNE negative n d
          (int (fraction_bits f) - format_emin f) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  obtain m :: nat where competitor:
      "signed_rat negative (finite_magnitude f b) =
        grid_point_value negative
          (int (fraction_bits f) - format_emin f) m"
    by (rule finite_magnitude_as_subnormal_grid_point)
  show ?thesis
    unfolding competitor
    by (rule grid_RNE_nearest_grid_point[OF denominator])
qed

theorem subnormal_grid_RNA_nearest_finite_magnitude:
  assumes denominator: "0 < d"
  shows
    "\<bar>rounded_grid_value RNA negative n d
          (int (fraction_bits f) - format_emin f) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  obtain m :: nat where competitor:
      "signed_rat negative (finite_magnitude f b) =
        grid_point_value negative
          (int (fraction_bits f) - format_emin f) m"
    by (rule finite_magnitude_as_subnormal_grid_point)
  show ?thesis
    unfolding competitor
    by (rule grid_RNA_nearest_grid_point[OF denominator])
qed

text \<open>
  Reconnecting the grid theorem to the actual branch selected by
  @{const round_rational_core_at} gives global finite optimality of the
  constructed core value.
\<close>

theorem round_rational_core_at_subnormal_RNE_nearest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and subnormal: "e < format_emin f"
  shows
    "\<bar>rounded_core_value f negative
          (round_rational_core_at f RNE negative n d e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have core_value:
      "rounded_core_value f negative
          (round_rational_core_at f RNE negative n d e) =
       rounded_grid_value RNE negative n d
          (int (fraction_bits f) - format_emin f)"
    using round_rational_core_at_value[OF valid, of negative RNE n d e]
      subnormal
    by simp
  show ?thesis
    unfolding core_value
    by (rule subnormal_grid_RNE_nearest_finite_magnitude[OF denominator])
qed

theorem round_rational_core_at_subnormal_RNA_nearest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and subnormal: "e < format_emin f"
  shows
    "\<bar>rounded_core_value f negative
          (round_rational_core_at f RNA negative n d e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have core_value:
      "rounded_core_value f negative
          (round_rational_core_at f RNA negative n d e) =
       rounded_grid_value RNA negative n d
          (int (fraction_bits f) - format_emin f)"
    using round_rational_core_at_value[OF valid, of negative RNA n d e]
      subnormal
    by simp
  show ?thesis
    unfolding core_value
    by (rule subnormal_grid_RNA_nearest_finite_magnitude[OF denominator])
qed

text \<open>
  With the floor-log invariant, the subnormal significand is bounded by the
  normal-boundary coefficient.  The encoding is therefore finite (possibly
  the smallest normal after promotion), and its bit-level magnitude is exactly
  the value carried by the rounded core.
\<close>

lemma finite_magnitude_subnormal_result_bits:
  assumes valid: "valid_format f"
      and bound: "m \<le> 2 ^ fraction_bits f"
  shows
    "finite_magnitude f (subnormal_result_bits f negative m) =
      of_nat m * minimum_subnormal_step f"
proof -
  have decoded:
      "decode_bits f (subnormal_result_bits f negative m) =
        Dynamic_Finite negative
          (of_nat m *
            pow2_rat (format_emin f - int (fraction_bits f)))"
    by (rule decode_subnormal_result_bits[OF valid bound])
  show ?thesis
    using decoded
    by (auto simp: decode_bits_def minimum_subnormal_step_def
        split: if_splits)
qed

lemma encode_round_rational_core_at_subnormal_magnitude:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows
    "finite_magnitude f
        (encode_rounded_core f rm negative
          (round_rational_core_at f rm negative n d e)) =
      rounded_core_magnitude f
        (round_rational_core_at f rm negative n d e)"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  let ?m = "scaled_round_integer rm negative n d ?k"
  have bound: "?m \<le> 2 ^ fraction_bits f"
    by (rule subnormal_rounded_significand_upper[
          OF denominator logarithm subnormal])
  have core:
      "round_rational_core_at f rm negative n d e =
        \<lparr>core_significand = ?m,
          core_exponent = format_emin f,
          core_is_subnormal = True\<rparr>"
    by (rule round_rational_core_at_subnormal[OF subnormal])
  have output_magnitude:
      "finite_magnitude f (subnormal_result_bits f negative ?m) =
        of_nat ?m * minimum_subnormal_step f"
    by (rule finite_magnitude_subnormal_result_bits[OF valid bound])
  show ?thesis
    using output_magnitude
    by (simp add: core encode_rounded_core_def rounded_core_magnitude_def
        minimum_subnormal_step_def pow2_rat_eq_rat_pow2)
qed

corollary encode_round_rational_core_at_subnormal_value:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows
    "signed_rat negative
        (finite_magnitude f
          (encode_rounded_core f rm negative
            (round_rational_core_at f rm negative n d e))) =
      rounded_core_value f negative
        (round_rational_core_at f rm negative n d e)"
  using encode_round_rational_core_at_subnormal_magnitude[
      OF valid denominator logarithm subnormal, of rm negative]
  by (simp add: rounded_core_value_def)

theorem encode_round_rational_core_at_subnormal_RNE_nearest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (encode_rounded_core f RNE negative
              (round_rational_core_at f RNE negative n d e))) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have output_value:
      "signed_rat negative
          (finite_magnitude f
            (encode_rounded_core f RNE negative
              (round_rational_core_at f RNE negative n d e))) =
        rounded_core_value f negative
          (round_rational_core_at f RNE negative n d e)"
    by (rule encode_round_rational_core_at_subnormal_value[
          OF valid denominator logarithm subnormal])
  show ?thesis
    unfolding output_value
    by (rule round_rational_core_at_subnormal_RNE_nearest_finite[
          OF valid denominator subnormal])
qed

theorem encode_round_rational_core_at_subnormal_RNA_nearest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (encode_rounded_core f RNA negative
              (round_rational_core_at f RNA negative n d e))) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have output_value:
      "signed_rat negative
          (finite_magnitude f
            (encode_rounded_core f RNA negative
              (round_rational_core_at f RNA negative n d e))) =
        rounded_core_value f negative
          (round_rational_core_at f RNA negative n d e)"
    by (rule encode_round_rational_core_at_subnormal_value[
          OF valid denominator logarithm subnormal])
  show ?thesis
    unfolding output_value
    by (rule round_rational_core_at_subnormal_RNA_nearest_finite[
          OF valid denominator subnormal])
qed

text \<open>
  The corresponding theorems for @{const round_rational_core} use the verified
  floor logarithm chosen by the conversion algorithm.  Positivity of the
  numerator is included because it is the precondition under which that
  logarithm denotes the input's binade.
\<close>

theorem round_rational_core_subnormal_RNE_nearest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
  shows
    "\<bar>rounded_core_value f negative
          (round_rational_core f RNE negative n d) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
  unfolding round_rational_core_def
  by (rule round_rational_core_at_subnormal_RNE_nearest_finite[
        OF valid denominator subnormal])

theorem round_rational_core_subnormal_RNA_nearest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
  shows
    "\<bar>rounded_core_value f negative
          (round_rational_core f RNA negative n d) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
  unfolding round_rational_core_def
  by (rule round_rational_core_at_subnormal_RNA_nearest_finite[
        OF valid denominator subnormal])

theorem round_rational_to_format_bits_subnormal_RNE_nearest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f RNE negative n d)) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct)
      (rule floor_log2_rel_exists[OF numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    by (rule encode_round_rational_core_at_subnormal_RNE_nearest_finite[
          OF valid denominator logarithm subnormal])
qed

theorem round_rational_to_format_bits_subnormal_RNA_nearest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f RNA negative n d)) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct)
      (rule floor_log2_rel_exists[OF numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    by (rule encode_round_rational_core_at_subnormal_RNA_nearest_finite[
          OF valid denominator logarithm subnormal])
qed

end

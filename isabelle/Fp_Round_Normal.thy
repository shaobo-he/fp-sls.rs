(* SPDX-License-Identifier: MIT *)

section \<open>Global nearestness in a normal binade\<close>

theory Fp_Round_Normal
  imports Fp_Round_Local Fp_Finite_Grid
begin

text \<open>
  Rounding at the normal-binade scale is locally optimal on the grid whose
  spacing is @{term "pow2_rat (e - int (fraction_bits f))"}.  Every finite
  format value at or above the binade boundary lies on that grid.  Values
  below the boundary cannot be closer than the boundary itself, which is also
  a point of the selected grid.  These two facts lift local integer
  nearestness to all same-sign, well-formed finite dynamic competitors.
\<close>

lemma exact_input_value_as_magnitude:
  "exact_input_value negative n d =
    signed_rat negative (exact_magnitude n d)"
  by (simp add: exact_input_value_def exact_magnitude_def)

lemma normal_binade_boundary_grid_point:
  "grid_point_value negative (int (fraction_bits f) - e)
      (2 ^ fraction_bits f) =
    signed_rat negative (pow2_rat e)"
proof -
  have split:
    "pow2_rat e = of_nat (2 ^ fraction_bits f) *
      pow2_rat (e - int (fraction_bits f))"
    by (rule pow2_rat_split_fraction_width)
  show ?thesis
    using split
    by (simp add: grid_point_value_def pow2_rat_eq_rat_pow2)
qed

lemma finite_magnitude_on_normal_rounding_grid:
  assumes magnitude:
    "finite_magnitude f b =
      of_nat z * pow2_rat (e - int (fraction_bits f))"
  shows
    "grid_point_value negative (int (fraction_bits f) - e) z =
      signed_rat negative (finite_magnitude f b)"
  using magnitude
  by (simp add: grid_point_value_def pow2_rat_eq_rat_pow2)

lemma same_sign_boundary_distance_mono:
  fixes a boundary x :: rat
  assumes below: "a \<le> boundary"
      and input_above: "boundary \<le> x"
  shows
    "\<bar>signed_rat negative boundary - signed_rat negative x\<bar> \<le>
     \<bar>signed_rat negative a - signed_rat negative x\<bar>"
proof -
  have left_nonpositive: "boundary - x \<le> 0"
    using input_above by linarith
  have right_nonpositive: "a - x \<le> 0"
    using below input_above by linarith
  show ?thesis
    using below left_nonpositive right_nonpositive
    by (simp add: abs_of_nonpos)
qed

theorem rounded_normal_grid_nearest_finite:
  fixes n d :: nat and e :: int
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and nearest_mode: "rm = RNE \<or> rm = RNA"
      and well_formed: "bits_well_formed f b"
      and finite_exponent:
        "exponent_field b < exponent_all_ones f"
  shows
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof (cases
    "pow2_rat e \<le> finite_magnitude f b")
  case competitor_above: True
  obtain z :: nat where competitor_grid:
      "finite_magnitude f b =
        of_nat z * pow2_rat (e - int (fraction_bits f))"
    by (rule finite_magnitude_above_power_on_grid[
          OF valid well_formed finite_exponent normal competitor_above])
  have grid_point:
    "grid_point_value negative (int (fraction_bits f) - e) z =
      signed_rat negative (finite_magnitude f b)"
    by (rule finite_magnitude_on_normal_rounding_grid[OF competitor_grid])
  have local_nearest:
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>grid_point_value negative (int (fraction_bits f) - e) z -
        exact_input_value negative n d\<bar>"
  proof (cases "rm = RNE")
    case True
    have nearest:
      "\<bar>rounded_grid_value RNE negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>grid_point_value negative (int (fraction_bits f) - e) z -
          exact_input_value negative n d\<bar>"
      by (rule grid_RNE_nearest_grid_point[OF denominator])
    with True show ?thesis by simp
  next
    case False
    with nearest_mode have "rm = RNA" by blast
    moreover have nearest:
      "\<bar>rounded_grid_value RNA negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>grid_point_value negative (int (fraction_bits f) - e) z -
          exact_input_value negative n d\<bar>"
      by (rule grid_RNA_nearest_grid_point[OF denominator])
    ultimately show ?thesis by simp
  qed
  show ?thesis
    using local_nearest grid_point by simp
next
  case competitor_below: False
  then have competitor_le_boundary:
    "finite_magnitude f b \<le> pow2_rat e"
    by linarith
  have input_above_boundary:
    "pow2_rat e \<le> exact_magnitude n d"
    using logarithm
    by (simp add: floor_log2_rel_def)
  have boundary_distance:
    "\<bar>signed_rat negative (pow2_rat e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
    unfolding exact_input_value_as_magnitude
    by (rule same_sign_boundary_distance_mono[
          OF competitor_le_boundary input_above_boundary])
  have local_nearest_boundary:
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>grid_point_value negative (int (fraction_bits f) - e)
          (2 ^ fraction_bits f) -
        exact_input_value negative n d\<bar>"
  proof (cases "rm = RNE")
    case True
    have nearest:
      "\<bar>rounded_grid_value RNE negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>grid_point_value negative (int (fraction_bits f) - e)
            (2 ^ fraction_bits f) -
          exact_input_value negative n d\<bar>"
      by (rule grid_RNE_nearest_grid_point[OF denominator])
    with True show ?thesis by simp
  next
    case False
    with nearest_mode have "rm = RNA" by blast
    moreover have nearest:
      "\<bar>rounded_grid_value RNA negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>grid_point_value negative (int (fraction_bits f) - e)
            (2 ^ fraction_bits f) -
          exact_input_value negative n d\<bar>"
      by (rule grid_RNA_nearest_grid_point[OF denominator])
    ultimately show ?thesis by simp
  qed
  have boundary_grid:
    "grid_point_value negative (int (fraction_bits f) - e)
        (2 ^ fraction_bits f) =
      signed_rat negative (pow2_rat e)"
    by (rule normal_binade_boundary_grid_point)
  have local_nearest_boundary':
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (pow2_rat e) -
        exact_input_value negative n d\<bar>"
    using local_nearest_boundary boundary_grid by simp
  show ?thesis
    using local_nearest_boundary' boundary_distance
    by (rule order_trans)
qed

corollary rounded_normal_grid_nearest_same_sign_bits:
  fixes n d :: nat and e :: int
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and nearest_mode: "rm = RNE \<or> rm = RNA"
      and well_formed: "bits_well_formed f b"
      and finite_exponent:
        "exponent_field b < exponent_all_ones f"
      and same_sign: "negative_bit b = negative"
  shows
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat (negative_bit b) (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
  using rounded_normal_grid_nearest_finite[OF
      valid denominator logarithm normal nearest_mode
      well_formed finite_exponent]
    same_sign
  by simp

corollary round_rational_core_at_normal_nearest_finite:
  fixes n d :: nat and e :: int
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and nearest_mode: "rm = RNE \<or> rm = RNA"
      and well_formed: "bits_well_formed f b"
      and finite_exponent:
        "exponent_field b < exponent_all_ones f"
  shows
    "\<bar>rounded_core_value f negative
          (round_rational_core_at f rm negative n d e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have core_value:
    "rounded_core_value f negative
        (round_rational_core_at f rm negative n d e) =
      rounded_grid_value rm negative n d
        (int (fraction_bits f) - e)"
    using round_rational_core_at_value[OF valid, of negative rm n d e]
      normal
    by simp
  have nearest:
    "\<bar>rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
    by (rule rounded_normal_grid_nearest_finite[OF
          valid denominator logarithm normal nearest_mode
          well_formed finite_exponent])
  show ?thesis using nearest core_value by simp
qed

theorem encode_normal_rounding_finite_and_nearest:
  fixes n d :: nat and e :: int
    and f :: binary_format and rm :: fp_round_mode
    and negative :: bool and c :: rounded_core
  defines core:
    "c \<equiv> round_rational_core_at f rm negative n d e"
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and nearest_mode: "rm = RNE \<or> rm = RNA"
      and no_overflow:
        "core_is_subnormal c \<or> core_exponent c \<le> format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent:
        "exponent_field b < exponent_all_ones f"
  shows
    "decode_bits f (encode_rounded_core f rm negative c) =
       Dynamic_Finite negative (rounded_core_magnitude f c)"
    "\<bar>signed_rat negative (rounded_core_magnitude f c) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
proof -
  have invariant: "core_encoding_invariant f c"
    unfolding core
    by (rule round_rational_core_at_invariant[
          OF valid denominator logarithm])
  show decode:
    "decode_bits f (encode_rounded_core f rm negative c) =
       Dynamic_Finite negative (rounded_core_magnitude f c)"
    by (rule decode_encode_rounded_core_finite[
          OF valid invariant no_overflow])
  have nearest:
    "\<bar>rounded_core_value f negative
          (round_rational_core_at f rm negative n d e) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
    by (rule round_rational_core_at_normal_nearest_finite[OF
          valid denominator logarithm normal nearest_mode
          well_formed finite_exponent])
  show
    "\<bar>signed_rat negative (rounded_core_magnitude f c) -
        exact_input_value negative n d\<bar> \<le>
     \<bar>signed_rat negative (finite_magnitude f b) -
        exact_input_value negative n d\<bar>"
    using nearest
    by (simp add: core rounded_core_value_def)
qed

end

(* SPDX-License-Identifier: MIT *)

section \<open>Nearest-mode preferences for every finite result\<close>

theory Fp_Round_Preference
  imports Fp_Round_Ties Fp_Round_Nearest_IEEE
begin

section \<open>Strict integer nearestness away from a midpoint\<close>

lemma scaled_error_strict_half_rat:
  fixes p q m :: nat
  assumes qpos: "0 < q"
      and strict: "2 * scaled_error p q m < q"
  shows
    "\<bar>(of_nat m :: rat) - of_nat p / of_nat q\<bar> < 1 / 2"
proof -
  have strict_rat:
      "2 * (of_nat (scaled_error p q m) :: rat) < of_nat q"
    using strict by simp
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have divided:
      "(of_nat (scaled_error p q m) :: rat) / of_nat q < 1 / 2"
    using strict_rat qrat
    by (simp add: pos_divide_less_eq; linarith)
  have error:
      "(of_nat (scaled_error p q m) :: rat) / of_nat q =
        \<bar>(of_nat m :: rat) - of_nat p / of_nat q\<bar>"
    by (rule scaled_error_divide_eq_abs[OF qpos])
  show ?thesis using divided error by simp
qed

lemma nearest_round_integer_strict_half_mode:
  fixes p q :: nat and rm :: fp_round_mode
  assumes qpos: "0 < q"
      and not_tie: "q \<noteq> 2 * (p mod q)"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
  shows
    "\<bar>(of_nat (round_integer rm negative p q) :: rat) -
        of_nat p / of_nat q\<bar> < 1 / 2"
proof -
  have remainder: "p mod q < q" by (rule mod_less_divisor[OF qpos])
  consider (below) "2 * (p mod q) < q"
    | (above) "q < 2 * (p mod q)"
    using not_tie by linarith
  then show ?thesis
  proof cases
    case below
    have rounded: "round_integer rm negative p q = p div q"
      using nearest_mode nearest_integer_below_half[OF below] by blast
    have strict:
        "2 * scaled_error p q (p div q) < q"
      using below by (simp add: scaled_error_floor)
    show ?thesis
      unfolding rounded
      by (rule scaled_error_strict_half_rat[OF qpos strict])
  next
    case above
    have rounded: "round_integer rm negative p q = p div q + 1"
      using nearest_mode nearest_integer_above_half[OF above] by blast
    have error:
        "scaled_error p q (p div q + 1) = q - p mod q"
      by (rule scaled_error_upper[OF qpos])
    have strict_nat: "2 * (q - p mod q) < q"
      using above remainder by linarith
    have strict:
        "2 * scaled_error p q (p div q + 1) < q"
      using error strict_nat by simp
    show ?thesis
      unfolding rounded
      by (rule scaled_error_strict_half_rat[OF qpos strict])
  qed
qed

lemma nearest_RNE_strict_half:
  assumes "0 < q" "q \<noteq> 2 * (p mod q)"
  shows
    "\<bar>(of_nat (round_integer Fp_Round_Int.RNE negative p q) :: rat) -
        of_nat p / of_nat q\<bar> < 1 / 2"
  by (rule nearest_round_integer_strict_half_mode[OF assms]) simp

lemma nearest_RNA_strict_half:
  assumes "0 < q" "q \<noteq> 2 * (p mod q)"
  shows
    "\<bar>(of_nat (round_integer Fp_Round_Int.RNA negative p q) :: rat) -
        of_nat p / of_nat q\<bar> < 1 / 2"
  by (rule nearest_round_integer_strict_half_mode[OF assms]) simp

lemma strict_half_equal_integer_unique:
  fixes x :: rat and m z :: nat
  assumes half: "\<bar>(of_nat m :: rat) - x\<bar> < 1 / 2"
      and equal:
        "\<bar>(of_nat z :: rat) - x\<bar> =
          \<bar>(of_nat m :: rat) - x\<bar>"
  shows "z = m"
proof (rule ccontr)
  assume different: "z \<noteq> m"
  have gap: "1 \<le> \<bar>(of_nat z :: rat) - of_nat m\<bar>"
  proof (cases "z < m")
    case True
    have step: "(of_nat z :: rat) + 1 \<le> of_nat m"
      using True by simp
    have nonpos: "(of_nat z :: rat) - of_nat m \<le> 0"
      using step by linarith
    show ?thesis
      using step by (simp add: abs_of_nonpos nonpos; linarith)
  next
    case False
    then have mz: "m < z" using different by auto
    have step: "(of_nat m :: rat) + 1 \<le> of_nat z"
      using mz by simp
    have nonneg: "0 \<le> (of_nat z :: rat) - of_nat m"
      using step by linarith
    show ?thesis
      using step by (simp add: abs_of_nonneg nonneg; linarith)
  qed
  have triangle:
      "\<bar>(of_nat z :: rat) - of_nat m\<bar> \<le>
        \<bar>(of_nat z :: rat) - x\<bar> +
        \<bar>(of_nat m :: rat) - x\<bar>"
  proof -
    have split:
        "(of_nat z :: rat) - of_nat m =
          ((of_nat z :: rat) - x) + (x - of_nat m)"
      by linarith
    have
      "\<bar>(of_nat z :: rat) - of_nat m\<bar> =
        \<bar>((of_nat z :: rat) - x) + (x - of_nat m)\<bar>"
      using split by simp
    also have "... \<le>
        \<bar>(of_nat z :: rat) - x\<bar> + \<bar>x - of_nat m\<bar>"
      by (rule abs_triangle_ineq)
    also have "... =
        \<bar>(of_nat z :: rat) - x\<bar> +
        \<bar>(of_nat m :: rat) - x\<bar>"
      by (simp add: abs_minus_commute)
    finally show ?thesis .
  qed
  show False using gap triangle half equal by linarith
qed

lemma RNE_equal_error_even_preference:
  fixes p q z :: nat
  assumes qpos: "0 < q"
      and equal:
        "\<bar>(of_nat z :: rat) - of_nat p / of_nat q\<bar> =
          \<bar>(of_nat (round_integer Fp_Round_Int.RNE negative p q) :: rat) -
            of_nat p / of_nat q\<bar>"
      and competitor_even: "even z"
  shows "even (round_integer Fp_Round_Int.RNE negative p q)"
proof (cases "q = 2 * (p mod q)")
  case True
  show ?thesis by (rule RNE_integer_at_half_is_even[OF qpos True])
next
  case False
  have half:
      "\<bar>(of_nat (round_integer Fp_Round_Int.RNE negative p q) :: rat) -
        of_nat p / of_nat q\<bar> < 1 / 2"
    by (rule nearest_RNE_strict_half[OF qpos False])
  have same:
      "z = round_integer Fp_Round_Int.RNE negative p q"
    by (rule strict_half_equal_integer_unique[OF half equal])
  show ?thesis using competitor_even same by simp
qed

lemma RNA_equal_error_outward_preference:
  fixes p q z :: nat
  assumes qpos: "0 < q"
      and equal:
        "\<bar>(of_nat z :: rat) - of_nat p / of_nat q\<bar> =
          \<bar>(of_nat (round_integer Fp_Round_Int.RNA negative p q) :: rat) -
            of_nat p / of_nat q\<bar>"
      and competitor_outward:
        "of_nat p / of_nat q \<le> (of_nat z :: rat)"
  shows
    "of_nat p / of_nat q \<le>
      (of_nat (round_integer Fp_Round_Int.RNA negative p q) :: rat)"
proof (cases "q = 2 * (p mod q)")
  case tie: True
  have rounded:
      "round_integer Fp_Round_Int.RNA negative p q = p div q + 1"
    by (rule RNA_integer_at_half[OF qpos tie])
  have upper_nat: "p < (p div q + 1) * q"
    using dividend_less_div_times[OF qpos, of p]
    by (simp add: add_mult_distrib ac_simps)
  have qrat: "0 < (of_nat q :: rat)" using qpos by simp
  have upper:
      "(of_nat p :: rat) / of_nat q < of_nat (p div q + 1)"
  proof -
    have cast:
        "(of_nat p :: rat) < of_nat (p div q + 1) * of_nat q"
      using upper_nat
      by (simp only: of_nat_mult[symmetric] of_nat_less_iff)
    show ?thesis
      using cast by (simp only: pos_divide_less_eq[OF qrat])
  qed
  show ?thesis using rounded upper by simp
next
  case not_tie: False
  have half:
      "\<bar>(of_nat (round_integer Fp_Round_Int.RNA negative p q) :: rat) -
        of_nat p / of_nat q\<bar> < 1 / 2"
    by (rule nearest_RNA_strict_half[OF qpos not_tie])
  have same:
      "z = round_integer Fp_Round_Int.RNA negative p q"
    by (rule strict_half_equal_integer_unique[OF half equal])
  show ?thesis using competitor_outward same by simp
qed

section \<open>Parity of the canonical minimum-grid coefficient\<close>

lemma finite_magnitude_even_minimum_grid_coefficient:
  assumes valid: "valid_format f"
      and fraction_even: "even (fraction_field b)"
  obtains z :: nat where
    "finite_magnitude f b = of_nat z * minimum_subnormal_step f"
    "even z"
proof (cases "exponent_field b = 0")
  case True
  show thesis
  proof (rule that[of "fraction_field b"])
    show "finite_magnitude f b =
        of_nat (fraction_field b) * minimum_subnormal_step f"
      by (rule finite_magnitude_subnormal_grid[OF True])
    show "even (fraction_field b)" by (rule fraction_even)
  qed
next
  case False
  then have positive: "0 < exponent_field b" by simp
  let ?z = "(2 ^ fraction_bits f + fraction_field b) *
    2 ^ (exponent_field b - 1)"
  have boundary_even: "even ((2::nat) ^ fraction_bits f)"
    using valid_format_fraction_bits_pos[OF valid] by simp
  have z_even: "even ?z"
    using boundary_even fraction_even by simp
  show thesis
    by (rule that[of ?z])
      (rule finite_magnitude_normal_grid[OF positive], rule z_even)
qed

section \<open>Subnormal output and equally-near competitors\<close>

lemma round_rational_to_format_bits_subnormal_signed_value:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
  shows
    "signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)) =
      rounded_grid_value rm negative n d
        (int (fraction_bits f) - format_emin f)"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    using encode_round_rational_core_at_subnormal_value[
      OF valid denominator logarithm subnormal]
      round_rational_core_at_value[OF valid] subnormal
    by (simp add: rounded_core_value_def)
qed

lemma subnormal_afp_result_finite_and_value:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
  shows
    "is_finite result"
    "valof result =
      of_rat (signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)))"
proof -
  have subnormal_runtime:
      "floor_log2_spec n d <
        format_emin (runtime_format TYPE(('e, 'f) float))"
    using subnormal unfolding f_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding f_def result_def
    by (rule afp_round_rational_subnormal_nearest_finite[OF
          width numerator denominator subnormal_runtime nearest_mode])
  show finite: "is_finite result"
    by (rule fp_nearest_finiteD(1)[OF nearest])
  let ?raw = "afp_round_rational rm negative n d :: ('e, 'f) float"
  have raw_finite: "IEEE.is_finite ?raw"
    using finite unfolding result_def by simp
  have fields:
      "runtime_bits ?raw =
        round_rational_to_format_bits f rm negative n d"
    unfolding f_def
    by (rule afp_round_rational_fields[OF width numerator denominator])
  have raw_sign:
      "IEEE.sign ?raw = (if negative then 1 else 0)"
    by (rule afp_round_rational_sign[OF width numerator denominator])
  have sign_eq: "(IEEE.sign ?raw = 1) = negative"
    using raw_sign by (cases negative) simp_all
  have quotient_value: "valof result = IEEE.valof ?raw"
    unfolding result_def by (rule single_nan_of_float_valof[OF raw_finite])
  have raw_value:
      "IEEE.valof ?raw =
        of_rat (signed_rat (IEEE.sign ?raw = 1)
          (finite_magnitude
            (runtime_format TYPE(('e, 'f) float)) (runtime_bits ?raw)))"
    using runtime_value_eq_signed_magnitude[of ?raw] by simp
  show "valof result =
      of_rat (signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)))"
    using quotient_value raw_value fields sign_eq unfolding f_def by simp
qed

lemma subnormal_nearest_raw_same_sign_error_equal:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and y :: "('e::len, 'f::len) float"
    and result competitor :: "('e, 'f) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
    and competitor_def: "competitor \<equiv> single_nan_of_float y"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and y_finite: "IEEE.is_finite y"
      and competitor_nearest:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d)) competitor"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f rm negative n d)) -
        exact_input_value negative n d\<bar> =
      \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
        exact_input_value negative n d\<bar>"
proof -
  let ?bits = "round_rational_to_format_bits f rm negative n d"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have subnormal_runtime:
      "floor_log2_spec n d <
        format_emin (runtime_format TYPE(('e, 'f) float))"
    using subnormal unfolding f_def .
  have result_nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_subnormal_nearest_finite[OF
          width numerator denominator subnormal_runtime nearest_mode])
  have result_value:
      "valof result =
        of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding f_def result_def
    by (rule subnormal_afp_result_finite_and_value(2)[OF
          width numerator denominator subnormal_runtime nearest_mode])
  have competitor_value:
      "valof competitor =
        of_rat (signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)))"
    using single_nan_value_eq_signed_magnitude[OF y_finite]
    unfolding competitor_def f_def by simp
  have real_equal:
      "\<bar>valof result - of_rat (exact_input_value negative n d)\<bar> =
       \<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar>"
  proof (rule antisym)
    show
      "\<bar>valof result - of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar>"
      by (rule fp_nearest_finiteD(2)[OF result_nearest])
        (rule fp_nearest_finiteD(1)[OF competitor_nearest])
    show
      "\<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>valof result - of_rat (exact_input_value negative n d)\<bar>"
      by (rule fp_nearest_finiteD(2)[OF competitor_nearest])
        (rule fp_nearest_finiteD(1)[OF result_nearest])
  qed
  have actual_equal:
      "\<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> =
       \<bar>signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
    using real_equal result_value competitor_value
    by (simp only: abs_real_of_rat_diff of_rat_eq_iff)
  have output_le_same:
      "\<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
  proof (cases "rm = Fp_Round_Int.RNE")
    case True
    show ?thesis
      using round_rational_to_format_bits_subnormal_RNE_nearest_finite[
        OF valid numerator denominator subnormal,
        of negative "runtime_bits y"] True
      by simp
  next
    case False
    with nearest_mode have mode: "rm = Fp_Round_Int.RNA" by blast
    show ?thesis
      using round_rational_to_format_bits_subnormal_RNA_nearest_finite[
        OF valid numerator denominator subnormal,
        of negative "runtime_bits y"] mode
      by simp
  qed
  have same_le_actual:
      "\<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
  proof -
    have exact_nonnegative: "0 \<le> exact_magnitude n d"
      using denominator by (simp add: exact_magnitude_def)
    show ?thesis
      unfolding exact_input_value_as_magnitude
      by (rule same_sign_competitor_no_farther[OF
            exact_nonnegative finite_magnitude_nonnegative])
  qed
  have same_le_output:
      "\<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar>"
    using same_le_actual actual_equal by linarith
  show ?thesis
    by (rule antisym[OF output_le_same same_le_output])
qed

lemma subnormal_same_sign_error_equal_scaled:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and magnitude:
        "finite_magnitude f b = of_nat z * minimum_subnormal_step f"
      and equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits f rm negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative (finite_magnitude f b) -
            exact_input_value negative n d\<bar>"
  shows
    "\<bar>(of_nat z :: rat) -
        of_nat (scaled_numerator n d
          (int (fraction_bits f) - format_emin f)) /
        of_nat (scaled_denominator n d
          (int (fraction_bits f) - format_emin f))\<bar> =
     \<bar>of_nat (scaled_round_integer rm negative n d
          (int (fraction_bits f) - format_emin f)) -
        of_nat (scaled_numerator n d
          (int (fraction_bits f) - format_emin f)) /
        of_nat (scaled_denominator n d
          (int (fraction_bits f) - format_emin f))\<bar>"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  have output_grid:
      "signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f rm negative n d)) =
        rounded_grid_value rm negative n d ?k"
    by (rule round_rational_to_format_bits_subnormal_signed_value[OF
          valid numerator denominator subnormal])
  have competitor_grid:
      "signed_rat negative (finite_magnitude f b) =
        grid_point_value negative ?k z"
    using magnitude
    by (simp add: grid_point_value_def
        minimum_subnormal_step_as_rounding_step)
  have grid_equal:
      "\<bar>rounded_grid_value rm negative n d ?k -
          exact_input_value negative n d\<bar> =
       \<bar>grid_point_value negative ?k z -
          exact_input_value negative n d\<bar>"
    using equal output_grid competitor_grid by simp
  have output_unscale:
      "\<bar>scaled_rounded_value rm negative n d ?k -
          scaled_exact_value negative n d ?k\<bar> * rat_pow2 (- ?k) =
       \<bar>rounded_grid_value rm negative n d ?k -
          exact_input_value negative n d\<bar>"
    by (rule rounded_grid_error_unscale)
  have competitor_unscale:
      "\<bar>signed_rat negative (of_nat z) -
          scaled_exact_value negative n d ?k\<bar> * rat_pow2 (- ?k) =
       \<bar>grid_point_value negative ?k z -
          exact_input_value negative n d\<bar>"
    by (rule grid_point_error_unscale)
  have step_nonzero: "rat_pow2 (- ?k) \<noteq> 0"
    using rat_pow2_pos[of "- ?k"] by linarith
  have scaled_equal:
      "\<bar>signed_rat negative (of_nat z) -
          scaled_exact_value negative n d ?k\<bar> =
       \<bar>scaled_rounded_value rm negative n d ?k -
          scaled_exact_value negative n d ?k\<bar>"
    using grid_equal output_unscale competitor_unscale step_nonzero
    by (metis mult_right_cancel)
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        (of_nat n / of_nat d) * rat_pow2 ?k"
    by (rule scale_ratio_exact[OF denominator])
  show ?thesis
    using scaled_equal scale
    by (cases negative)
      (simp_all add: scaled_exact_value_def scaled_rounded_value_def
        abs_minus_commute)
qed

theorem afp_round_rational_subnormal_RNE_preferred_nearest:
  fixes negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
  shows
    "fp_preferred_nearest fp_even_lsb
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  let ?p = "scaled_numerator n d ?k"
  let ?q = "scaled_denominator n d ?k"
  let ?m = "scaled_round_integer Fp_Round_Int.RNE negative n d ?k"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have subnormal_runtime:
      "floor_log2_spec n d <
        format_emin (runtime_format TYPE(('e, 'f) float))"
    using subnormal unfolding f_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_subnormal_nearest_finite[OF
          width numerator denominator subnormal_runtime]) simp
  show ?thesis
    unfolding fp_preferred_nearest_def
  proof (intro conjI impI)
    show "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
      by (rule nearest)
    assume preferred_exists:
        "\<exists>competitor::('e, 'f) floatSingleNaN.
          fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor \<and>
          fp_even_lsb competitor"
    then obtain competitor :: "('e, 'f) floatSingleNaN"
      where competitor_nearest:
          "fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor"
        and competitor_even: "fp_even_lsb competitor"
      by blast
    obtain y :: "('e, 'f) float"
      where competitor: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using fp_nearest_finiteD(1)[OF competitor_nearest]
      by (rule finite_single_nan_representation)
    have y_fraction_even: "even (IEEE.fraction y)"
      using competitor_even y_finite competitor by simp
    have y_dynamic_even: "even (fraction_field (runtime_bits y))"
      using y_fraction_even by simp
    obtain z :: nat where y_magnitude:
        "finite_magnitude f (runtime_bits y) =
          of_nat z * minimum_subnormal_step f"
      and z_even: "even z"
      by (rule finite_magnitude_even_minimum_grid_coefficient[
            OF valid y_dynamic_even])
    have competitor_nearest_y:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d))
          (single_nan_of_float y)"
      using competitor_nearest unfolding competitor .
    have same_sign_equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits
                  f Fp_Round_Int.RNE negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
            exact_input_value negative n d\<bar>"
      unfolding f_def result_def
      by (rule subnormal_nearest_raw_same_sign_error_equal[OF
            width numerator denominator subnormal_runtime
            disjI1[OF refl] y_finite competitor_nearest_y])
    have scaled_equal:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat ?m - of_nat ?p / of_nat ?q\<bar>"
      by (rule subnormal_same_sign_error_equal_scaled[OF
            valid numerator denominator subnormal y_magnitude
            same_sign_equal])
    have qpos: "0 < ?q"
      by (rule scaled_denominator_pos[OF denominator])
    have scaled_equal_unfolded:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat (round_integer Fp_Round_Int.RNE negative ?p ?q) -
            of_nat ?p / of_nat ?q\<bar>"
      using scaled_equal by (simp add: scaled_round_integer_def)
    have rounded_integer_even:
        "even (round_integer Fp_Round_Int.RNE negative ?p ?q)"
      by (rule RNE_equal_error_even_preference[OF
            qpos scaled_equal_unfolded z_even])
    have m_even: "even ?m"
      using rounded_integer_even by (simp add: scaled_round_integer_def)
    have logarithm:
        "floor_log2_rel n d (floor_log2_spec n d)"
      by (rule floor_log2_spec_correct_positive[OF numerator denominator])
    have bound: "?m \<le> 2 ^ fraction_bits f"
      by (rule subnormal_rounded_significand_upper[OF
            denominator logarithm subnormal])
    have output_fraction_even:
        "even (fraction_field
          (round_rational_to_format_bits
            f Fp_Round_Int.RNE negative n d))"
    proof -
      have core:
          "round_rational_core f Fp_Round_Int.RNE negative n d =
            \<lparr>core_significand = ?m,
              core_exponent = format_emin f,
              core_is_subnormal = True\<rparr>"
        using subnormal
        by (simp add: round_rational_core_def
            round_rational_core_at_subnormal)
      have encoded:
          "round_rational_to_format_bits
              f Fp_Round_Int.RNE negative n d =
            subnormal_result_bits f negative ?m"
        by (simp add: round_rational_to_format_bits_def core
            encode_rounded_core_def)
      show ?thesis
        unfolding encoded
        by (rule subnormal_result_fraction_even[OF valid bound m_even])
    qed
    let ?raw =
      "afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float"
    have raw_finite: "IEEE.is_finite ?raw"
      using fp_nearest_finiteD(1)[OF nearest]
      unfolding result_def by simp
    have fields:
        "runtime_bits ?raw =
          round_rational_to_format_bits
            f Fp_Round_Int.RNE negative n d"
      unfolding f_def
      by (rule afp_round_rational_fields[OF width numerator denominator])
    have raw_even: "even (IEEE.fraction ?raw)"
      using output_fraction_even fields by (metis runtime_bits_fields(3))
    show "fp_even_lsb result"
      using single_nan_of_float_even_lsb[OF raw_finite] raw_even
      by (simp add: result_def)
  qed
qed

lemma subnormal_outward_coefficient:
  assumes denominator: "0 < d"
      and magnitude:
        "finite_magnitude f b = of_nat z * minimum_subnormal_step f"
      and outward:
        "exact_magnitude n d \<le> finite_magnitude f b"
  shows
    "of_nat (scaled_numerator n d
        (int (fraction_bits f) - format_emin f)) /
      of_nat (scaled_denominator n d
        (int (fraction_bits f) - format_emin f)) \<le>
      (of_nat z :: rat)"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        exact_magnitude n d * rat_pow2 ?k"
    using scale_ratio_exact[OF denominator, of n ?k]
    by (simp add: exact_magnitude_def)
  have nonnegative: "0 \<le> rat_pow2 ?k" by simp
  have multiplied:
      "exact_magnitude n d * rat_pow2 ?k \<le>
        (of_nat z * minimum_subnormal_step f) * rat_pow2 ?k"
    using outward magnitude
    by (intro mult_right_mono[OF _ nonnegative]) simp
  have cancellation:
      "minimum_subnormal_step f * rat_pow2 ?k = 1"
  proof -
    have exponent:
        "format_emin f - int (fraction_bits f) = - ?k"
      by simp
    show ?thesis
      unfolding minimum_subnormal_step_def pow2_rat_eq_rat_pow2 exponent
      by (rule rat_pow2_neg_cancel_left)
  qed
  show ?thesis
    using scale multiplied cancellation by (simp add: mult.assoc)
qed

lemma subnormal_scaled_round_outward:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and scaled_outward:
        "(of_nat (scaled_numerator n d
            (int (fraction_bits f) - format_emin f)) :: rat) /
          of_nat (scaled_denominator n d
            (int (fraction_bits f) - format_emin f)) \<le>
          of_nat (scaled_round_integer Fp_Round_Int.RNA negative n d
            (int (fraction_bits f) - format_emin f))"
  shows
    "exact_magnitude n d \<le>
      finite_magnitude f
        (round_rational_to_format_bits
          f Fp_Round_Int.RNA negative n d)"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  let ?m = "scaled_round_integer Fp_Round_Int.RNA negative n d ?k"
  have output_grid:
      "signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits
              f Fp_Round_Int.RNA negative n d)) =
        rounded_grid_value Fp_Round_Int.RNA negative n d ?k"
    by (rule round_rational_to_format_bits_subnormal_signed_value[OF
          valid numerator denominator subnormal])
  have output_magnitude:
      "finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        of_nat ?m * rat_pow2 (- ?k)"
  proof -
    have absolute:
        "\<bar>signed_rat negative
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d))\<bar> =
          \<bar>rounded_grid_value Fp_Round_Int.RNA negative n d ?k\<bar>"
      by (rule arg_cong[OF output_grid])
    show ?thesis
      using absolute
      by (cases negative)
        (simp_all add: rounded_grid_value_def grid_point_value_def)
  qed
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        exact_magnitude n d * rat_pow2 ?k"
    using scale_ratio_exact[OF denominator, of n ?k]
    by (simp add: exact_magnitude_def)
  have step_nonnegative: "0 \<le> rat_pow2 (- ?k)" by simp
  have multiplied:
      "((of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k)) * rat_pow2 (- ?k) \<le>
        of_nat ?m * rat_pow2 (- ?k)"
    by (rule mult_right_mono[OF scaled_outward step_nonnegative])
  have exact_unscaled:
      "((of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k)) * rat_pow2 (- ?k) =
        exact_magnitude n d"
  proof -
    have cancellation: "rat_pow2 ?k * rat_pow2 (- ?k) = 1"
      by (rule rat_pow2_neg_cancel)
    show ?thesis using scale cancellation by (simp add: mult.assoc)
  qed
  show ?thesis
    using multiplied exact_unscaled output_magnitude by simp
qed

theorem afp_round_rational_subnormal_RNA_preferred_nearest:
  fixes negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
  shows
    "fp_preferred_nearest
      (\<lambda>b. \<bar>valof b\<bar> \<ge>
        \<bar>of_rat (exact_input_value negative n d)\<bar>)
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  let ?p = "scaled_numerator n d ?k"
  let ?q = "scaled_denominator n d ?k"
  let ?m = "scaled_round_integer Fp_Round_Int.RNA negative n d ?k"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have subnormal_runtime:
      "floor_log2_spec n d <
        format_emin (runtime_format TYPE(('e, 'f) float))"
    using subnormal unfolding f_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_subnormal_nearest_finite[OF
          width numerator denominator subnormal_runtime]) simp
  show ?thesis
    unfolding fp_preferred_nearest_def
  proof (intro conjI impI)
    show "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
      by (rule nearest)
    assume preferred_exists:
        "\<exists>competitor::('e, 'f) floatSingleNaN.
          fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor \<and>
          \<bar>valof competitor\<bar> \<ge>
            \<bar>of_rat (exact_input_value negative n d)\<bar>"
    then obtain competitor :: "('e, 'f) floatSingleNaN"
      where competitor_nearest:
          "fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor"
        and competitor_outward:
          "\<bar>valof competitor\<bar> \<ge>
            \<bar>of_rat (exact_input_value negative n d)\<bar>"
      by blast
    obtain y :: "('e, 'f) float"
      where competitor: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using fp_nearest_finiteD(1)[OF competitor_nearest]
      by (rule finite_single_nan_representation)
    obtain z :: nat where y_magnitude:
        "finite_magnitude f (runtime_bits y) =
          of_nat z * minimum_subnormal_step f"
      by (rule finite_magnitude_on_minimum_subnormal_grid)
    have competitor_value: "valof competitor = IEEE.valof y"
      unfolding competitor by (rule single_nan_of_float_valof[OF y_finite])
    have exact_absolute:
        "\<bar>(of_rat (exact_input_value negative n d) :: real)\<bar> =
          of_rat (exact_magnitude n d)"
      using denominator
      by (simp add: exact_input_value_as_magnitude exact_magnitude_def)
    have y_absolute:
        "\<bar>IEEE.valof y\<bar> =
          of_rat (finite_magnitude f (runtime_bits y))"
      using runtime_magnitude_eq_abs_valof[of y]
      unfolding f_def by simp
    have y_outward:
        "exact_magnitude n d \<le> finite_magnitude f (runtime_bits y)"
      using competitor_outward competitor_value exact_absolute y_absolute
      by (simp only: of_rat_less_eq)
    have z_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le> of_nat z"
      by (rule subnormal_outward_coefficient[OF
            denominator y_magnitude y_outward])
    have competitor_nearest_y:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d))
          (single_nan_of_float y)"
      using competitor_nearest unfolding competitor .
    have same_sign_equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits
                  f Fp_Round_Int.RNA negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
            exact_input_value negative n d\<bar>"
      unfolding f_def result_def
      by (rule subnormal_nearest_raw_same_sign_error_equal[OF
            width numerator denominator subnormal_runtime
            disjI2[OF refl] y_finite competitor_nearest_y])
    have scaled_equal:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat ?m - of_nat ?p / of_nat ?q\<bar>"
      by (rule subnormal_same_sign_error_equal_scaled[OF
            valid numerator denominator subnormal y_magnitude
            same_sign_equal])
    have qpos: "0 < ?q"
      by (rule scaled_denominator_pos[OF denominator])
    have scaled_equal_unfolded:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat (round_integer Fp_Round_Int.RNA negative ?p ?q) -
            of_nat ?p / of_nat ?q\<bar>"
      using scaled_equal by (simp add: scaled_round_integer_def)
    have rounded_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le>
          of_nat (round_integer Fp_Round_Int.RNA negative ?p ?q)"
      by (rule RNA_equal_error_outward_preference[OF
            qpos scaled_equal_unfolded z_outward])
    have scaled_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le> of_nat ?m"
      using rounded_outward by (simp add: scaled_round_integer_def)
    have output_outward:
        "exact_magnitude n d \<le>
          finite_magnitude f
            (round_rational_to_format_bits
              f Fp_Round_Int.RNA negative n d)"
      by (rule subnormal_scaled_round_outward[OF
            valid numerator denominator subnormal scaled_outward])
    have result_value:
        "valof result =
          of_rat (signed_rat negative
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d)))"
      unfolding f_def result_def
      by (rule subnormal_afp_result_finite_and_value(2)[OF
            width numerator denominator subnormal_runtime disjI2[OF refl]])
    show "\<bar>valof result\<bar> \<ge>
        \<bar>of_rat (exact_input_value negative n d)\<bar>"
      using output_outward result_value exact_absolute
      by (simp only: abs_of_rat abs_signed_rat of_rat_less_eq)
  qed
qed

section \<open>Normal-binade output and equally-near competitors\<close>

lemma round_rational_to_format_bits_normal_signed_value:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> floor_log2_spec n d"
      and no_overflow:
        "core_exponent (round_rational_core f rm negative n d) \<le>
          format_emax f"
  shows
    "signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)) =
      rounded_grid_value rm negative n d
        (int (fraction_bits f) - floor_log2_spec n d)"
proof -
  let ?c = "round_rational_core f rm negative n d"
  have core_normal: "\<not> core_is_subnormal ?c"
    using normal
    by (simp add: round_rational_core_def round_rational_core_at_def
        apply_significand_carry_def)
  have decoded:
      "decode_bits f
          (round_rational_to_format_bits f rm negative n d) =
        Dynamic_Finite negative (rounded_core_magnitude f ?c)"
    by (rule decode_round_rational_to_format_bits_finite[OF
          valid numerator denominator])
      (use core_normal no_overflow in blast)
  have magnitude:
      "finite_magnitude f
          (round_rational_to_format_bits f rm negative n d) =
        rounded_core_magnitude f ?c"
    by (rule finite_magnitude_from_dynamic_decode[OF decoded])
  have core_grid:
      "rounded_core_value f negative ?c =
        rounded_grid_value rm negative n d
          (int (fraction_bits f) - floor_log2_spec n d)"
    using round_rational_core_value[OF valid] normal
    by simp
  show ?thesis
    using magnitude core_grid
    by (simp add: rounded_core_value_def)
qed

lemma normal_afp_result_finite_and_value:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and e :: int and c :: rounded_core
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and e_def: "e \<equiv> floor_log2_spec n d"
    and c_def: "c \<equiv> round_rational_core_at f rm negative n d e"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> e"
      and no_overflow: "core_exponent c \<le> format_emax f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
  shows
    "is_finite result"
    "valof result =
      of_rat (signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)))"
proof -
  have normal_runtime:
      "format_emin (runtime_format TYPE(('e, 'f) float)) \<le>
        floor_log2_spec n d"
    using normal unfolding f_def e_def .
  have no_overflow_runtime:
      "core_exponent
          (round_rational_core_at
            (runtime_format TYPE(('e, 'f) float)) rm negative n d
            (floor_log2_spec n d)) \<le>
        format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow unfolding f_def e_def c_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_normal_nearest_finite[OF
          width numerator denominator normal_runtime no_overflow_runtime
          nearest_mode])
  show finite: "is_finite result"
    by (rule fp_nearest_finiteD(1)[OF nearest])
  let ?raw = "afp_round_rational rm negative n d :: ('e, 'f) float"
  have raw_finite: "IEEE.is_finite ?raw"
    using finite unfolding result_def by simp
  have fields:
      "runtime_bits ?raw =
        round_rational_to_format_bits f rm negative n d"
    unfolding f_def
    by (rule afp_round_rational_fields[OF width numerator denominator])
  have raw_sign:
      "IEEE.sign ?raw = (if negative then 1 else 0)"
    by (rule afp_round_rational_sign[OF width numerator denominator])
  have sign_eq: "(IEEE.sign ?raw = 1) = negative"
    using raw_sign by (cases negative) simp_all
  have quotient_value: "valof result = IEEE.valof ?raw"
    unfolding result_def by (rule single_nan_of_float_valof[OF raw_finite])
  have raw_value:
      "IEEE.valof ?raw =
        of_rat (signed_rat (IEEE.sign ?raw = 1)
          (finite_magnitude
            (runtime_format TYPE(('e, 'f) float)) (runtime_bits ?raw)))"
    using runtime_value_eq_signed_magnitude[of ?raw] by simp
  show "valof result =
      of_rat (signed_rat negative
        (finite_magnitude f
          (round_rational_to_format_bits f rm negative n d)))"
    using quotient_value raw_value fields sign_eq unfolding f_def by simp
qed

lemma normal_nearest_raw_same_sign_error_equal:
  fixes rm :: fp_round_mode and negative :: bool and n d :: nat
    and f :: binary_format and e :: int and c :: rounded_core
    and y :: "('e::len, 'f::len) float"
    and result competitor :: "('e, 'f) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and e_def: "e \<equiv> floor_log2_spec n d"
    and c_def: "c \<equiv> round_rational_core_at f rm negative n d e"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational rm negative n d :: ('e, 'f) float)"
    and competitor_def: "competitor \<equiv> single_nan_of_float y"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> e"
      and no_overflow: "core_exponent c \<le> format_emax f"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and y_finite: "IEEE.is_finite y"
      and competitor_nearest:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d)) competitor"
  shows
    "\<bar>signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f rm negative n d)) -
        exact_input_value negative n d\<bar> =
      \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
        exact_input_value negative n d\<bar>"
proof -
  let ?bits = "round_rational_to_format_bits f rm negative n d"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have normal_runtime:
      "format_emin (runtime_format TYPE(('e, 'f) float)) \<le>
        floor_log2_spec n d"
    using normal unfolding f_def e_def .
  have no_overflow_runtime:
      "core_exponent
          (round_rational_core_at
            (runtime_format TYPE(('e, 'f) float)) rm negative n d
            (floor_log2_spec n d)) \<le>
        format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow unfolding f_def e_def c_def .
  have result_nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_normal_nearest_finite[OF
          width numerator denominator normal_runtime no_overflow_runtime
          nearest_mode])
  have result_value:
      "valof result =
        of_rat (signed_rat negative (finite_magnitude f ?bits))"
    unfolding f_def e_def c_def result_def
    by (rule normal_afp_result_finite_and_value(2)[OF
          width numerator denominator normal_runtime no_overflow_runtime
          nearest_mode])
  have competitor_value:
      "valof competitor =
        of_rat (signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)))"
    using single_nan_value_eq_signed_magnitude[OF y_finite]
    unfolding competitor_def f_def by simp
  have real_equal:
      "\<bar>valof result - of_rat (exact_input_value negative n d)\<bar> =
       \<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar>"
  proof (rule antisym)
    show
      "\<bar>valof result - of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar>"
      by (rule fp_nearest_finiteD(2)[OF result_nearest])
        (rule fp_nearest_finiteD(1)[OF competitor_nearest])
    show
      "\<bar>valof competitor - of_rat (exact_input_value negative n d)\<bar> \<le>
       \<bar>valof result - of_rat (exact_input_value negative n d)\<bar>"
      by (rule fp_nearest_finiteD(2)[OF competitor_nearest])
        (rule fp_nearest_finiteD(1)[OF result_nearest])
  qed
  have actual_equal:
      "\<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> =
       \<bar>signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
    using real_equal result_value competitor_value
    by (simp only: abs_real_of_rat_diff of_rat_eq_iff)
  have logarithm: "floor_log2_rel n d e"
    unfolding e_def by (rule floor_log2_spec_correct_positive[
          OF numerator denominator])
  have y_well_formed: "bits_well_formed f (runtime_bits y)"
    unfolding f_def by simp
  have y_exponent:
      "exponent_field (runtime_bits y) < exponent_all_ones f"
    unfolding f_def by (rule finite_runtime_bits_exponent[OF width y_finite])
  have core_nearest:
      "\<bar>rounded_core_value f negative
            (round_rational_core_at f rm negative n d e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
    by (rule round_rational_core_at_normal_nearest_finite[OF
          valid denominator logarithm normal nearest_mode
          y_well_formed y_exponent])
  have output_value:
      "signed_rat negative (finite_magnitude f ?bits) =
        rounded_core_value f negative
          (round_rational_core_at f rm negative n d e)"
  proof -
    have normal_core:
        "format_emin f \<le> floor_log2_spec n d"
      using normal unfolding e_def .
    have no_overflow_core:
        "core_exponent (round_rational_core f rm negative n d) \<le>
          format_emax f"
      using no_overflow
      unfolding c_def e_def round_rational_core_def .
    have grid:
        "signed_rat negative (finite_magnitude f ?bits) =
          rounded_grid_value rm negative n d
            (int (fraction_bits f) - e)"
      using round_rational_to_format_bits_normal_signed_value[OF
        valid numerator denominator normal_core no_overflow_core]
      unfolding e_def by simp
    have core_grid:
        "rounded_core_value f negative
            (round_rational_core_at f rm negative n d e) =
          rounded_grid_value rm negative n d
            (int (fraction_bits f) - e)"
      using round_rational_core_at_value[OF valid] normal by simp
    show ?thesis using grid core_grid by simp
  qed
  have output_le_same:
      "\<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
    using core_nearest output_value by simp
  have same_le_actual:
      "\<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat (IEEE.sign y = 1)
          (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar>"
  proof -
    have exact_nonnegative: "0 \<le> exact_magnitude n d"
      using denominator by (simp add: exact_magnitude_def)
    show ?thesis
      unfolding exact_input_value_as_magnitude
      by (rule same_sign_competitor_no_farther[OF
            exact_nonnegative finite_magnitude_nonnegative])
  qed
  have same_le_output:
      "\<bar>signed_rat negative (finite_magnitude f (runtime_bits y)) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (finite_magnitude f ?bits) -
          exact_input_value negative n d\<bar>"
    using same_le_actual actual_equal by linarith
  show ?thesis
    by (rule antisym[OF output_le_same same_le_output])
qed


lemma normal_equal_nearest_competitor_above_boundary:
  assumes denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and nearest_mode:
        "rm = Fp_Round_Int.RNE \<or> rm = Fp_Round_Int.RNA"
      and equal:
        "\<bar>rounded_grid_value rm negative n d
              (int (fraction_bits f) - e) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative (finite_magnitude f b) -
            exact_input_value negative n d\<bar>"
  shows "pow2_rat e \<le> finite_magnitude f b"
proof (rule ccontr)
  assume not_above:
      "\<not> pow2_rat e \<le> finite_magnitude f b"
  then have competitor_below:
      "finite_magnitude f b < pow2_rat e"
    by simp
  have input_above:
      "pow2_rat e \<le> exact_magnitude n d"
    using logarithm by (simp add: floor_log2_rel_def)
  have unsigned_strict:
      "\<bar>pow2_rat e - exact_magnitude n d\<bar> <
       \<bar>finite_magnitude f b - exact_magnitude n d\<bar>"
    using competitor_below input_above
    by (simp add: abs_of_nonpos; linarith)
  have boundary_strict:
      "\<bar>signed_rat negative (pow2_rat e) -
          exact_input_value negative n d\<bar> <
       \<bar>signed_rat negative (finite_magnitude f b) -
          exact_input_value negative n d\<bar>"
    unfolding exact_input_value_as_magnitude
    using unsigned_strict by (simp only: abs_signed_rat_diff)
  have local_nearest:
      "\<bar>rounded_grid_value rm negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>grid_point_value negative
            (int (fraction_bits f) - e) (2 ^ fraction_bits f) -
          exact_input_value negative n d\<bar>"
  proof (cases "rm = Fp_Round_Int.RNE")
    case True
    show ?thesis
      using grid_RNE_nearest_grid_point[
        OF denominator, of negative n
          "int (fraction_bits f) - e" "2 ^ fraction_bits f"] True
      by simp
  next
    case False
    with nearest_mode have mode: "rm = Fp_Round_Int.RNA" by blast
    show ?thesis
      using grid_RNA_nearest_grid_point[
        OF denominator, of negative n
          "int (fraction_bits f) - e" "2 ^ fraction_bits f"] mode
      by simp
  qed
  have boundary_grid:
      "grid_point_value negative
          (int (fraction_bits f) - e) (2 ^ fraction_bits f) =
        signed_rat negative (pow2_rat e)"
    by (rule normal_binade_boundary_grid_point)
  have output_le_boundary:
      "\<bar>rounded_grid_value rm negative n d
            (int (fraction_bits f) - e) -
          exact_input_value negative n d\<bar> \<le>
       \<bar>signed_rat negative (pow2_rat e) -
          exact_input_value negative n d\<bar>"
    using local_nearest boundary_grid by simp
  show False
    using equal output_le_boundary boundary_strict by linarith
qed

lemma finite_magnitude_even_normal_grid_coefficient:
  assumes valid: "valid_format f"
      and well_formed: "bits_well_formed f b"
      and exponent_lower: "format_emin f \<le> e"
      and magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
      and fraction_even: "even (fraction_field b)"
  obtains z :: nat where
    "finite_magnitude f b =
      of_nat z * pow2_rat (e - int (fraction_bits f))"
    "even z"
proof -
  have positive_exponent: "0 < exponent_field b"
    by (rule finite_magnitude_above_power_is_normal[
          OF well_formed exponent_lower magnitude_lower])
  have exponent_order:
      "e \<le> stored_unbiased_exponent f b"
    by (rule finite_magnitude_above_power_exponent[
          OF well_formed magnitude_lower positive_exponent])
  let ?g = "stored_unbiased_exponent f b"
  let ?delta = "nat (?g - e)"
  let ?z =
    "(2 ^ fraction_bits f + fraction_field b) * 2 ^ ?delta"
  have delta: "int ?delta = ?g - e"
    using exponent_order by simp
  have exponent_decomposition:
      "?g - int (fraction_bits f) =
        (e - int (fraction_bits f)) + int ?delta"
    using delta by linarith
  have scale_decomposition:
      "pow2_rat (?g - int (fraction_bits f)) =
        of_nat (2 ^ ?delta) *
          pow2_rat (e - int (fraction_bits f))"
  proof -
    have "pow2_rat (?g - int (fraction_bits f)) =
        pow2_rat ((e - int (fraction_bits f)) + int ?delta)"
      by (rule arg_cong[OF exponent_decomposition])
    also have "... =
        pow2_rat (e - int (fraction_bits f)) *
          pow2_rat (int ?delta)"
      by (rule pow2_rat_add)
    also have "... =
        of_nat (2 ^ ?delta) *
          pow2_rat (e - int (fraction_bits f))"
    proof -
      have power:
          "pow2_rat (int ?delta) = (of_nat (2 ^ ?delta) :: rat)"
        by (rule pow2_rat_nat)
      show ?thesis
        by (subst power) (simp add: mult.commute)
    qed
    finally show ?thesis .
  qed
  have magnitude:
      "finite_magnitude f b =
        of_nat ?z * pow2_rat (e - int (fraction_bits f))"
    using finite_magnitude_normal_binade_grid[OF positive_exponent]
      scale_decomposition
    by (simp add: of_nat_mult algebra_simps)
  have boundary_even: "even ((2::nat) ^ fraction_bits f)"
    using valid_format_fraction_bits_pos[OF valid] by simp
  have coefficient_even:
      "even (2 ^ fraction_bits f + fraction_field b)"
    using boundary_even fraction_even by simp
  have z_even: "even ?z"
    using coefficient_even by simp
  show thesis
    by (rule that[OF magnitude z_even])
qed

lemma normal_same_sign_error_equal_scaled:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and no_overflow:
        "core_exponent (round_rational_core f rm negative n d) \<le>
          format_emax f"
      and magnitude:
        "finite_magnitude f b =
          of_nat z * pow2_rat
            (floor_log2_spec n d - int (fraction_bits f))"
      and equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits f rm negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative (finite_magnitude f b) -
            exact_input_value negative n d\<bar>"
  shows
    "\<bar>(of_nat z :: rat) -
        of_nat (scaled_numerator n d
          (int (fraction_bits f) - floor_log2_spec n d)) /
        of_nat (scaled_denominator n d
          (int (fraction_bits f) - floor_log2_spec n d))\<bar> =
     \<bar>of_nat (scaled_round_integer rm negative n d
          (int (fraction_bits f) - floor_log2_spec n d)) -
        of_nat (scaled_numerator n d
          (int (fraction_bits f) - floor_log2_spec n d)) /
        of_nat (scaled_denominator n d
          (int (fraction_bits f) - floor_log2_spec n d))\<bar>"
proof -
  let ?e = "floor_log2_spec n d"
  let ?k = "int (fraction_bits f) - ?e"
  have output_grid:
      "signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits f rm negative n d)) =
        rounded_grid_value rm negative n d ?k"
    by (rule round_rational_to_format_bits_normal_signed_value[
          OF valid numerator denominator normal no_overflow])
  have competitor_grid:
      "signed_rat negative (finite_magnitude f b) =
        grid_point_value negative ?k z"
    using magnitude
    by (simp add: grid_point_value_def pow2_rat_eq_rat_pow2)
  have grid_equal:
      "\<bar>rounded_grid_value rm negative n d ?k -
          exact_input_value negative n d\<bar> =
       \<bar>grid_point_value negative ?k z -
          exact_input_value negative n d\<bar>"
    using equal output_grid competitor_grid by simp
  have output_unscale:
      "\<bar>scaled_rounded_value rm negative n d ?k -
          scaled_exact_value negative n d ?k\<bar> * rat_pow2 (- ?k) =
       \<bar>rounded_grid_value rm negative n d ?k -
          exact_input_value negative n d\<bar>"
    by (rule rounded_grid_error_unscale)
  have competitor_unscale:
      "\<bar>signed_rat negative (of_nat z) -
          scaled_exact_value negative n d ?k\<bar> * rat_pow2 (- ?k) =
       \<bar>grid_point_value negative ?k z -
          exact_input_value negative n d\<bar>"
    by (rule grid_point_error_unscale)
  have step_nonzero: "rat_pow2 (- ?k) \<noteq> 0"
    using rat_pow2_pos[of "- ?k"] by linarith
  have scaled_equal:
      "\<bar>signed_rat negative (of_nat z) -
          scaled_exact_value negative n d ?k\<bar> =
       \<bar>scaled_rounded_value rm negative n d ?k -
          scaled_exact_value negative n d ?k\<bar>"
    using grid_equal output_unscale competitor_unscale step_nonzero
    by (metis mult_right_cancel)
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        (of_nat n / of_nat d) * rat_pow2 ?k"
    by (rule scale_ratio_exact[OF denominator])
  show ?thesis
    using scaled_equal scale
    by (cases negative)
      (simp_all add: scaled_exact_value_def scaled_rounded_value_def
        abs_minus_commute)
qed


theorem afp_round_rational_normal_RNE_preferred_nearest:
  fixes negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational Fp_Round_Int.RNE negative n d ::
          ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNE negative n d) \<le>
            format_emax f"
  shows
    "fp_preferred_nearest fp_even_lsb
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?e = "floor_log2_spec n d"
  let ?k = "int (fraction_bits f) - ?e"
  let ?p = "scaled_numerator n d ?k"
  let ?q = "scaled_denominator n d ?k"
  let ?m = "scaled_round_integer Fp_Round_Int.RNE negative n d ?k"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have normal_runtime:
      "format_emin (runtime_format TYPE(('e, 'f) float)) \<le>
        floor_log2_spec n d"
    using normal unfolding f_def .
  have no_overflow_runtime:
      "core_exponent
          (round_rational_core_at
            (runtime_format TYPE(('e, 'f) float))
            Fp_Round_Int.RNE negative n d (floor_log2_spec n d)) \<le>
        format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow
    unfolding f_def round_rational_core_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_normal_nearest_finite[
          OF width numerator denominator normal_runtime
            no_overflow_runtime disjI1[OF refl]])
  show ?thesis
    unfolding fp_preferred_nearest_def
  proof (intro conjI impI)
    show "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
      by (rule nearest)
    assume preferred_exists:
        "\<exists>competitor::('e, 'f) floatSingleNaN.
          fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor \<and>
          fp_even_lsb competitor"
    then obtain competitor :: "('e, 'f) floatSingleNaN"
      where competitor_nearest:
          "fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor"
        and competitor_even: "fp_even_lsb competitor"
      by blast
    obtain y :: "('e, 'f) float"
      where competitor: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using fp_nearest_finiteD(1)[OF competitor_nearest]
      by (rule finite_single_nan_representation)
    have competitor_nearest_y:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d))
          (single_nan_of_float y)"
      using competitor_nearest unfolding competitor .
    have y_fraction_even: "even (IEEE.fraction y)"
      using competitor_even y_finite competitor by simp
    have y_dynamic_even:
        "even (fraction_field (runtime_bits y))"
      using y_fraction_even by simp
    have y_well_formed:
        "bits_well_formed f (runtime_bits y)"
      unfolding f_def by simp
    have same_sign_equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits
                  f Fp_Round_Int.RNE negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative
              (finite_magnitude f (runtime_bits y)) -
            exact_input_value negative n d\<bar>"
      unfolding f_def result_def
      by (rule normal_nearest_raw_same_sign_error_equal[
            OF width numerator denominator normal_runtime
              no_overflow_runtime disjI1[OF refl]
              y_finite competitor_nearest_y])
    have output_grid:
        "signed_rat negative
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNE negative n d)) =
          rounded_grid_value Fp_Round_Int.RNE negative n d ?k"
      by (rule round_rational_to_format_bits_normal_signed_value[
            OF valid numerator denominator normal no_overflow])
    have grid_equal:
        "\<bar>rounded_grid_value Fp_Round_Int.RNE negative n d ?k -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative
              (finite_magnitude f (runtime_bits y)) -
            exact_input_value negative n d\<bar>"
      using same_sign_equal output_grid by simp
    have logarithm: "floor_log2_rel n d ?e"
      by (rule floor_log2_spec_correct_positive[
            OF numerator denominator])
    have y_above:
        "pow2_rat ?e \<le> finite_magnitude f (runtime_bits y)"
      by (rule normal_equal_nearest_competitor_above_boundary[
            OF denominator logarithm disjI1[OF refl] grid_equal])
    obtain z :: nat where y_magnitude:
        "finite_magnitude f (runtime_bits y) =
          of_nat z * pow2_rat (?e - int (fraction_bits f))"
      and z_even: "even z"
      by (rule finite_magnitude_even_normal_grid_coefficient[
            OF valid y_well_formed normal y_above y_dynamic_even])
    have scaled_equal:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat ?m - of_nat ?p / of_nat ?q\<bar>"
      by (rule normal_same_sign_error_equal_scaled[
            OF valid numerator denominator normal no_overflow
              y_magnitude same_sign_equal])
    have qpos: "0 < ?q"
      by (rule scaled_denominator_pos[OF denominator])
    have scaled_equal_unfolded:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat
              (round_integer Fp_Round_Int.RNE negative ?p ?q) -
            of_nat ?p / of_nat ?q\<bar>"
      using scaled_equal by (simp add: scaled_round_integer_def)
    have rounded_integer_even:
        "even (round_integer Fp_Round_Int.RNE negative ?p ?q)"
      by (rule RNE_equal_error_even_preference[
            OF qpos scaled_equal_unfolded z_even])
    have m_even: "even ?m"
      using rounded_integer_even
      by (simp add: scaled_round_integer_def)
    have bounds:
        "2 ^ fraction_bits f \<le> ?m \<and>
         ?m \<le> 2 ^ precision_bits f"
      by (rule normal_rounded_significand_bounds[
            OF valid denominator logarithm])
    have core:
        "round_rational_core
            f Fp_Round_Int.RNE negative n d =
          apply_significand_carry f ?m ?e"
      unfolding round_rational_core_def
      by (rule round_rational_core_at_normal[OF normal])
    have output_fraction_even:
        "even (fraction_field
          (round_rational_to_format_bits
            f Fp_Round_Int.RNE negative n d))"
      unfolding round_rational_to_format_bits_def core
      by (rule apply_significand_carry_fraction_even[
            OF valid bounds[THEN conjunct1] bounds[THEN conjunct2]
              m_even])
        (use no_overflow core in simp)
    let ?raw =
      "afp_round_rational Fp_Round_Int.RNE negative n d ::
        ('e, 'f) float"
    have raw_finite: "IEEE.is_finite ?raw"
      using fp_nearest_finiteD(1)[OF nearest]
      unfolding result_def by simp
    have fields:
        "runtime_bits ?raw =
          round_rational_to_format_bits
            f Fp_Round_Int.RNE negative n d"
      unfolding f_def
      by (rule afp_round_rational_fields[
            OF width numerator denominator])
    have raw_even: "even (IEEE.fraction ?raw)"
      using output_fraction_even fields
      by (metis runtime_bits_fields(3))
    show "fp_even_lsb result"
      using single_nan_of_float_even_lsb[OF raw_finite] raw_even
      by (simp add: result_def)
  qed
qed


lemma normal_outward_coefficient:
  assumes denominator: "0 < d"
      and magnitude:
        "finite_magnitude f b =
          of_nat z * pow2_rat (e - int (fraction_bits f))"
      and outward:
        "exact_magnitude n d \<le> finite_magnitude f b"
  shows
    "of_nat (scaled_numerator n d
        (int (fraction_bits f) - e)) /
      of_nat (scaled_denominator n d
        (int (fraction_bits f) - e)) \<le>
      (of_nat z :: rat)"
proof -
  let ?k = "int (fraction_bits f) - e"
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        exact_magnitude n d * rat_pow2 ?k"
    using scale_ratio_exact[OF denominator, of n ?k]
    by (simp add: exact_magnitude_def)
  have nonnegative: "0 \<le> rat_pow2 ?k" by simp
  have multiplied:
      "exact_magnitude n d * rat_pow2 ?k \<le>
        (of_nat z * pow2_rat
          (e - int (fraction_bits f))) * rat_pow2 ?k"
    using outward magnitude
    by (intro mult_right_mono[OF _ nonnegative]) simp
  have exponent:
      "e - int (fraction_bits f) = - ?k"
    by simp
  have cancellation:
      "pow2_rat (e - int (fraction_bits f)) * rat_pow2 ?k = 1"
    unfolding pow2_rat_eq_rat_pow2 exponent
    by (rule rat_pow2_neg_cancel_left)
  show ?thesis
    using scale multiplied cancellation by (simp add: mult.assoc)
qed

lemma normal_scaled_round_outward:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and no_overflow:
        "core_exponent
          (round_rational_core
            f Fp_Round_Int.RNA negative n d) \<le>
          format_emax f"
      and scaled_outward:
        "(of_nat (scaled_numerator n d
            (int (fraction_bits f) - floor_log2_spec n d)) :: rat) /
          of_nat (scaled_denominator n d
            (int (fraction_bits f) - floor_log2_spec n d)) \<le>
          of_nat (scaled_round_integer Fp_Round_Int.RNA negative n d
            (int (fraction_bits f) - floor_log2_spec n d))"
  shows
    "exact_magnitude n d \<le>
      finite_magnitude f
        (round_rational_to_format_bits
          f Fp_Round_Int.RNA negative n d)"
proof -
  let ?e = "floor_log2_spec n d"
  let ?k = "int (fraction_bits f) - ?e"
  let ?m = "scaled_round_integer Fp_Round_Int.RNA negative n d ?k"
  have output_grid:
      "signed_rat negative
          (finite_magnitude f
            (round_rational_to_format_bits
              f Fp_Round_Int.RNA negative n d)) =
        rounded_grid_value Fp_Round_Int.RNA negative n d ?k"
    by (rule round_rational_to_format_bits_normal_signed_value[
          OF valid numerator denominator normal no_overflow])
  have output_magnitude:
      "finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        of_nat ?m * rat_pow2 (- ?k)"
  proof -
    have absolute:
        "\<bar>signed_rat negative
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d))\<bar> =
          \<bar>rounded_grid_value
              Fp_Round_Int.RNA negative n d ?k\<bar>"
      by (rule arg_cong[OF output_grid])
    show ?thesis
      using absolute
      by (cases negative)
        (simp_all add: rounded_grid_value_def grid_point_value_def)
  qed
  have scale:
      "(of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k) =
        exact_magnitude n d * rat_pow2 ?k"
    using scale_ratio_exact[OF denominator, of n ?k]
    by (simp add: exact_magnitude_def)
  have step_nonnegative: "0 \<le> rat_pow2 (- ?k)" by simp
  have multiplied:
      "((of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k)) * rat_pow2 (- ?k) \<le>
        of_nat ?m * rat_pow2 (- ?k)"
    by (rule mult_right_mono[OF scaled_outward step_nonnegative])
  have exact_unscaled:
      "((of_nat (scaled_numerator n d ?k) :: rat) /
          of_nat (scaled_denominator n d ?k)) * rat_pow2 (- ?k) =
        exact_magnitude n d"
  proof -
    have cancellation: "rat_pow2 ?k * rat_pow2 (- ?k) = 1"
      by (rule rat_pow2_neg_cancel)
    show ?thesis
      using scale cancellation by (simp add: mult.assoc)
  qed
  show ?thesis
    using multiplied exact_unscaled output_magnitude by simp
qed


theorem afp_round_rational_normal_RNA_preferred_nearest:
  fixes negative :: bool and n d :: nat
    and f :: binary_format
    and result :: "('e::len, 'f::len) floatSingleNaN"
  defines f_def:
      "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and result_def:
      "result \<equiv> single_nan_of_float
        (afp_round_rational Fp_Round_Int.RNA negative n d ::
          ('e, 'f) float)"
  assumes width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNA negative n d) \<le>
            format_emax f"
  shows
    "fp_preferred_nearest
      (\<lambda>b. \<bar>valof b\<bar> \<ge>
        \<bar>of_rat (exact_input_value negative n d)\<bar>)
      (of_rat (exact_input_value negative n d)) result"
proof -
  let ?e = "floor_log2_spec n d"
  let ?k = "int (fraction_bits f) - ?e"
  let ?p = "scaled_numerator n d ?k"
  let ?q = "scaled_denominator n d ?k"
  let ?m = "scaled_round_integer Fp_Round_Int.RNA negative n d ?k"
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF width])
  have normal_runtime:
      "format_emin (runtime_format TYPE(('e, 'f) float)) \<le>
        floor_log2_spec n d"
    using normal unfolding f_def .
  have no_overflow_runtime:
      "core_exponent
          (round_rational_core_at
            (runtime_format TYPE(('e, 'f) float))
            Fp_Round_Int.RNA negative n d (floor_log2_spec n d)) \<le>
        format_emax (runtime_format TYPE(('e, 'f) float))"
    using no_overflow
    unfolding f_def round_rational_core_def .
  have nearest:
      "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
    unfolding result_def
    by (rule afp_round_rational_normal_nearest_finite[
          OF width numerator denominator normal_runtime
            no_overflow_runtime disjI2[OF refl]])
  show ?thesis
    unfolding fp_preferred_nearest_def
  proof (intro conjI impI)
    show "fp_nearest_finite
        (of_rat (exact_input_value negative n d)) result"
      by (rule nearest)
    assume preferred_exists:
        "\<exists>competitor::('e, 'f) floatSingleNaN.
          fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor \<and>
          \<bar>valof competitor\<bar> \<ge>
            \<bar>of_rat (exact_input_value negative n d)\<bar>"
    then obtain competitor :: "('e, 'f) floatSingleNaN"
      where competitor_nearest:
          "fp_nearest_finite
            (of_rat (exact_input_value negative n d)) competitor"
        and competitor_outward:
          "\<bar>valof competitor\<bar> \<ge>
            \<bar>of_rat (exact_input_value negative n d)\<bar>"
      by blast
    obtain y :: "('e, 'f) float"
      where competitor: "competitor = single_nan_of_float y"
        and y_finite: "IEEE.is_finite y"
      using fp_nearest_finiteD(1)[OF competitor_nearest]
      by (rule finite_single_nan_representation)
    have competitor_nearest_y:
        "fp_nearest_finite
          (of_rat (exact_input_value negative n d))
          (single_nan_of_float y)"
      using competitor_nearest unfolding competitor .
    have y_well_formed:
        "bits_well_formed f (runtime_bits y)"
      unfolding f_def by simp
    have y_exponent:
        "exponent_field (runtime_bits y) < exponent_all_ones f"
      unfolding f_def
      by (rule finite_runtime_bits_exponent[OF width y_finite])
    have competitor_value: "valof competitor = IEEE.valof y"
      unfolding competitor
      by (rule single_nan_of_float_valof[OF y_finite])
    have exact_absolute:
        "\<bar>(of_rat (exact_input_value negative n d) :: real)\<bar> =
          of_rat (exact_magnitude n d)"
      using denominator
      by (simp add: exact_input_value_as_magnitude exact_magnitude_def)
    have y_absolute:
        "\<bar>IEEE.valof y\<bar> =
          of_rat (finite_magnitude f (runtime_bits y))"
      using runtime_magnitude_eq_abs_valof[of y]
      unfolding f_def by simp
    have y_outward:
        "exact_magnitude n d \<le>
          finite_magnitude f (runtime_bits y)"
      using competitor_outward competitor_value
        exact_absolute y_absolute
      by (simp only: of_rat_less_eq)
    have logarithm: "floor_log2_rel n d ?e"
      by (rule floor_log2_spec_correct_positive[
            OF numerator denominator])
    have input_above:
        "pow2_rat ?e \<le> exact_magnitude n d"
      using logarithm by (simp add: floor_log2_rel_def)
    have y_above:
        "pow2_rat ?e \<le> finite_magnitude f (runtime_bits y)"
      using input_above y_outward by linarith
    obtain z :: nat where y_magnitude:
        "finite_magnitude f (runtime_bits y) =
          of_nat z * pow2_rat (?e - int (fraction_bits f))"
      by (rule finite_magnitude_above_power_on_grid[
            OF valid y_well_formed y_exponent normal y_above])
    have z_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le> of_nat z"
      by (rule normal_outward_coefficient[
            OF denominator y_magnitude y_outward])
    have same_sign_equal:
        "\<bar>signed_rat negative
              (finite_magnitude f
                (round_rational_to_format_bits
                  f Fp_Round_Int.RNA negative n d)) -
            exact_input_value negative n d\<bar> =
         \<bar>signed_rat negative
              (finite_magnitude f (runtime_bits y)) -
            exact_input_value negative n d\<bar>"
      unfolding f_def result_def
      by (rule normal_nearest_raw_same_sign_error_equal[
            OF width numerator denominator normal_runtime
              no_overflow_runtime disjI2[OF refl]
              y_finite competitor_nearest_y])
    have scaled_equal:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat ?m - of_nat ?p / of_nat ?q\<bar>"
      by (rule normal_same_sign_error_equal_scaled[
            OF valid numerator denominator normal no_overflow
              y_magnitude same_sign_equal])
    have qpos: "0 < ?q"
      by (rule scaled_denominator_pos[OF denominator])
    have scaled_equal_unfolded:
        "\<bar>(of_nat z :: rat) - of_nat ?p / of_nat ?q\<bar> =
         \<bar>of_nat
              (round_integer Fp_Round_Int.RNA negative ?p ?q) -
            of_nat ?p / of_nat ?q\<bar>"
      using scaled_equal by (simp add: scaled_round_integer_def)
    have rounded_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le>
          of_nat (round_integer Fp_Round_Int.RNA negative ?p ?q)"
      by (rule RNA_equal_error_outward_preference[
            OF qpos scaled_equal_unfolded z_outward])
    have scaled_outward:
        "(of_nat ?p :: rat) / of_nat ?q \<le> of_nat ?m"
      using rounded_outward
      by (simp add: scaled_round_integer_def)
    have output_outward:
        "exact_magnitude n d \<le>
          finite_magnitude f
            (round_rational_to_format_bits
              f Fp_Round_Int.RNA negative n d)"
      by (rule normal_scaled_round_outward[
            OF valid numerator denominator normal no_overflow
              scaled_outward])
    have result_value:
        "valof result =
          of_rat (signed_rat negative
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d)))"
      unfolding f_def result_def
      by (rule normal_afp_result_finite_and_value(2)[
            OF width numerator denominator normal_runtime
              no_overflow_runtime disjI2[OF refl]])
    show "\<bar>valof result\<bar> \<ge>
        \<bar>of_rat (exact_input_value negative n d)\<bar>"
      using output_outward result_value exact_absolute
      by (simp only: abs_of_rat abs_signed_rat of_rat_less_eq)
  qed
qed

end

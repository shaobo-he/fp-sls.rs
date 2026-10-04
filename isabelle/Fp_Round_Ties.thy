(* SPDX-License-Identifier: MIT *)

section \<open>Tie preferences of exact rational rounding\<close>

theory Fp_Round_Ties
  imports
    Fp_Round_Normal
    Fp_Round_Subnormal
    Fp_Round_IEEE
    Fp_SingleNaN_Bridge
begin

text \<open>
  Integer rounding already establishes the two numerical tie policies: RNE
  chooses an even integer, and RNA chooses the upper magnitude.  This theory
  shows that the subsequent format-specific boundary operations preserve
  those policies.  A normal significand carry and promotion of the largest
  subnormal candidate both produce a stored fraction of zero.
\<close>

section \<open>Parity through field encoding\<close>

lemma normal_result_fraction_even:
  assumes valid: "valid_format f"
      and lower: "2 ^ fraction_bits f \<le> m"
      and rounded_even: "even m"
  shows "even (fraction_field (normal_result_bits f negative m e))"
proof -
  have boundary_even: "even ((2::nat) ^ fraction_bits f)"
    using valid_format_fraction_bits_pos[OF valid] by simp
  show ?thesis
    using lower rounded_even boundary_even
    by (simp add: normal_result_bits_def)
qed

lemma subnormal_result_fraction_even:
  assumes valid: "valid_format f"
      and bound: "m \<le> 2 ^ fraction_bits f"
      and rounded_even: "even m"
  shows "even (fraction_field (subnormal_result_bits f negative m))"
proof (cases "m < 2 ^ fraction_bits f")
  case True
  then have field:
      "fraction_field (subnormal_result_bits f negative m) = m"
    by (rule subnormal_result_fields_below(2))
  show ?thesis using rounded_even by (simp add: field)
next
  case False
  with bound have boundary: "m = 2 ^ fraction_bits f" by simp
  have fraction_pos: "0 < fraction_bits f"
    by (rule valid_format_fraction_bits_pos[OF valid])
  have field:
      "fraction_field (subnormal_result_bits f negative m) = 0"
    using subnormal_result_fields_at_boundary(2)[OF fraction_pos, of negative]
      boundary
    by simp
  show ?thesis by (simp add: field)
qed

lemma apply_significand_carry_fraction_even:
  assumes valid: "valid_format f"
      and lower: "2 ^ fraction_bits f \<le> m"
      and upper: "m \<le> 2 ^ precision_bits f"
      and rounded_even: "even m"
      and no_overflow:
        "core_exponent (apply_significand_carry f m e) \<le> format_emax f"
  shows
    "even (fraction_field
      (encode_rounded_core f rm negative
        (apply_significand_carry f m e)))"
proof (cases "m = 2 ^ precision_bits f")
  case carry: True
  have precision_pos: "0 < precision_bits f"
    using valid by (simp add: valid_format_def)
  have core:
      "apply_significand_carry f m e =
        \<lparr>core_significand = 2 ^ fraction_bits f,
          core_exponent = e + 1, core_is_subnormal = False\<rparr>"
    using carry carry_at_precision[OF precision_pos, of e] by simp
  show ?thesis
    using no_overflow
    by (simp add: core encode_rounded_core_def normal_result_bits_def)
next
  case no_carry: False
  have core:
      "apply_significand_carry f m e =
        \<lparr>core_significand = m, core_exponent = e,
          core_is_subnormal = False\<rparr>"
    by (rule no_significand_carry[OF no_carry])
  have field_even:
      "even (fraction_field (normal_result_bits f negative m e))"
    by (rule normal_result_fraction_even[OF valid lower rounded_even])
  show ?thesis
    using no_overflow field_even
    by (simp add: core encode_rounded_core_def)
qed

section \<open>RNE ties in each rounding branch\<close>

theorem encode_round_rational_core_at_normal_RNE_tie_even:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and tie:
        "scaled_denominator n d (int (fraction_bits f) - e) =
          2 * (scaled_numerator n d (int (fraction_bits f) - e) mod
            scaled_denominator n d (int (fraction_bits f) - e))"
      and no_overflow:
        "core_exponent (round_rational_core_at f Fp_Round_Int.RNE negative n d e)
          \<le> format_emax f"
  shows
    "even (fraction_field
      (encode_rounded_core f Fp_Round_Int.RNE negative
        (round_rational_core_at f Fp_Round_Int.RNE negative n d e)))"
proof -
  let ?k = "int (fraction_bits f) - e"
  let ?m = "scaled_round_integer Fp_Round_Int.RNE negative n d ?k"
  have bounds:
      "2 ^ fraction_bits f \<le> ?m \<and>
       ?m \<le> 2 ^ precision_bits f"
    by (rule normal_rounded_significand_bounds[OF
          valid denominator logarithm])
  have rounded_even: "even ?m"
    by (rule scaled_RNE_tie_even[OF denominator tie])
  have core:
      "round_rational_core_at f Fp_Round_Int.RNE negative n d e =
        apply_significand_carry f ?m e"
    by (rule round_rational_core_at_normal[OF normal])
  show ?thesis
    unfolding core
    by (rule apply_significand_carry_fraction_even[OF
          valid bounds[THEN conjunct1] bounds[THEN conjunct2]
          rounded_even])
      (use no_overflow core in simp)
qed

theorem encode_round_rational_core_at_subnormal_RNE_tie_even:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and logarithm: "floor_log2_rel n d e"
      and subnormal: "e < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
  shows
    "even (fraction_field
      (encode_rounded_core f Fp_Round_Int.RNE negative
        (round_rational_core_at f Fp_Round_Int.RNE negative n d e)))"
proof -
  let ?k = "int (fraction_bits f) - format_emin f"
  let ?m = "scaled_round_integer Fp_Round_Int.RNE negative n d ?k"
  have bound: "?m \<le> 2 ^ fraction_bits f"
    by (rule subnormal_rounded_significand_upper[OF
          denominator logarithm subnormal])
  have rounded_even: "even ?m"
    by (rule scaled_RNE_tie_even[OF denominator tie])
  have core:
      "round_rational_core_at f Fp_Round_Int.RNE negative n d e =
        \<lparr>core_significand = ?m, core_exponent = format_emin f,
          core_is_subnormal = True\<rparr>"
    by (rule round_rational_core_at_subnormal[OF subnormal])
  show ?thesis
    using subnormal_result_fraction_even[OF valid bound rounded_even,
        of negative]
    by (simp add: core encode_rounded_core_def)
qed

section \<open>RNA ties point away from zero\<close>

lemma scaled_RNA_tie_strictly_above:
  assumes denominator: "0 < d"
      and tie:
        "scaled_denominator n d k =
          2 * (scaled_numerator n d k mod scaled_denominator n d k)"
  shows
    "(of_nat n / of_nat d) <
      of_nat (scaled_round_integer Fp_Round_Int.RNA negative n d k) * rat_pow2 (- k)"
proof -
  let ?p = "scaled_numerator n d k"
  let ?q = "scaled_denominator n d k"
  have qpos: "0 < ?q" by (rule scaled_denominator_pos[OF denominator])
  have rounded:
      "scaled_round_integer Fp_Round_Int.RNA negative n d k = ?p div ?q + 1"
    by (rule scaled_RNA_tie_away[OF denominator tie])
  have quotient_upper: "?p < (?p div ?q + 1) * ?q"
    using dividend_less_div_times[OF qpos, of ?p]
    by (simp add: add_mult_distrib ac_simps)
  have qrat: "0 < (of_nat ?q :: rat)" using qpos by simp
  have scaled_less:
      "(of_nat ?p :: rat) / of_nat ?q <
        of_nat (?p div ?q + 1)"
  proof -
    have cast:
        "(of_nat ?p :: rat) < of_nat (?p div ?q + 1) * of_nat ?q"
      using quotient_upper
      by (simp only: of_nat_mult[symmetric] of_nat_less_iff)
    show ?thesis
      using cast by (simp only: pos_divide_less_eq[OF qrat])
  qed
  have scale:
      "(of_nat ?p :: rat) / of_nat ?q =
        (of_nat n / of_nat d) * rat_pow2 k"
    by (rule scale_ratio_exact[OF denominator])
  have positive_step: "0 < rat_pow2 (- k)" by simp
  have multiplied:
      "((of_nat n / of_nat d) * rat_pow2 k) * rat_pow2 (- k) <
        of_nat (?p div ?q + 1) * rat_pow2 (- k)"
    using scaled_less scale
    by (intro mult_strict_right_mono[OF _ positive_step]) simp
  show ?thesis
    using multiplied rounded
    by (simp add: mult.assoc)
qed

lemma grid_RNA_tie_strictly_away:
  assumes denominator: "0 < d"
      and tie:
        "scaled_denominator n d k =
          2 * (scaled_numerator n d k mod scaled_denominator n d k)"
  shows
    "\<bar>exact_input_value negative n d\<bar> <
      \<bar>rounded_grid_value Fp_Round_Int.RNA negative n d k\<bar>"
proof -
  have away:
      "(of_nat n / of_nat d :: rat) <
        of_nat (scaled_round_integer Fp_Round_Int.RNA negative n d k) * rat_pow2 (- k)"
    by (rule scaled_RNA_tie_strictly_above[OF denominator tie])
  have ratio_nonnegative: "0 \<le> (of_nat n / of_nat d :: rat)"
    using denominator by simp
  show ?thesis
    using away ratio_nonnegative
    by (cases negative)
      (simp_all add: exact_input_value_def rounded_grid_value_def
        grid_point_value_def)
qed

theorem round_rational_core_at_normal_RNA_tie_strictly_away:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> e"
      and tie:
        "scaled_denominator n d (int (fraction_bits f) - e) =
          2 * (scaled_numerator n d (int (fraction_bits f) - e) mod
            scaled_denominator n d (int (fraction_bits f) - e))"
  shows
    "\<bar>exact_input_value negative n d\<bar> <
      rounded_core_magnitude f
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e)"
proof -
  have core_value:
      "rounded_core_value f negative
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e) =
        rounded_grid_value Fp_Round_Int.RNA negative n d
          (int (fraction_bits f) - e)"
    using round_rational_core_at_value[OF valid, of negative Fp_Round_Int.RNA n d e]
      normal
    by simp
  have away:
      "\<bar>exact_input_value negative n d\<bar> <
        \<bar>rounded_grid_value Fp_Round_Int.RNA negative n d
          (int (fraction_bits f) - e)\<bar>"
    by (rule grid_RNA_tie_strictly_away[OF denominator tie])
  have away_core:
      "\<bar>exact_input_value negative n d\<bar> <
        \<bar>rounded_core_value f negative
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e)\<bar>"
    using away core_value by simp
  show ?thesis
    using away_core by simp
qed

theorem round_rational_core_at_subnormal_RNA_tie_strictly_away:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and subnormal: "e < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
  shows
    "\<bar>exact_input_value negative n d\<bar> <
      rounded_core_magnitude f
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e)"
proof -
  have core_value:
      "rounded_core_value f negative
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e) =
        rounded_grid_value Fp_Round_Int.RNA negative n d
          (int (fraction_bits f) - format_emin f)"
    using round_rational_core_at_value[OF valid, of negative Fp_Round_Int.RNA n d e]
      subnormal
    by simp
  have away:
      "\<bar>exact_input_value negative n d\<bar> <
        \<bar>rounded_grid_value Fp_Round_Int.RNA negative n d
          (int (fraction_bits f) - format_emin f)\<bar>"
    by (rule grid_RNA_tie_strictly_away[OF denominator tie])
  have away_core:
      "\<bar>exact_input_value negative n d\<bar> <
        \<bar>rounded_core_value f negative
          (round_rational_core_at f Fp_Round_Int.RNA negative n d e)\<bar>"
    using away core_value by simp
  show ?thesis
    using away_core by simp
qed

section \<open>Whole-conversion consequences\<close>

definition exact_input_real :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "exact_input_real negative n d = of_rat (exact_input_value negative n d)"

lemma finite_magnitude_from_dynamic_decode:
  assumes decoded: "decode_bits f b = Dynamic_Finite negative magnitude"
  shows "finite_magnitude f b = magnitude"
  using decoded
  by (auto simp: decode_bits_def split: if_splits)

lemma runtime_float_of_bits_finite_from_dynamic_decode:
  fixes b :: fp_bits
  assumes well_formed:
        "bits_well_formed
          (runtime_format TYPE(('e::len, 'f::len) float)) b"
      and decoded:
        "decode_bits (runtime_format TYPE(('e, 'f) float)) b =
          Dynamic_Finite negative magnitude"
  shows "IEEE.is_finite (runtime_float_of_bits b :: ('e, 'f) float)"
proof -
  let ?x = "runtime_float_of_bits b :: ('e, 'f) float"
  have fields: "runtime_bits ?x = b"
    by (rule runtime_bits_of_runtime_float[OF well_formed])
  have not_nan:
      "\<not> bits_is_nan (runtime_format TYPE(('e, 'f) float)) b"
    using decoded
    by (auto simp: decode_bits_def split: if_splits)
  have not_infinity:
      "\<not> bits_is_infinity (runtime_format TYPE(('e, 'f) float)) b"
    using decoded
    by (auto simp: decode_bits_def split: if_splits)
  have raw_not_nan: "\<not> IEEE.is_nan ?x"
  proof -
    have agreement:
        "bits_is_nan (runtime_format TYPE(('e, 'f) float))
            (runtime_bits ?x) \<longleftrightarrow> IEEE.is_nan ?x"
      by (rule runtime_bits_is_nan_iff)
    show ?thesis using agreement fields not_nan by simp
  qed
  have raw_not_infinity: "\<not> IEEE.is_infinity ?x"
  proof -
    have agreement:
        "bits_is_infinity (runtime_format TYPE(('e, 'f) float))
            (runtime_bits ?x) \<longleftrightarrow> IEEE.is_infinity ?x"
      by (rule runtime_bits_is_infinity_iff)
    show ?thesis using agreement fields not_infinity by simp
  qed
  show ?thesis
    using float_cases_finite[of ?x] raw_not_nan raw_not_infinity
    by blast
qed

lemma decode_round_rational_to_format_bits_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f rm negative n d) \<or>
         core_exponent (round_rational_core f rm negative n d) \<le>
           format_emax f"
  shows
    "decode_bits f (round_rational_to_format_bits f rm negative n d) =
      Dynamic_Finite negative
        (rounded_core_magnitude f
          (round_rational_core f rm negative n d))"
proof -
  have invariant:
      "core_encoding_invariant f
        (round_rational_core f rm negative n d)"
    by (rule round_rational_core_invariant[OF
          valid numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def
    by (rule decode_encode_rounded_core_finite[OF
          valid invariant no_overflow])
qed

lemma afp_round_rational_finite_if_no_overflow:
  fixes rm :: fp_round_mode
  assumes exponent_width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal
          (round_rational_core
            (runtime_format TYPE(('e, 'f::len) float)) rm negative n d) \<or>
         core_exponent
          (round_rational_core
            (runtime_format TYPE(('e, 'f) float)) rm negative n d) \<le>
           format_emax (runtime_format TYPE(('e, 'f) float))"
  shows
    "IEEE.is_finite
      (afp_round_rational rm negative n d :: ('e, 'f) float)"
proof -
  let ?format = "runtime_format TYPE(('e, 'f) float)"
  let ?bits = "round_rational_to_format_bits ?format rm negative n d"
  have valid: "valid_format ?format"
    by (rule runtime_format_valid[OF exponent_width])
  have well_formed: "bits_well_formed ?format ?bits"
    by (rule round_rational_to_format_bits_well_formed[OF
          valid numerator denominator])
  have decoded:
      "decode_bits ?format ?bits =
        Dynamic_Finite negative
          (rounded_core_magnitude ?format
            (round_rational_core ?format rm negative n d))"
    by (rule decode_round_rational_to_format_bits_finite[OF
          valid numerator denominator no_overflow])
  show ?thesis
    unfolding afp_round_rational_def
    by (rule runtime_float_of_bits_finite_from_dynamic_decode[OF
          well_formed decoded])
qed

theorem round_rational_to_format_bits_normal_RNE_tie_even:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - floor_log2_spec n d) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - floor_log2_spec n d) mod
            scaled_denominator n d
              (int (fraction_bits f) - floor_log2_spec n d))"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNE negative n d) \<le>
            format_emax f"
  shows
    "even (fraction_field
      (round_rational_to_format_bits
        f Fp_Round_Int.RNE negative n d))"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct)
      (rule floor_log2_rel_exists[OF numerator denominator])
  have no_overflow_at:
      "core_exponent
        (round_rational_core_at f Fp_Round_Int.RNE negative n d
          (floor_log2_spec n d)) \<le> format_emax f"
    using no_overflow by (simp add: round_rational_core_def)
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    by (rule encode_round_rational_core_at_normal_RNE_tie_even[OF
          valid denominator logarithm normal tie no_overflow_at])
qed

theorem round_rational_to_format_bits_subnormal_RNE_tie_even:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
  shows
    "even (fraction_field
      (round_rational_to_format_bits
        f Fp_Round_Int.RNE negative n d))"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct)
      (rule floor_log2_rel_exists[OF numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def round_rational_core_def
    by (rule encode_round_rational_core_at_subnormal_RNE_tie_even[OF
          valid denominator logarithm subnormal tie])
qed

theorem round_rational_to_format_bits_normal_RNA_tie_away:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal:
        "format_emin f \<le> floor_log2_spec n d"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - floor_log2_spec n d) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - floor_log2_spec n d) mod
            scaled_denominator n d
              (int (fraction_bits f) - floor_log2_spec n d))"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNA negative n d) \<le>
            format_emax f"
  shows
    "\<bar>exact_input_value negative n d\<bar> <
      finite_magnitude f
        (round_rational_to_format_bits
          f Fp_Round_Int.RNA negative n d)"
proof -
  have logarithm:
      "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct)
      (rule floor_log2_rel_exists[OF numerator denominator])
  have core_away:
      "\<bar>exact_input_value negative n d\<bar> <
        rounded_core_magnitude f
          (round_rational_core f Fp_Round_Int.RNA negative n d)"
    unfolding round_rational_core_def
    by (rule round_rational_core_at_normal_RNA_tie_strictly_away[OF
          valid denominator normal tie])
  have core_normal:
      "\<not> core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNA negative n d)"
    using normal
    by (simp add: round_rational_core_def
        round_rational_core_at_def apply_significand_carry_def)
  have decoded:
      "decode_bits f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        Dynamic_Finite negative
          (rounded_core_magnitude f
            (round_rational_core f Fp_Round_Int.RNA negative n d))"
    by (rule decode_round_rational_to_format_bits_finite[OF
          valid numerator denominator])
      (use core_normal no_overflow in blast)
  have magnitude:
      "finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        rounded_core_magnitude f
          (round_rational_core f Fp_Round_Int.RNA negative n d)"
    by (rule finite_magnitude_from_dynamic_decode[OF decoded])
  show ?thesis using core_away magnitude by simp
qed

theorem round_rational_to_format_bits_subnormal_RNA_tie_away:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal:
        "floor_log2_spec n d < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
  shows
    "\<bar>exact_input_value negative n d\<bar> <
      finite_magnitude f
        (round_rational_to_format_bits
          f Fp_Round_Int.RNA negative n d)"
proof -
  have core_away:
      "\<bar>exact_input_value negative n d\<bar> <
        rounded_core_magnitude f
          (round_rational_core f Fp_Round_Int.RNA negative n d)"
    unfolding round_rational_core_def
    by (rule round_rational_core_at_subnormal_RNA_tie_strictly_away[OF
          valid denominator subnormal tie])
  have core_subnormal:
      "core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNA negative n d)"
    using subnormal
    by (simp add: round_rational_core_def round_rational_core_at_def)
  have decoded:
      "decode_bits f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        Dynamic_Finite negative
          (rounded_core_magnitude f
            (round_rational_core f Fp_Round_Int.RNA negative n d))"
    by (rule decode_round_rational_to_format_bits_finite[OF
          valid numerator denominator])
      (use core_subnormal in blast)
  have magnitude:
      "finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d) =
        rounded_core_magnitude f
          (round_rational_core f Fp_Round_Int.RNA negative n d)"
    by (rule finite_magnitude_from_dynamic_decode[OF decoded])
  show ?thesis using core_away magnitude by simp
qed

section \<open>Conditional AFP preference theorems\<close>

theorem rne_normal_preference_result:
  fixes negative :: bool and n d :: nat
  defines f_def:
    "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and a_def: "a \<equiv> single_nan_of_float
      (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float)"
  assumes exponent_width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> floor_log2_spec n d"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - floor_log2_spec n d) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - floor_log2_spec n d) mod
            scaled_denominator n d
              (int (fraction_bits f) - floor_log2_spec n d))"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNE negative n d) \<le>
            format_emax f"
      and nearest: "fp_nearest_finite (exact_input_real negative n d) a"
  shows
    "fp_preferred_nearest fp_even_lsb
      (exact_input_real negative n d) a"
proof -
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF exponent_width])
  have dynamic_even:
      "even (fraction_field
        (round_rational_to_format_bits
          f Fp_Round_Int.RNE negative n d))"
    by (rule round_rational_to_format_bits_normal_RNE_tie_even[OF
          valid numerator denominator normal tie no_overflow])
  have fields:
      "runtime_bits
        (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float) =
       round_rational_to_format_bits
        f Fp_Round_Int.RNE negative n d"
    unfolding f_def
    by (rule afp_round_rational_fields[OF
          exponent_width numerator denominator])
  have core_normal:
      "\<not> core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNE negative n d)"
    using normal
    by (simp add: round_rational_core_def
        round_rational_core_at_def apply_significand_carry_def)
  have raw_finite:
      "IEEE.is_finite
        (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float)"
    unfolding f_def
    by (rule afp_round_rational_finite_if_no_overflow[OF
          exponent_width numerator denominator])
      (use core_normal no_overflow f_def in simp)
  have even_lsb: "fp_even_lsb a"
  proof -
    have raw_even:
        "even (IEEE.fraction
          (afp_round_rational Fp_Round_Int.RNE negative n d ::
            ('e, 'f) float))"
      using dynamic_even fields
      by (metis runtime_bits_fields(3))
    show ?thesis
      using single_nan_of_float_even_lsb[OF raw_finite] raw_even
      by (simp add: a_def)
  qed
  show ?thesis
    using nearest even_lsb
    by (simp add: fp_preferred_nearest_def)
qed

theorem rne_subnormal_preference_result:
  fixes negative :: bool and n d :: nat
  defines f_def:
    "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and a_def: "a \<equiv> single_nan_of_float
      (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float)"
  assumes exponent_width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
      and nearest: "fp_nearest_finite (exact_input_real negative n d) a"
  shows
    "fp_preferred_nearest fp_even_lsb
      (exact_input_real negative n d) a"
proof -
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF exponent_width])
  have dynamic_even:
      "even (fraction_field
        (round_rational_to_format_bits
          f Fp_Round_Int.RNE negative n d))"
    by (rule round_rational_to_format_bits_subnormal_RNE_tie_even[OF
          valid numerator denominator subnormal tie])
  have fields:
      "runtime_bits
        (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float) =
       round_rational_to_format_bits
        f Fp_Round_Int.RNE negative n d"
    unfolding f_def
    by (rule afp_round_rational_fields[OF
          exponent_width numerator denominator])
  have core_subnormal:
      "core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNE negative n d)"
    using subnormal
    by (simp add: round_rational_core_def round_rational_core_at_def)
  have raw_finite:
      "IEEE.is_finite
        (afp_round_rational Fp_Round_Int.RNE negative n d :: ('e, 'f) float)"
    unfolding f_def
    by (rule afp_round_rational_finite_if_no_overflow[OF
          exponent_width numerator denominator])
      (use core_subnormal f_def in simp)
  have even_lsb: "fp_even_lsb a"
  proof -
    have raw_even:
        "even (IEEE.fraction
          (afp_round_rational Fp_Round_Int.RNE negative n d ::
            ('e, 'f) float))"
      using dynamic_even fields
      by (metis runtime_bits_fields(3))
    show ?thesis
      using single_nan_of_float_even_lsb[OF raw_finite] raw_even
      by (simp add: a_def)
  qed
  show ?thesis
    using nearest even_lsb
    by (simp add: fp_preferred_nearest_def)
qed

theorem rna_normal_preference_result:
  fixes negative :: bool and n d :: nat
  defines f_def:
    "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and a_def: "a \<equiv> single_nan_of_float
      (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
  assumes exponent_width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and normal: "format_emin f \<le> floor_log2_spec n d"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - floor_log2_spec n d) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - floor_log2_spec n d) mod
            scaled_denominator n d
              (int (fraction_bits f) - floor_log2_spec n d))"
      and no_overflow:
        "core_exponent
          (round_rational_core f Fp_Round_Int.RNA negative n d) \<le>
            format_emax f"
      and nearest: "fp_nearest_finite (exact_input_real negative n d) a"
  shows
    "fp_preferred_nearest
      (\<lambda>b. \<bar>valof b\<bar> \<ge> \<bar>exact_input_real negative n d\<bar>)
      (exact_input_real negative n d) a"
proof -
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF exponent_width])
  have dynamic_away:
      "\<bar>exact_input_value negative n d\<bar> <
        finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d)"
    by (rule round_rational_to_format_bits_normal_RNA_tie_away[OF
          valid numerator denominator normal tie no_overflow])
  have core_normal:
      "\<not> core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNA negative n d)"
    using normal
    by (simp add: round_rational_core_def
        round_rational_core_at_def apply_significand_carry_def)
  have raw_finite:
      "IEEE.is_finite
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
    unfolding f_def
    by (rule afp_round_rational_finite_if_no_overflow[OF
          exponent_width numerator denominator])
      (use core_normal no_overflow f_def in simp)
  have magnitude:
      "(of_rat
        (finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d)) :: real) =
       \<bar>IEEE.valof
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)\<bar>"
    unfolding f_def
    by (rule afp_round_rational_magnitude[OF
          exponent_width numerator denominator])
  have raw_away:
      "\<bar>exact_input_real negative n d\<bar> <
       \<bar>IEEE.valof
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)\<bar>"
  proof -
    have cast_away:
        "(of_rat \<bar>exact_input_value negative n d\<bar> :: real) <
          of_rat
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d))"
      using dynamic_away by (simp only: of_rat_less)
    show ?thesis
      using cast_away magnitude
      by (simp add: exact_input_real_def)
  qed
  have quotient_value:
      "valof a =
        IEEE.valof
          (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
    using single_nan_of_float_valof[OF raw_finite]
    by (simp add: a_def)
  have preferred:
      "\<bar>valof a\<bar> \<ge> \<bar>exact_input_real negative n d\<bar>"
    using raw_away quotient_value by simp
  show ?thesis
    using nearest preferred
    by (simp add: fp_preferred_nearest_def)
qed

theorem rna_subnormal_preference_result:
  fixes negative :: bool and n d :: nat
  defines f_def:
    "f \<equiv> runtime_format TYPE(('e::len, 'f::len) float)"
    and a_def: "a \<equiv> single_nan_of_float
      (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
  assumes exponent_width: "2 \<le> LENGTH('e)"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and subnormal: "floor_log2_spec n d < format_emin f"
      and tie:
        "scaled_denominator n d
            (int (fraction_bits f) - format_emin f) =
          2 * (scaled_numerator n d
              (int (fraction_bits f) - format_emin f) mod
            scaled_denominator n d
              (int (fraction_bits f) - format_emin f))"
      and nearest: "fp_nearest_finite (exact_input_real negative n d) a"
  shows
    "fp_preferred_nearest
      (\<lambda>b. \<bar>valof b\<bar> \<ge> \<bar>exact_input_real negative n d\<bar>)
      (exact_input_real negative n d) a"
proof -
  have valid: "valid_format f"
    unfolding f_def by (rule runtime_format_valid[OF exponent_width])
  have dynamic_away:
      "\<bar>exact_input_value negative n d\<bar> <
        finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d)"
    by (rule round_rational_to_format_bits_subnormal_RNA_tie_away[OF
          valid numerator denominator subnormal tie])
  have core_subnormal:
      "core_is_subnormal
        (round_rational_core f Fp_Round_Int.RNA negative n d)"
    using subnormal
    by (simp add: round_rational_core_def round_rational_core_at_def)
  have raw_finite:
      "IEEE.is_finite
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
    unfolding f_def
    by (rule afp_round_rational_finite_if_no_overflow[OF
          exponent_width numerator denominator])
      (use core_subnormal f_def in simp)
  have magnitude:
      "(of_rat
        (finite_magnitude f
          (round_rational_to_format_bits
            f Fp_Round_Int.RNA negative n d)) :: real) =
       \<bar>IEEE.valof
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)\<bar>"
    unfolding f_def
    by (rule afp_round_rational_magnitude[OF
          exponent_width numerator denominator])
  have raw_away:
      "\<bar>exact_input_real negative n d\<bar> <
       \<bar>IEEE.valof
        (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)\<bar>"
  proof -
    have cast_away:
        "(of_rat \<bar>exact_input_value negative n d\<bar> :: real) <
          of_rat
            (finite_magnitude f
              (round_rational_to_format_bits
                f Fp_Round_Int.RNA negative n d))"
      using dynamic_away by (simp only: of_rat_less)
    show ?thesis
      using cast_away magnitude
      by (simp add: exact_input_real_def)
  qed
  have quotient_value:
      "valof a =
        IEEE.valof
          (afp_round_rational Fp_Round_Int.RNA negative n d :: ('e, 'f) float)"
    using single_nan_of_float_valof[OF raw_finite]
    by (simp add: a_def)
  have preferred:
      "\<bar>valof a\<bar> \<ge> \<bar>exact_input_real negative n d\<bar>"
    using raw_away quotient_value by simp
  show ?thesis
    using nearest preferred
    by (simp add: fp_preferred_nearest_def)
qed

end

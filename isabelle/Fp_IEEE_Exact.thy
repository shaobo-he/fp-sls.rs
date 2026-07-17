(* SPDX-License-Identifier: MIT *)

section \<open>Exact values in the IEEE rounding relation\<close>

theory Fp_IEEE_Exact
  imports Fp_IEEE_Spec
begin

text \<open>
  AFP proves the extremal-value bounds for its raw, payload-preserving float
  type.  The following lemmas expose the same facts for the single-NaN
  quotient used by the conversion specification.
\<close>

lemma fp_finite_le_largest:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "valof a \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
  using width finite
  unfolding fp_largest_def
  by transfer (auto dest: finite_infinity intro: float_val_le_largest)

lemma fp_finite_ge_minus_largest:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "- fp_largest TYPE(('e, 'f) floatSingleNaN) \<le> valof a"
  using width finite
  unfolding fp_largest_def
  by transfer (auto dest: finite_infinity intro: float_val_ge_largest)

lemma fp_finite_lt_threshold:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "valof a < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
  using width finite
  unfolding fp_threshold_def
  by transfer (auto dest: finite_infinity intro: float_val_lt_threshold)

lemma fp_finite_gt_minus_threshold:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "- fp_threshold TYPE(('e, 'f) floatSingleNaN) < valof a"
  using width finite
  unfolding fp_threshold_def
  by transfer (auto dest: finite_infinity intro: float_val_gt_threshold)

text \<open>
  Exact representable inputs are fixed points of RNA and all three directed
  modes.  RNE is also immediate whenever the exact representation has an even
  low bit; the remaining odd-low-bit case needs the finite-grid uniqueness
  result developed separately.
\<close>

lemma fp_round_RNA_exact:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "fp_round_rel RNA (valof a) a"
  using fp_finite_gt_minus_threshold[OF width finite]
    fp_finite_lt_threshold[OF width finite]
    fp_RNA_exact_choice[OF finite]
  by simp

lemma fp_round_RTP_exact:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "fp_round_rel RTP (valof a) a"
  using fp_finite_le_largest[OF width finite]
    fp_least_finite_above_exact[OF finite]
  by simp

lemma fp_round_RTN_exact:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
  shows "fp_round_rel RTN (valof a) a"
  using fp_finite_ge_minus_largest[OF width finite]
    fp_greatest_finite_below_exact[OF finite]
  by simp

lemma fp_round_RTZ_exact:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes finite: "is_finite a"
  shows "fp_round_rel RTZ (valof a) a"
  using fp_least_finite_above_exact[OF finite]
    fp_greatest_finite_below_exact[OF finite]
  by (cases "0 \<le> valof a") simp_all

lemma fp_round_RNE_exact_even:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes width: "1 < LENGTH('e)"
      and finite: "is_finite a"
      and even: "fp_even_lsb a"
  shows "fp_round_rel RNE (valof a) a"
proof -
  have preferred:
    "fp_preferred_nearest fp_even_lsb (valof a) a"
  proof (rule fp_preferred_nearestI)
    show "fp_nearest_finite (valof a) a"
      by (rule fp_nearest_finite_exact[OF finite])
    show "fp_even_lsb a" by (rule even)
  qed
  show ?thesis
    using fp_finite_gt_minus_threshold[OF width finite]
      fp_finite_lt_threshold[OF width finite] preferred
    by simp
qed

end

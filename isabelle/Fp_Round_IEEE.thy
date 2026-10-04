(* SPDX-License-Identifier: MIT *)

section \<open>Realizing the rational-rounding result as an AFP IEEE float\<close>

theory Fp_Round_IEEE
  imports Fp_Round_Format Fp_IEEE_Bridge Fp_IEEE_Spec
begin

text \<open>
  This is the representation-level end of the pure reference path.  The
  dynamic algorithm produces bounded natural-number fields; the AFP float
  below stores exactly those fields in words of the destination widths.
  Correct rounding with respect to @{const fp_signed_round_rel} is a stronger
  theorem and is deliberately kept separate from this lossless encoding fact.
\<close>

definition afp_round_rational ::
    "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ('e::len, 'f::len) float"
  where
    "afp_round_rational rm negative n d =
      runtime_float_of_bits
        (round_rational_to_format_bits
          (runtime_format TYPE(('e, 'f) float)) rm negative n d)"

lemma afp_round_rational_fields:
  assumes exponent_width: "2 \<le> LENGTH('e::len)"
      and numerator: "0 < n"
      and denominator: "0 < d"
  shows "runtime_bits
      (afp_round_rational rm negative n d :: ('e, 'f::len) float) =
    round_rational_to_format_bits
      (runtime_format TYPE(('e, 'f) float)) rm negative n d"
proof -
  have valid: "valid_format (runtime_format TYPE(('e, 'f) float))"
    by (rule runtime_format_valid[OF exponent_width])
  have well_formed:
    "bits_well_formed (runtime_format TYPE(('e, 'f) float))
      (round_rational_to_format_bits
        (runtime_format TYPE(('e, 'f) float)) rm negative n d)"
    by (rule round_rational_to_format_bits_well_formed
        [OF valid numerator denominator])
  show ?thesis
    unfolding afp_round_rational_def
    by (rule runtime_bits_of_runtime_float[OF well_formed])
qed

lemma afp_round_rational_sign:
  assumes "2 \<le> LENGTH('e::len)" "0 < n" "0 < d"
  shows "IEEE.sign
      (afp_round_rational rm negative n d :: ('e, 'f::len) float) =
    (if negative then 1 else 0)"
  by (simp add: afp_round_rational_def runtime_float_of_bits_def
      IEEE.sign.rep_eq IEEE.Abs_float_inverse)

lemma afp_round_rational_magnitude:
  assumes "2 \<le> LENGTH('e::len)" "0 < n" "0 < d"
  shows "(of_rat
      (finite_magnitude (runtime_format TYPE(('e, 'f::len) float))
        (round_rational_to_format_bits
          (runtime_format TYPE(('e, 'f) float)) rm negative n d)) :: real) =
    \<bar>IEEE.valof
      (afp_round_rational rm negative n d :: ('e, 'f) float)\<bar>"
proof -
  have fields:
    "runtime_bits
      (afp_round_rational rm negative n d :: ('e, 'f) float) =
     round_rational_to_format_bits
      (runtime_format TYPE(('e, 'f) float)) rm negative n d"
    by (rule afp_round_rational_fields[OF assms])
  from runtime_magnitude_eq_abs_valof[
      of "afp_round_rational rm negative n d :: ('e, 'f) float"] fields
  show ?thesis by simp
qed

theorem round_rational_has_afp_encoding:
  fixes rm :: fp_round_mode
    and negative :: bool
  assumes "2 \<le> LENGTH('e::len)" "0 < n" "0 < d"
  defines "b \<equiv> round_rational_to_format_bits
    (runtime_format TYPE(('e, 'f::len) float)) rm negative n d"
  shows "\<exists>x::('e, 'f) float.
    runtime_bits x = b \<and>
    IEEE.sign x = (if negative then 1 else 0) \<and>
    (of_rat (finite_magnitude
      (runtime_format TYPE(('e, 'f) float)) b) :: real) = \<bar>IEEE.valof x\<bar>"
proof (intro exI conjI)
  show "runtime_bits
      (afp_round_rational rm negative n d :: ('e, 'f) float) = b"
    unfolding b_def by (rule afp_round_rational_fields[OF assms(1-3)])
  show "IEEE.sign
      (afp_round_rational rm negative n d :: ('e, 'f) float) =
      (if negative then 1 else 0)"
    by (rule afp_round_rational_sign[OF assms(1-3)])
  show "(of_rat (finite_magnitude
      (runtime_format TYPE(('e, 'f) float)) b) :: real) =
      \<bar>IEEE.valof
        (afp_round_rational rm negative n d :: ('e, 'f) float)\<bar>"
    unfolding b_def by (rule afp_round_rational_magnitude[OF assms(1-3)])
qed

end

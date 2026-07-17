(* SPDX-License-Identifier: MIT *)

section \<open>Value denoted by the rounded core\<close>

theory Fp_Round_Local
  imports Fp_Round_Format Fp_Round_Value
begin

text \<open>
  The integer-rounding layer works in units of a selected power-of-two grid.
  This theory reconnects that grid value with the significand/exponent pair
  constructed by @{const round_rational_core_at}.  In particular, shifting a
  carried significand right by one while incrementing the exponent leaves the
  exact rational value unchanged.
\<close>

definition rounded_core_magnitude ::
    "binary_format \<Rightarrow> rounded_core \<Rightarrow> rat" where
  "rounded_core_magnitude f c =
    (if core_is_subnormal c then
       of_nat (core_significand c) *
         rat_pow2 (format_emin f - int (fraction_bits f))
     else
       of_nat (core_significand c) *
         rat_pow2 (core_exponent c - int (fraction_bits f)))"

definition rounded_core_value ::
    "binary_format \<Rightarrow> bool \<Rightarrow> rounded_core \<Rightarrow> rat" where
  "rounded_core_value f negative c =
    signed_rat negative (rounded_core_magnitude f c)"

lemma rounded_core_magnitude_nonnegative [simp]:
  "0 \<le> rounded_core_magnitude f c"
  by (simp add: rounded_core_magnitude_def)

lemma abs_rounded_core_value [simp]:
  "\<bar>rounded_core_value f negative c\<bar> = rounded_core_magnitude f c"
  by (simp add: rounded_core_value_def)

lemma rat_pow2_carry_step:
  "rat_pow2 (e + 1 - int p) = 2 * rat_pow2 (e - int p)"
proof -
  have exponent: "e + 1 - int p = (e - int p) + 1" by simp
  have "rat_pow2 (e + 1 - int p) =
      rat_pow2 (e - int p) * rat_pow2 1"
    unfolding exponent by (rule rat_pow2_add)
  also have "... = 2 * rat_pow2 (e - int p)"
    by (simp add: rat_pow2_def mult.commute)
  finally show ?thesis .
qed

lemma apply_significand_carry_value:
  assumes valid: "valid_format f"
  shows "rounded_core_value f negative (apply_significand_carry f m e) =
    grid_point_value negative (int (fraction_bits f) - e) m"
proof (cases "m = 2 ^ precision_bits f")
  case carry: True
  have precision:
    "precision_bits f = Suc (fraction_bits f)"
    by (rule valid_format_precision_as_fraction[OF valid])
  have half:
    "(2::nat) ^ precision_bits f div 2 = 2 ^ fraction_bits f"
    by (simp add: precision power_Suc)
  have step:
    "rat_pow2 (e + 1 - int (fraction_bits f)) =
      2 * rat_pow2 (e - int (fraction_bits f))"
    by (rule rat_pow2_carry_step)
  show ?thesis
    using carry half step
    by (cases negative)
      (simp_all add: apply_significand_carry_def rounded_core_value_def
        rounded_core_magnitude_def grid_point_value_def precision power_Suc
        mult_ac)
next
  case no_carry: False
  then show ?thesis
    by (simp add: apply_significand_carry_def rounded_core_value_def
        rounded_core_magnitude_def grid_point_value_def)
qed

lemma subnormal_core_value:
  "rounded_core_value f negative
      \<lparr>core_significand = m, core_exponent = format_emin f,
        core_is_subnormal = True\<rparr> =
    grid_point_value negative
      (int (fraction_bits f) - format_emin f) m"
  by (simp add: rounded_core_value_def rounded_core_magnitude_def
      grid_point_value_def)

theorem round_rational_core_at_value:
  assumes valid: "valid_format f"
  shows "rounded_core_value f negative
      (round_rational_core_at f rm negative n d e) =
    (if format_emin f \<le> e then
       rounded_grid_value rm negative n d
         (int (fraction_bits f) - e)
     else
       rounded_grid_value rm negative n d
         (int (fraction_bits f) - format_emin f))"
proof (cases "format_emin f \<le> e")
  case normal: True
  have core_value:
    "rounded_core_value f negative
       (apply_significand_carry f
         (scaled_round_integer rm negative n d
           (int (fraction_bits f) - e)) e) =
     grid_point_value negative (int (fraction_bits f) - e)
       (scaled_round_integer rm negative n d
         (int (fraction_bits f) - e))"
    by (rule apply_significand_carry_value[OF valid])
  from normal core_value show ?thesis
    by (simp add: round_rational_core_at_def)
next
  case subnormal: False
  have core_value:
    "rounded_core_value f negative
       \<lparr>core_significand = scaled_round_integer rm negative n d
           (int (fraction_bits f) - format_emin f),
         core_exponent = format_emin f,
         core_is_subnormal = True\<rparr> =
     grid_point_value negative
       (int (fraction_bits f) - format_emin f)
       (scaled_round_integer rm negative n d
         (int (fraction_bits f) - format_emin f))"
    by (rule subnormal_core_value)
  from subnormal core_value show ?thesis
    by (simp add: round_rational_core_at_def)
qed

corollary round_rational_core_value:
  fixes n d :: nat and e :: int
  assumes valid: "valid_format f"
  defines "e \<equiv> floor_log2_spec n d"
  shows "rounded_core_value f negative
      (round_rational_core f rm negative n d) =
    (if format_emin f \<le> e then
       rounded_grid_value rm negative n d
         (int (fraction_bits f) - e)
     else
       rounded_grid_value rm negative n d
         (int (fraction_bits f) - format_emin f))"
  unfolding round_rational_core_def e_def
  by (rule round_rational_core_at_value[OF valid])

text \<open>
  In every non-overflow case, decoding the generated fields yields precisely
  the magnitude recorded by the rounded core.  Thus the preceding grid theorem
  talks about the same value that the run-time bit record denotes.
\<close>

lemma decode_encode_rounded_core_finite:
  assumes valid: "valid_format f"
      and invariant: "core_encoding_invariant f c"
      and no_overflow:
        "core_is_subnormal c \<or> core_exponent c \<le> format_emax f"
  shows "decode_bits f (encode_rounded_core f rm negative c) =
    Dynamic_Finite negative (rounded_core_magnitude f c)"
  using decode_encode_rounded_core[OF valid invariant]
    no_overflow
  by (auto simp: rounded_core_magnitude_def rat_pow2_eq_pow2_rat
      split: if_splits)

end

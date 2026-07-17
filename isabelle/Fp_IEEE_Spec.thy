(*  SPDX-License-Identifier: MIT

    A corrected, relational specification of conversion to an IEEE binary
    floating-point format.  The AFP IEEE theory supplies the representation,
    valuation, and classification predicates.  In particular, this theory
    deliberately does not use IEEE.round: its RNA branch restricts the set of
    candidates before finding a nearest value, which turns RNA into directed
    rounding away from zero for every inexact input.
*)

theory Fp_IEEE_Spec
  imports IEEE_Floating_Point.IEEE_Single_NaN
begin

section \<open>Destination-format parameters\<close>

text \<open>
  AFP's @{typ "('e, 'f) floatSingleNaN"} counts only the stored fraction
  bits.  The following constants expose the corresponding parameters of the
  underlying @{typ "('e, 'f) float"} format.
\<close>

definition fp_largest :: "('e::len, 'f::len) floatSingleNaN itself \<Rightarrow> real"
  where "fp_largest _ = IEEE.largest TYPE(('e, 'f) float)"

definition fp_threshold :: "('e::len, 'f::len) floatSingleNaN itself \<Rightarrow> real"
  where "fp_threshold _ = IEEE.threshold TYPE(('e, 'f) float)"

text \<open>
  A NaN cannot be a rounding candidate, so its least-significant-bit parity
  is immaterial.  Making the predicate true on every NaN makes it well-defined
  on AFP's quotient that identifies all NaN encodings.
\<close>

lift_definition fp_even_lsb :: "('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  is "\<lambda>a. IEEE.is_nan a \<or> even (IEEE.fraction a)"
  unfolding is_nan_equivalent_def by auto

section \<open>Finite rounding choices\<close>

definition fp_nearest_finite ::
    "real \<Rightarrow> ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_nearest_finite x a \<longleftrightarrow>
      is_finite a \<and>
      (\<forall>b::('e, 'f) floatSingleNaN.
        is_finite b \<longrightarrow> \<bar>valof a - x\<bar> \<le> \<bar>valof b - x\<bar>)"

definition fp_preferred_nearest ::
    "(('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool) \<Rightarrow>
      real \<Rightarrow> ('e, 'f) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_preferred_nearest preferred x a \<longleftrightarrow>
      fp_nearest_finite x a \<and>
      ((\<exists>b::('e, 'f) floatSingleNaN.
        fp_nearest_finite x b \<and> preferred b) \<longrightarrow> preferred a)"

definition fp_least_finite_above ::
    "real \<Rightarrow> ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_least_finite_above x a \<longleftrightarrow>
      is_finite a \<and> x \<le> valof a \<and>
      (\<forall>b::('e, 'f) floatSingleNaN.
        is_finite b \<and> x \<le> valof b \<longrightarrow> valof a \<le> valof b)"

definition fp_greatest_finite_below ::
    "real \<Rightarrow> ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_greatest_finite_below x a \<longleftrightarrow>
      is_finite a \<and> valof a \<le> x \<and>
      (\<forall>b::('e, 'f) floatSingleNaN.
        is_finite b \<and> valof b \<le> x \<longrightarrow> valof b \<le> valof a)"

lemma fp_nearest_finiteD:
  fixes a b :: "('e::len, 'f::len) floatSingleNaN"
  assumes "fp_nearest_finite x a"
  shows "is_finite a"
    and "is_finite b \<Longrightarrow> \<bar>valof a - x\<bar> \<le> \<bar>valof b - x\<bar>"
  using assms unfolding fp_nearest_finite_def by auto

lemma fp_nearest_finite_exact:
  assumes "is_finite a"
  shows "fp_nearest_finite (valof a) a"
  using assms unfolding fp_nearest_finite_def by simp

lemma fp_preferred_nearestD:
  assumes "fp_preferred_nearest preferred x a"
  shows "fp_nearest_finite x a"
    and "(\<exists>b. fp_nearest_finite x b \<and> preferred b) \<Longrightarrow> preferred a"
  using assms unfolding fp_preferred_nearest_def by auto

lemma fp_preferred_nearestI:
  assumes "fp_nearest_finite x a" "preferred a"
  shows "fp_preferred_nearest preferred x a"
  using assms unfolding fp_preferred_nearest_def by blast

lemma fp_RNA_exact_choice:
  assumes "is_finite a"
  shows "fp_preferred_nearest
    (\<lambda>b. \<bar>valof b\<bar> \<ge> \<bar>valof a\<bar>) (valof a) a"
  using assms
  by (intro fp_preferred_nearestI fp_nearest_finite_exact) simp_all

lemma fp_least_finite_above_exact:
  assumes "is_finite a"
  shows "fp_least_finite_above (valof a) a"
  using assms unfolding fp_least_finite_above_def by auto

lemma fp_greatest_finite_below_exact:
  assumes "is_finite a"
  shows "fp_greatest_finite_below (valof a) a"
  using assms unfolding fp_greatest_finite_below_def by auto

section \<open>Correct rounding relation\<close>

text \<open>
  Nearest-ties-away first minimizes error over the full set of finite values.
  Only after that minimization does it prefer a tied result whose magnitude is
  at least the exact magnitude.  This ordering of the two conditions is the
  essential correction to AFP's current RNA definition.
\<close>

fun fp_round_rel ::
    "roundmode \<Rightarrow> real \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_round_rel RNE x a \<longleftrightarrow>
      (if x \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)
       then a = minus_infinity
       else if x \<ge> fp_threshold TYPE(('e, 'f) floatSingleNaN)
       then a = plus_infinity
       else fp_preferred_nearest fp_even_lsb x a)"
  | "fp_round_rel RNA x a \<longleftrightarrow>
      (if x \<le> - fp_threshold TYPE(('e, 'f) floatSingleNaN)
       then a = minus_infinity
       else if x \<ge> fp_threshold TYPE(('e, 'f) floatSingleNaN)
       then a = plus_infinity
       else fp_preferred_nearest (\<lambda>b. \<bar>valof b\<bar> \<ge> \<bar>x\<bar>) x a)"
  | "fp_round_rel RTP x a \<longleftrightarrow>
      (if x > fp_largest TYPE(('e, 'f) floatSingleNaN)
       then a = plus_infinity
       else fp_least_finite_above x a)"
  | "fp_round_rel RTN x a \<longleftrightarrow>
      (if x < - fp_largest TYPE(('e, 'f) floatSingleNaN)
       then a = minus_infinity
       else fp_greatest_finite_below x a)"
  | "fp_round_rel RTZ x a \<longleftrightarrow>
      (if 0 \<le> x
       then fp_greatest_finite_below x a
       else fp_least_finite_above x a)"

lemma fp_round_RNA_full_finite:
  fixes a b :: "('e::len, 'f::len) floatSingleNaN"
  assumes lower: "- fp_threshold TYPE(('e, 'f) floatSingleNaN) < x"
      and upper: "x < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
      and rounded: "fp_round_rel RNA x a"
  shows "is_finite a"
    and "is_finite b \<Longrightarrow> \<bar>valof a - x\<bar> \<le> \<bar>valof b - x\<bar>"
  using assms
  by (auto simp: fp_preferred_nearest_def fp_nearest_finite_def)

lemma fp_round_RNA_tie_away:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes lower: "- fp_threshold TYPE(('e, 'f) floatSingleNaN) < x"
      and upper: "x < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
      and rounded: "fp_round_rel RNA x a"
      and outward_tie:
        "\<exists>b::('e, 'f) floatSingleNaN.
          fp_nearest_finite x b \<and> \<bar>valof b\<bar> \<ge> \<bar>x\<bar>"
  shows "\<bar>valof a\<bar> \<ge> \<bar>x\<bar>"
  using assms by (auto simp: fp_preferred_nearest_def)

lemma fp_round_RNE_even_tie:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes lower: "- fp_threshold TYPE(('e, 'f) floatSingleNaN) < x"
      and upper: "x < fp_threshold TYPE(('e, 'f) floatSingleNaN)"
      and rounded: "fp_round_rel RNE x a"
      and even_tie: "\<exists>b::('e, 'f) floatSingleNaN.
        fp_nearest_finite x b \<and> fp_even_lsb b"
  shows "fp_even_lsb a"
  using assms by (auto simp: fp_preferred_nearest_def)

lemma fp_round_rel_result_cases:
  assumes "fp_round_rel mode x a"
  shows "is_finite a \<or> a = plus_infinity \<or> a = minus_infinity"
  using assms
  by (cases mode)
    (auto simp: fp_preferred_nearest_def fp_nearest_finite_def
      fp_least_finite_above_def fp_greatest_finite_below_def split: if_splits)

lemma fp_round_RTP_direction:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes "fp_round_rel RTP x a" "x \<le> fp_largest TYPE(('e, 'f) floatSingleNaN)"
  shows "is_finite a" "x \<le> valof a"
  using assms by (auto simp: fp_least_finite_above_def)

lemma fp_round_RTN_direction:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes "fp_round_rel RTN x a" "- fp_largest TYPE(('e, 'f) floatSingleNaN) \<le> x"
  shows "is_finite a" "valof a \<le> x"
  using assms by (auto simp: fp_greatest_finite_below_def)

lemma fp_round_RTZ_direction:
  assumes "fp_round_rel RTZ x a"
  shows "is_finite a"
    and "0 \<le> x \<Longrightarrow> valof a \<le> x"
    and "x < 0 \<Longrightarrow> x \<le> valof a"
proof -
  from assms have rel:
    "if 0 \<le> x then fp_greatest_finite_below x a
     else fp_least_finite_above x a"
    by simp
  show "is_finite a"
    using rel by (auto simp: fp_greatest_finite_below_def
      fp_least_finite_above_def split: if_splits)
  show "0 \<le> x \<Longrightarrow> valof a \<le> x"
    using rel by (simp add: fp_greatest_finite_below_def)
  show "x < 0 \<Longrightarrow> x \<le> valof a"
    using rel by (simp add: fp_least_finite_above_def)
qed

section \<open>Signed zero and floating-point conversion\<close>

definition fp_zero_with_sign ::
    "bool \<Rightarrow> ('e::len, 'f::len) floatSingleNaN"
  where "fp_zero_with_sign negative = (if negative then minus_zero else 0)"

definition fp_signed_round_rel ::
    "roundmode \<Rightarrow> bool \<Rightarrow> real \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_signed_round_rel mode negative x a \<longleftrightarrow>
      fp_round_rel mode x a \<and>
      (is_zero a \<longrightarrow> a = fp_zero_with_sign negative)"

lemma fp_signed_round_rel_round:
  "fp_signed_round_rel mode negative x a \<Longrightarrow> fp_round_rel mode x a"
  unfolding fp_signed_round_rel_def by simp

lemma fp_signed_round_rel_zero:
  assumes "fp_signed_round_rel mode negative x a" "is_zero a"
  shows "a = fp_zero_with_sign negative"
  using assms unfolding fp_signed_round_rel_def by blast

lemma fp_signed_round_rel_nonzero:
  assumes "\<not> is_zero a"
  shows "fp_signed_round_rel mode negative x a \<longleftrightarrow> fp_round_rel mode x a"
  using assms unfolding fp_signed_round_rel_def by simp

text \<open>
  Special values are converted without passing through @{const valof}.  Every
  finite input, including a signed zero, is rounded from its exact real value;
  @{const fp_signed_round_rel} restores the source sign if that result is zero.
\<close>

definition fp_convert_rel ::
    "roundmode \<Rightarrow> ('a::len, 'b::len) floatSingleNaN \<Rightarrow>
      ('e::len, 'f::len) floatSingleNaN \<Rightarrow> bool"
  where
    "fp_convert_rel mode source dest \<longleftrightarrow>
      (if is_nan source then dest = NaN
       else if source = plus_infinity then dest = plus_infinity
       else if source = minus_infinity then dest = minus_infinity
       else is_finite source \<and>
         fp_signed_round_rel mode (is_negative source) (valof source) dest)"

lemma fp_convert_nan:
  assumes "is_nan source"
  shows "fp_convert_rel mode source dest \<longleftrightarrow> dest = NaN"
  using assms unfolding fp_convert_rel_def by simp

lemma fp_convert_plus_infinity:
  assumes "\<not> is_nan source" "source = plus_infinity"
  shows "fp_convert_rel mode source dest \<longleftrightarrow> dest = plus_infinity"
  using assms unfolding fp_convert_rel_def by simp

lemma fp_convert_minus_infinity:
  assumes "\<not> is_nan source" "source \<noteq> plus_infinity"
      and "source = minus_infinity"
  shows "fp_convert_rel mode source dest \<longleftrightarrow> dest = minus_infinity"
  using assms unfolding fp_convert_rel_def by simp

lemma fp_convert_finite:
  assumes finite: "is_finite source"
      and not_pos_inf: "source \<noteq> plus_infinity"
      and not_neg_inf: "source \<noteq> minus_infinity"
      and not_nan: "\<not> is_nan source"
  shows "fp_convert_rel mode source dest \<longleftrightarrow>
    fp_signed_round_rel mode (is_negative source) (valof source) dest"
  using assms unfolding fp_convert_rel_def by simp

lemma fp_convert_zero_sign:
  assumes converted: "fp_convert_rel mode source dest"
      and finite: "is_finite source"
      and not_pos_inf: "source \<noteq> plus_infinity"
      and not_neg_inf: "source \<noteq> minus_infinity"
      and not_nan: "\<not> is_nan source"
      and zero: "is_zero dest"
  shows "dest = fp_zero_with_sign (is_negative source)"
  using converted zero
  unfolding fp_convert_rel_def fp_signed_round_rel_def
  using finite not_pos_inf not_neg_inf not_nan by auto

end

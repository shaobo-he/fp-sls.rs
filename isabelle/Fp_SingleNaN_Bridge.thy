(*  SPDX-License-Identifier: MIT

    Explicit bridge from AFP's bit-level float type to the quotient in which
    all NaN encodings are identified.
*)

theory Fp_SingleNaN_Bridge
  imports
    Fp_IEEE_Bridge
    Fp_IEEE_Spec
begin

section \<open>Embedding raw AFP floats\<close>

text \<open>
  This is the quotient abstraction map, exposed under a stable project-local
  name.  Keeping it explicit lets later proofs quantify over raw bit patterns
  while stating their semantic conclusions over @{typ "('e, 'f) floatSingleNaN"}.
\<close>

definition single_nan_of_float ::
    "('e::len, 'f::len) float \<Rightarrow> ('e, 'f) floatSingleNaN"
  where "single_nan_of_float x = abs_floatSingleNaN x"

lemma single_nan_of_float_is_finite [simp]:
  "is_finite (single_nan_of_float x) \<longleftrightarrow> IEEE.is_finite x"
  unfolding single_nan_of_float_def by transfer simp

lemma single_nan_of_float_valof:
  assumes "IEEE.is_finite x"
  shows "valof (single_nan_of_float x) = IEEE.valof x"
proof -
  have not_nan: "\<not> IEEE.is_nan x"
    using assms by (rule finite_nan)
  have not_infinity: "\<not> IEEE.is_infinity x"
    using assms by (rule finite_infinity)
  show ?thesis
    using not_nan not_infinity
    by (simp add: single_nan_of_float_def valof.abs_eq)
qed

lemma single_nan_of_float_even_lsb [simp]:
  assumes "IEEE.is_finite x"
  shows "fp_even_lsb (single_nan_of_float x) \<longleftrightarrow>
    even (IEEE.fraction x)"
  using assms unfolding single_nan_of_float_def by transfer auto

section \<open>Finite representatives\<close>

lemma finite_single_nan_representation:
  fixes a :: "('e::len, 'f::len) floatSingleNaN"
  assumes "is_finite a"
  obtains x :: "('e, 'f) float"
    where "a = single_nan_of_float x" "IEEE.is_finite x"
proof
  have rep: "single_nan_of_float (rep_floatSingleNaN a) = a"
    unfolding single_nan_of_float_def
    using Quotient_abs_rep[OF Quotient_floatSingleNaN, of a] .
  show "a = single_nan_of_float (rep_floatSingleNaN a)"
    using rep by simp
  have embedded_finite:
    "is_finite (single_nan_of_float (rep_floatSingleNaN a))"
    using assms rep by simp
  show "IEEE.is_finite (rep_floatSingleNaN a)"
    using embedded_finite
      single_nan_of_float_is_finite[of "rep_floatSingleNaN a"]
    by blast
qed

lemma finite_single_nan_all_raw_iff:
  "(\<forall>a::('e::len, 'f::len) floatSingleNaN.
      is_finite a \<longrightarrow> P a) \<longleftrightarrow>
    (\<forall>x::('e, 'f) float.
      IEEE.is_finite x \<longrightarrow> P (single_nan_of_float x))"
proof
  assume all: "\<forall>a::('e, 'f) floatSingleNaN. is_finite a \<longrightarrow> P a"
  then show "\<forall>x::('e, 'f) float.
      IEEE.is_finite x \<longrightarrow> P (single_nan_of_float x)"
    by simp
next
  assume raw: "\<forall>x::('e, 'f) float.
      IEEE.is_finite x \<longrightarrow> P (single_nan_of_float x)"
  show "\<forall>a::('e, 'f) floatSingleNaN. is_finite a \<longrightarrow> P a"
  proof (intro allI impI)
    fix a :: "('e, 'f) floatSingleNaN"
    assume "is_finite a"
    then obtain x :: "('e, 'f) float"
      where a: "a = single_nan_of_float x" and finite: "IEEE.is_finite x"
      by (rule finite_single_nan_representation)
    show "P a"
      using raw finite by (simp add: a)
  qed
qed

lemma finite_single_nan_competitor:
  fixes b :: "('e::len, 'f::len) floatSingleNaN"
  assumes finite: "is_finite b"
      and raw_bound:
        "\<And>y::('e, 'f) float.
          IEEE.is_finite y \<Longrightarrow> Q (single_nan_of_float y)"
  shows "Q b"
proof -
  obtain y :: "('e, 'f) float"
    where b: "b = single_nan_of_float y" and y_finite: "IEEE.is_finite y"
    using finite by (rule finite_single_nan_representation)
  show ?thesis
    using raw_bound[OF y_finite] by (simp add: b)
qed

lemma finite_single_nan_value_competitor:
  fixes b :: "('e::len, 'f::len) floatSingleNaN"
  assumes finite: "is_finite b"
      and raw_bound:
        "\<And>y::('e, 'f) float.
          IEEE.is_finite y \<Longrightarrow> Q (IEEE.valof y)"
  shows "Q (valof b)"
proof -
  obtain y :: "('e, 'f) float"
    where b: "b = single_nan_of_float y" and y_finite: "IEEE.is_finite y"
    using finite by (rule finite_single_nan_representation)
  have "Q (IEEE.valof y)"
    by (rule raw_bound[OF y_finite])
  then show ?thesis
    using b y_finite single_nan_of_float_valof[of y] by simp
qed

lemma finite_single_nan_value_parity_competitor:
  fixes b :: "('e::len, 'f::len) floatSingleNaN"
  assumes finite: "is_finite b"
      and raw_bound:
        "\<And>y::('e, 'f) float.
          IEEE.is_finite y \<Longrightarrow>
          Q (IEEE.valof y) (even (IEEE.fraction y))"
  shows "Q (valof b) (fp_even_lsb b)"
proof -
  obtain y :: "('e, 'f) float"
    where b: "b = single_nan_of_float y" and y_finite: "IEEE.is_finite y"
    using finite by (rule finite_single_nan_representation)
  have "Q (IEEE.valof y) (even (IEEE.fraction y))"
    by (rule raw_bound[OF y_finite])
  then show ?thesis
    using b y_finite single_nan_of_float_valof[of y]
      single_nan_of_float_even_lsb[of y]
    by simp
qed

end

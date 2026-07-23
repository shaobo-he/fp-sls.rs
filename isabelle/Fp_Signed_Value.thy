(* SPDX-License-Identifier: MIT *)

section \<open>Signed values and opposite-sign competitors\<close>

theory Fp_Signed_Value
  imports Fp_Round_Value Fp_SingleNaN_Bridge
begin

text \<open>
  The representation bridge initially identifies the dynamic magnitude with
  the absolute value of AFP's valuation.  Recovering the sign gives the exact
  value equation needed by the rounding relation.
\<close>

lemma abs_real_of_rat_diff:
  "\<bar>(of_rat a :: real) - of_rat b\<bar> = of_rat \<bar>a - b\<bar>"
  by (simp only: of_rat_diff[symmetric] abs_of_rat)

lemma runtime_value_eq_signed_magnitude:
  fixes x :: "('e::len, 'f::len) float"
  shows
    "(of_rat (signed_rat (IEEE.sign x = 1)
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (runtime_bits x))) :: real) = IEEE.valof x"
proof (cases x rule: sign_cases)
  case pos
  have nonnegative: "0 \<le> IEEE.valof x"
    by (rule valof_nonneg[OF pos])
  show ?thesis
    using runtime_magnitude_eq_abs_valof[of x] pos nonnegative
    by (simp add: signed_rat_def abs_of_nonneg)
next
  case neg
  have nonpositive: "IEEE.valof x \<le> 0"
    by (rule valof_nonpos[OF neg])
  show ?thesis
    using runtime_magnitude_eq_abs_valof[of x] neg nonpositive
    by (simp add: signed_rat_def abs_of_nonpos of_rat_minus)
qed

lemma single_nan_value_eq_signed_magnitude:
  fixes x :: "('e::len, 'f::len) float"
  assumes finite: "IEEE.is_finite x"
  shows
    "(of_rat (signed_rat (IEEE.sign x = 1)
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (runtime_bits x))) :: real) =
      valof (single_nan_of_float x)"
  using runtime_value_eq_signed_magnitude[of x]
    single_nan_of_float_valof[OF finite]
  by simp

text \<open>
  For a fixed non-negative input magnitude, changing a finite competitor to
  the input's sign cannot increase its distance from the input.  This closes
  the gap between grid theorems stated for magnitudes and IEEE nearestness,
  which quantifies over values of either sign.
\<close>

lemma same_sign_competitor_no_farther:
  assumes x_nonnegative: "0 \<le> x"
      and y_nonnegative: "0 \<le> y"
  shows
    "\<bar>signed_rat negative y - signed_rat negative x\<bar> \<le>
     \<bar>signed_rat competitor_negative y - signed_rat negative x\<bar>"
proof -
  have distance: "\<bar>y - x\<bar> \<le> y + x"
  proof (rule abs_leI)
    show "y - x \<le> y + x"
      using x_nonnegative by linarith
    show "-(y - x) \<le> y + x"
      using y_nonnegative by linarith
  qed
  show ?thesis
    using x_nonnegative y_nonnegative distance
    by (cases negative; cases competitor_negative)
      (simp_all add: signed_rat_def abs_of_nonneg abs_of_nonpos
        abs_minus_commute add.commute)
qed

lemma same_sign_runtime_competitor_no_farther:
  fixes y :: "('e::len, 'f::len) float"
  assumes input_nonnegative: "0 \<le> x"
  shows
    "\<bar>(of_rat (signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float))
            (runtime_bits y))) :: real) -
        of_rat (signed_rat negative x)\<bar> \<le>
     \<bar>IEEE.valof y - of_rat (signed_rat negative x)\<bar>"
proof -
  have magnitude_nonnegative:
    "0 \<le> finite_magnitude (runtime_format TYPE(('e, 'f) float))
      (runtime_bits y)"
    by simp
  have rational:
    "\<bar>signed_rat negative
          (finite_magnitude (runtime_format TYPE(('e, 'f) float))
            (runtime_bits y)) - signed_rat negative x\<bar> \<le>
     \<bar>signed_rat (IEEE.sign y = 1)
          (finite_magnitude (runtime_format TYPE(('e, 'f) float))
            (runtime_bits y)) - signed_rat negative x\<bar>"
    by (rule same_sign_competitor_no_farther[
          OF input_nonnegative magnitude_nonnegative])
  have casted:
    "(of_rat
        \<bar>signed_rat negative
            (finite_magnitude (runtime_format TYPE(('e, 'f) float))
              (runtime_bits y)) - signed_rat negative x\<bar> :: real) \<le>
     of_rat
        \<bar>signed_rat (IEEE.sign y = 1)
            (finite_magnitude (runtime_format TYPE(('e, 'f) float))
              (runtime_bits y)) - signed_rat negative x\<bar>"
    using rational by (simp only: of_rat_less_eq)
  have actual:
    "IEEE.valof y =
      (of_rat (signed_rat (IEEE.sign y = 1)
        (finite_magnitude (runtime_format TYPE(('e, 'f) float))
          (runtime_bits y))) :: real)"
    using runtime_value_eq_signed_magnitude[of y] by simp
  show ?thesis
    unfolding actual
    using casted
    by (simp only: abs_real_of_rat_diff)
qed

end

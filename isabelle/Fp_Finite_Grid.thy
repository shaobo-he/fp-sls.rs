section \<open>Finite runtime values lie on the binary grid\<close>

theory Fp_Finite_Grid
  imports Fp_Format Fp_Rational_Scale
begin

text \<open>
  The dynamic format model spells powers of two out using a rational-valued
  definition, while the scaling theory uses integer powers.  Identifying the
  two views makes the grid arithmetic below routine.
\<close>

lemma pow2_rat_eq_rat_pow2:
  "pow2_rat k = rat_pow2 k"
proof (cases "0 \<le> k")
  case True
  then show ?thesis
    by (simp add: pow2_rat_def rat_pow2_def power_int_def)
next
  case False
  then show ?thesis
    by (simp add: pow2_rat_def rat_pow2_def power_int_def
        flip: power_inverse)
qed

lemma pow2_rat_add:
  "pow2_rat (a + b) = pow2_rat a * pow2_rat b"
  by (simp add: pow2_rat_eq_rat_pow2 rat_pow2_add)

lemma pow2_rat_nat [simp]:
  "pow2_rat (int n) = (of_nat (2 ^ n) :: rat)"
  by (simp add: pow2_rat_eq_rat_pow2)

lemma pow2_rat_mono:
  assumes "a \<le> b"
  shows "pow2_rat a \<le> pow2_rat b"
  using assms
  by (simp add: pow2_rat_eq_rat_pow2 rat_pow2_increasing)

definition minimum_subnormal_step :: "binary_format \<Rightarrow> rat" where
  "minimum_subnormal_step f =
     pow2_rat (format_emin f - int (fraction_bits f))"

lemma minimum_subnormal_step_pos [simp]:
  "0 < minimum_subnormal_step f"
  by (simp add: minimum_subnormal_step_def)

lemma finite_magnitude_subnormal_grid:
  assumes zero_exponent: "exponent_field b = 0"
  shows "finite_magnitude f b =
    of_nat (fraction_field b) * minimum_subnormal_step f"
  using zero_exponent
  by (simp add: finite_magnitude_def minimum_subnormal_step_def)

lemma normal_scale_as_minimum_step:
  assumes positive_exponent: "0 < exponent_field b"
  shows
    "pow2_rat (int (exponent_field b) - int (format_bias f) -
        int (fraction_bits f)) =
     of_nat (2 ^ (exponent_field b - 1)) * minimum_subnormal_step f"
proof -
  have exponent_decomposition:
    "int (exponent_field b) - int (format_bias f) -
        int (fraction_bits f) =
     (format_emin f - int (fraction_bits f)) +
        int (exponent_field b - 1)"
    using positive_exponent
    by (simp add: format_emin_def; linarith)
  show ?thesis
    by (simp add: exponent_decomposition pow2_rat_add
        minimum_subnormal_step_def mult.commute)
qed

lemma finite_magnitude_normal_grid:
  assumes positive_exponent: "0 < exponent_field b"
  shows "finite_magnitude f b =
    of_nat ((2 ^ fraction_bits f + fraction_field b) *
      2 ^ (exponent_field b - 1)) * minimum_subnormal_step f"
  using positive_exponent normal_scale_as_minimum_step[OF positive_exponent]
  by (simp add: finite_magnitude_def of_nat_mult algebra_simps)

definition stored_unbiased_exponent ::
    "binary_format \<Rightarrow> fp_bits \<Rightarrow> int" where
  "stored_unbiased_exponent f b =
     int (exponent_field b) - int (format_bias f)"

lemma finite_magnitude_normal_binade_grid:
  assumes positive_exponent: "0 < exponent_field b"
  shows "finite_magnitude f b =
    of_nat (2 ^ fraction_bits f + fraction_field b) *
      pow2_rat (stored_unbiased_exponent f b - int (fraction_bits f))"
  using positive_exponent
  by (simp add: finite_magnitude_def stored_unbiased_exponent_def)

lemma pow2_rat_split_fraction_width:
  "pow2_rat e = of_nat (2 ^ fraction_bits f) *
    pow2_rat (e - int (fraction_bits f))"
proof -
  have decomposition:
    "e = (e - int (fraction_bits f)) + int (fraction_bits f)"
    by simp
  have "pow2_rat e = pow2_rat
      ((e - int (fraction_bits f)) + int (fraction_bits f))"
    by (rule arg_cong[OF decomposition])
  also have "... = pow2_rat (e - int (fraction_bits f)) *
      pow2_rat (int (fraction_bits f))"
    by (rule pow2_rat_add)
  also have "... = of_nat (2 ^ fraction_bits f) *
      pow2_rat (e - int (fraction_bits f))"
  proof -
    have power:
      "pow2_rat (int (fraction_bits f)) =
        (of_nat (2 ^ fraction_bits f) :: rat)"
      by (rule pow2_rat_nat)
    show ?thesis
      by (subst power) (simp add: mult.commute)
  qed
  finally show ?thesis .
qed

lemma pow2_rat_split_precision_width:
  "pow2_rat (e + 1) = of_nat (2 ^ Suc (fraction_bits f)) *
    pow2_rat (e - int (fraction_bits f))"
proof -
  have decomposition: "e + 1 =
      (e - int (fraction_bits f)) + int (Suc (fraction_bits f))"
    by simp
  have "pow2_rat (e + 1) = pow2_rat
      ((e - int (fraction_bits f)) + int (Suc (fraction_bits f)))"
    by (rule arg_cong[OF decomposition])
  also have "... = pow2_rat (e - int (fraction_bits f)) *
      pow2_rat (int (Suc (fraction_bits f)))"
    by (rule pow2_rat_add)
  also have "... = of_nat (2 ^ Suc (fraction_bits f)) *
      pow2_rat (e - int (fraction_bits f))"
  proof -
    have power:
      "pow2_rat (int (Suc (fraction_bits f))) =
        (of_nat (2 ^ Suc (fraction_bits f)) :: rat)"
      by (rule pow2_rat_nat)
    show ?thesis
      by (subst power) (simp add: mult.commute)
  qed
  finally show ?thesis .
qed

lemma finite_magnitude_normal_binade_lower:
  assumes positive_exponent: "0 < exponent_field b"
  shows "pow2_rat (stored_unbiased_exponent f b) \<le>
    finite_magnitude f b"
proof -
  have coefficient:
    "(of_nat (2 ^ fraction_bits f) :: rat) \<le>
      of_nat (2 ^ fraction_bits f + fraction_field b)"
    by simp
  have step_nonnegative:
    "0 \<le> pow2_rat
      (stored_unbiased_exponent f b - int (fraction_bits f))"
    by simp
  note scaled = mult_right_mono[OF coefficient step_nonnegative]
  show ?thesis
    using scaled finite_magnitude_normal_binade_grid[OF positive_exponent]
      pow2_rat_split_fraction_width[
        of "stored_unbiased_exponent f b" f]
    by simp
qed

lemma finite_magnitude_normal_binade_upper:
  assumes positive_exponent: "0 < exponent_field b"
      and well_formed: "bits_well_formed f b"
  shows "finite_magnitude f b <
    pow2_rat (stored_unbiased_exponent f b + 1)"
proof -
  have fraction_bound:
    "fraction_field b < 2 ^ fraction_bits f"
    using well_formed by (rule well_formed_fraction_field)
  have coefficient:
    "(of_nat (2 ^ fraction_bits f + fraction_field b) :: rat) <
      of_nat (2 ^ Suc (fraction_bits f))"
    using fraction_bound
    by (simp add: power_Suc; linarith)
  have step_positive:
    "0 < pow2_rat
      (stored_unbiased_exponent f b - int (fraction_bits f))"
    by simp
  note scaled = mult_strict_right_mono[OF coefficient step_positive]
  show ?thesis
    using scaled finite_magnitude_normal_binade_grid[OF positive_exponent]
      pow2_rat_split_precision_width[
        of "stored_unbiased_exponent f b" f]
    by simp
qed

lemma finite_magnitude_subnormal_upper:
  assumes zero_exponent: "exponent_field b = 0"
      and well_formed: "bits_well_formed f b"
  shows "finite_magnitude f b < pow2_rat (format_emin f)"
proof -
  have fraction_bound:
    "fraction_field b < 2 ^ fraction_bits f"
    using well_formed by (rule well_formed_fraction_field)
  have coefficient:
    "(of_nat (fraction_field b) :: rat) <
      of_nat (2 ^ fraction_bits f)"
    using fraction_bound by simp
  have step_positive: "0 < minimum_subnormal_step f" by simp
  note scaled = mult_strict_right_mono[OF coefficient step_positive]
  show ?thesis
    using scaled finite_magnitude_subnormal_grid[OF zero_exponent]
      pow2_rat_split_fraction_width[of "format_emin f" f]
    by (simp add: minimum_subnormal_step_def)
qed

lemma finite_magnitude_above_power_is_normal:
  assumes well_formed: "bits_well_formed f b"
      and exponent_lower: "format_emin f \<le> e"
      and magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
  shows "0 < exponent_field b"
proof (rule ccontr)
  assume "\<not> 0 < exponent_field b"
  then have zero_exponent: "exponent_field b = 0" by simp
  have magnitude_upper:
    "finite_magnitude f b < pow2_rat (format_emin f)"
    by (rule finite_magnitude_subnormal_upper[OF zero_exponent well_formed])
  have power_order: "pow2_rat (format_emin f) \<le> pow2_rat e"
    by (rule pow2_rat_mono[OF exponent_lower])
  show False
    using magnitude_lower magnitude_upper power_order by linarith
qed

lemma finite_magnitude_above_power_exponent:
  assumes well_formed: "bits_well_formed f b"
      and magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
      and positive_exponent: "0 < exponent_field b"
  shows "e \<le> stored_unbiased_exponent f b"
proof (rule ccontr)
  assume "\<not> e \<le> stored_unbiased_exponent f b"
  then have next_le:
    "stored_unbiased_exponent f b + 1 \<le> e"
    by simp
  have magnitude_upper:
    "finite_magnitude f b <
      pow2_rat (stored_unbiased_exponent f b + 1)"
    by (rule finite_magnitude_normal_binade_upper[
          OF positive_exponent well_formed])
  have power_order:
    "pow2_rat (stored_unbiased_exponent f b + 1) \<le> pow2_rat e"
    by (rule pow2_rat_mono[OF next_le])
  show False
    using magnitude_lower magnitude_upper power_order by linarith
qed

lemma finite_magnitude_normal_on_lower_binade_grid:
  assumes positive_exponent: "0 < exponent_field b"
      and exponent_order: "e \<le> stored_unbiased_exponent f b"
  obtains m :: nat where
    "finite_magnitude f b =
      of_nat m * pow2_rat (e - int (fraction_bits f))"
proof -
  let ?g = "stored_unbiased_exponent f b"
  let ?delta = "nat (?g - e)"
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
    also have "... = pow2_rat (e - int (fraction_bits f)) *
        pow2_rat (int ?delta)"
      by (rule pow2_rat_add)
    also have "... = of_nat (2 ^ ?delta) *
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
  show thesis
    by (rule that[of
          "(2 ^ fraction_bits f + fraction_field b) * 2 ^ ?delta"])
      (simp add: finite_magnitude_normal_binade_grid[OF positive_exponent]
        scale_decomposition of_nat_mult algebra_simps)
qed

theorem finite_magnitude_above_power_on_grid:
  assumes valid: "valid_format f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and exponent_lower: "format_emin f \<le> e"
      and magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
  obtains m :: nat where
    "finite_magnitude f b =
      of_nat m * pow2_rat (e - int (fraction_bits f))"
proof -
  have positive_exponent: "0 < exponent_field b"
    by (rule finite_magnitude_above_power_is_normal[
          OF well_formed exponent_lower magnitude_lower])
  have exponent_order: "e \<le> stored_unbiased_exponent f b"
    by (rule finite_magnitude_above_power_exponent[
          OF well_formed magnitude_lower positive_exponent])
  show thesis
    by (rule finite_magnitude_normal_on_lower_binade_grid[
          OF positive_exponent exponent_order that])
qed

theorem finite_magnitude_on_minimum_subnormal_grid:
  obtains m :: nat where
    "finite_magnitude f b = of_nat m * minimum_subnormal_step f"
proof (cases "exponent_field b = 0")
  case True
  show thesis
  proof (rule that[of "fraction_field b"])
    show "finite_magnitude f b =
        of_nat (fraction_field b) * minimum_subnormal_step f"
      by (rule finite_magnitude_subnormal_grid[OF True])
  qed
next
  case False
  then have positive_exponent: "0 < exponent_field b" by simp
  show thesis
    by (rule that[of
          "(2 ^ fraction_bits f + fraction_field b) *
            2 ^ (exponent_field b - 1)"])
      (rule finite_magnitude_normal_grid[OF positive_exponent])
qed

corollary well_formed_finite_magnitude_on_grid:
  assumes "valid_format f"
      and "bits_well_formed f b"
      and "exponent_field b < exponent_all_ones f"
  obtains m :: nat where
    "finite_magnitude f b =
      of_nat m * pow2_rat (format_emin f - int (fraction_bits f))"
  using finite_magnitude_on_minimum_subnormal_grid[of f b]
  unfolding minimum_subnormal_step_def
  by blast

end

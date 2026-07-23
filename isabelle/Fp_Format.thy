section \<open>Runtime binary floating-point formats\<close>

theory Fp_Format
  imports "HOL-Library.Float"
begin

text \<open>
  AFP's IEEE theory represents the exponent and fraction widths at the type
  level.  The Rust implementation receives both widths at run time and counts
  the hidden bit as part of its significand width.  This small model is the
  run-time side of the eventual refinement theorem.
\<close>

record binary_format =
  exponent_bits :: nat
  precision_bits :: nat

definition valid_format :: "binary_format \<Rightarrow> bool" where
  "valid_format f \<longleftrightarrow> 2 \<le> exponent_bits f \<and> 2 \<le> precision_bits f"

definition fraction_bits :: "binary_format \<Rightarrow> nat" where
  "fraction_bits f = precision_bits f - 1"

definition exponent_all_ones :: "binary_format \<Rightarrow> nat" where
  "exponent_all_ones f = 2 ^ exponent_bits f - 1"

definition format_bias :: "binary_format \<Rightarrow> nat" where
  "format_bias f = 2 ^ (exponent_bits f - 1) - 1"

definition format_emin :: "binary_format \<Rightarrow> int" where
  "format_emin f = 1 - int (format_bias f)"

definition format_emax :: "binary_format \<Rightarrow> int" where
  "format_emax f = int (format_bias f)"

lemma valid_format_exponent_bits:
  "valid_format f \<Longrightarrow> 2 \<le> exponent_bits f"
  by (simp add: valid_format_def)

lemma valid_format_precision_bits:
  "valid_format f \<Longrightarrow> 2 \<le> precision_bits f"
  by (simp add: valid_format_def)

lemma valid_format_fraction_bits_pos:
  "valid_format f \<Longrightarrow> 0 < fraction_bits f"
  by (simp add: valid_format_def fraction_bits_def)

lemma valid_format_precision_as_fraction:
  assumes "valid_format f"
  shows "precision_bits f = Suc (fraction_bits f)"
  using assms by (simp add: valid_format_def fraction_bits_def)

lemma valid_format_precision_power:
  assumes "valid_format f"
  shows "(2::nat) ^ precision_bits f =
    2 ^ fraction_bits f + 2 ^ fraction_bits f"
  using valid_format_precision_as_fraction[OF assms]
  by (simp add: power_Suc)

lemma format_emin_plus_bias [simp]:
  "format_emin f + int (format_bias f) = 1"
  by (simp add: format_emin_def)

lemma twice_bias_lt_exponent_all_ones:
  assumes "valid_format f"
  shows "2 * format_bias f < exponent_all_ones f"
proof -
  have eb_pos: "0 < exponent_bits f"
    using assms by (simp add: valid_format_def)
  then obtain k where eb: "exponent_bits f = Suc k"
    by (cases "exponent_bits f") auto
  have power_pos: "0 < (2::nat) ^ k" by simp
  then obtain j where power: "(2::nat) ^ k = Suc j"
    by (cases "(2::nat) ^ k") auto
  show ?thesis
    by (simp add: format_bias_def exponent_all_ones_def eb power_Suc power
        algebra_simps)
qed

lemma normal_biased_exponent_bounds:
  assumes valid: "valid_format f"
      and lower: "format_emin f \<le> e"
      and upper: "e \<le> format_emax f"
  shows "0 < e + int (format_bias f)"
    and "nat (e + int (format_bias f)) < exponent_all_ones f"
proof -
  show "0 < e + int (format_bias f)"
    using lower by (simp add: format_emin_def; linarith)
  have sum_le: "nat (e + int (format_bias f)) \<le> 2 * format_bias f"
    using upper by (simp add: nat_le_iff format_emax_def; linarith)
  also have "2 * format_bias f < exponent_all_ones f"
    by (rule twice_bias_lt_exponent_all_ones[OF valid])
  finally show "nat (e + int (format_bias f)) < exponent_all_ones f" .
qed

text \<open>An untyped bit-level payload, matching the three fields stored by Rust.\<close>

record fp_bits =
  negative_bit :: bool
  exponent_field :: nat
  fraction_field :: nat

definition bits_well_formed :: "binary_format \<Rightarrow> fp_bits \<Rightarrow> bool" where
  "bits_well_formed f x \<longleftrightarrow>
     exponent_field x < 2 ^ exponent_bits f \<and>
     fraction_field x < 2 ^ fraction_bits f"

definition bits_is_nan :: "binary_format \<Rightarrow> fp_bits \<Rightarrow> bool" where
  "bits_is_nan f x \<longleftrightarrow>
     exponent_field x = exponent_all_ones f \<and> fraction_field x \<noteq> 0"

definition bits_is_infinity :: "binary_format \<Rightarrow> fp_bits \<Rightarrow> bool" where
  "bits_is_infinity f x \<longleftrightarrow>
     exponent_field x = exponent_all_ones f \<and> fraction_field x = 0"

definition bits_is_zero :: "fp_bits \<Rightarrow> bool" where
  "bits_is_zero x \<longleftrightarrow> exponent_field x = 0 \<and> fraction_field x = 0"

definition pow2_rat :: "int \<Rightarrow> rat" where
  "pow2_rat k =
     (if 0 \<le> k then of_nat (2 ^ nat k)
      else inverse (of_nat (2 ^ nat (- k))))"

lemma pow2_rat_pos [simp]: "0 < pow2_rat k"
  unfolding pow2_rat_def
  by (auto simp: zero_less_power)

lemma pow2_rat_nonzero [simp]: "pow2_rat k \<noteq> 0"
  using pow2_rat_pos[of k] by linarith

lemma pow2_rat_nonnegative [simp]: "0 \<le> pow2_rat k"
  using pow2_rat_pos[of k] by linarith

lemma pow2_rat_zero [simp]: "pow2_rat 0 = 1"
  by (simp add: pow2_rat_def)

definition finite_magnitude :: "binary_format \<Rightarrow> fp_bits \<Rightarrow> rat" where
  "finite_magnitude f x =
     (if exponent_field x = 0 then
        of_nat (fraction_field x) *
          pow2_rat (format_emin f - int (fraction_bits f))
      else
        of_nat (2 ^ fraction_bits f + fraction_field x) *
          pow2_rat (int (exponent_field x) - int (format_bias f) -
            int (fraction_bits f)))"

lemma finite_magnitude_nonnegative [simp]: "0 \<le> finite_magnitude f x"
  unfolding finite_magnitude_def
  by (auto intro!: mult_nonneg_nonneg)

lemma finite_magnitude_zero_iff [simp]:
  "finite_magnitude f x = 0 \<longleftrightarrow>
     exponent_field x = 0 \<and> fraction_field x = 0"
proof (cases "exponent_field x = 0")
  case True
  then show ?thesis by (simp add: finite_magnitude_def)
next
  case False
  have power_pos: "0 < (2::rat) ^ fraction_bits f" by simp
  have fraction_nonnegative: "0 \<le> (of_nat (fraction_field x)::rat)" by simp
  have "(of_nat (2 ^ fraction_bits f + fraction_field x) :: rat) \<noteq> 0"
    using power_pos fraction_nonnegative by (simp; linarith)
  with False show ?thesis by (simp add: finite_magnitude_def)
qed

datatype dynamic_float_value =
    Dynamic_NaN
  | Dynamic_Infinity bool
  | Dynamic_Finite bool rat

definition decode_bits :: "binary_format \<Rightarrow> fp_bits \<Rightarrow> dynamic_float_value" where
  "decode_bits f x =
     (if bits_is_nan f x then Dynamic_NaN
      else if bits_is_infinity f x then Dynamic_Infinity (negative_bit x)
      else Dynamic_Finite (negative_bit x) (finite_magnitude f x))"

definition positive_zero_bits :: fp_bits where
  "positive_zero_bits = \<lparr>negative_bit = False, exponent_field = 0,
     fraction_field = 0\<rparr>"

definition negative_zero_bits :: fp_bits where
  "negative_zero_bits = \<lparr>negative_bit = True, exponent_field = 0,
     fraction_field = 0\<rparr>"

lemma decode_positive_zero [simp]:
  "0 < exponent_bits f \<Longrightarrow>
   decode_bits f positive_zero_bits = Dynamic_Finite False 0"
proof -
  assume "0 < exponent_bits f"
  then have "exponent_all_ones f \<noteq> 0"
    unfolding exponent_all_ones_def
    using one_less_power[of "2::nat" "exponent_bits f"] by simp
  then show ?thesis
    by (simp add: decode_bits_def positive_zero_bits_def bits_is_nan_def
        bits_is_infinity_def finite_magnitude_def)
qed

lemma decode_negative_zero [simp]:
  "0 < exponent_bits f \<Longrightarrow>
   decode_bits f negative_zero_bits = Dynamic_Finite True 0"
proof -
  assume "0 < exponent_bits f"
  then have "exponent_all_ones f \<noteq> 0"
    unfolding exponent_all_ones_def
    using one_less_power[of "2::nat" "exponent_bits f"] by simp
  then show ?thesis
    by (simp add: decode_bits_def negative_zero_bits_def bits_is_nan_def
        bits_is_infinity_def finite_magnitude_def)
qed

lemma signed_zeros_distinct:
  "decode_bits f positive_zero_bits \<noteq> decode_bits f negative_zero_bits"
  if "0 < exponent_bits f"
  using that by simp

lemma well_formed_exponent_field:
  "bits_well_formed f x \<Longrightarrow> exponent_field x < 2 ^ exponent_bits f"
  by (simp add: bits_well_formed_def)

lemma well_formed_fraction_field:
  "bits_well_formed f x \<Longrightarrow> fraction_field x < 2 ^ fraction_bits f"
  by (simp add: bits_well_formed_def)

text \<open>Concrete instances used by the Rust tests and SMT-LIB front end.\<close>

definition binary16 :: binary_format where
  "binary16 = \<lparr>exponent_bits = 5, precision_bits = 11\<rparr>"

definition binary32 :: binary_format where
  "binary32 = \<lparr>exponent_bits = 8, precision_bits = 24\<rparr>"

definition binary64 :: binary_format where
  "binary64 = \<lparr>exponent_bits = 11, precision_bits = 53\<rparr>"

lemma standard_formats_valid [simp]:
  "valid_format binary16" "valid_format binary32" "valid_format binary64"
  by (simp_all add: valid_format_def binary16_def binary32_def binary64_def)

lemma binary16_parameters [simp]:
  "fraction_bits binary16 = 10"
  "format_bias binary16 = 15"
  "format_emin binary16 = -14"
  "format_emax binary16 = 15"
  by (simp_all add: fraction_bits_def format_bias_def format_emin_def format_emax_def
      binary16_def)

lemma binary32_parameters [simp]:
  "fraction_bits binary32 = 23"
  "format_bias binary32 = 127"
  "format_emin binary32 = -126"
  "format_emax binary32 = 127"
  by (simp_all add: fraction_bits_def format_bias_def format_emin_def format_emax_def
      binary32_def)

lemma binary64_parameters [simp]:
  "fraction_bits binary64 = 52"
  "format_bias binary64 = 1023"
  "format_emin binary64 = -1022"
  "format_emax binary64 = 1023"
  by (simp_all add: fraction_bits_def format_bias_def format_emin_def format_emax_def
      binary64_def)

end

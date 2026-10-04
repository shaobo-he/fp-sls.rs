theory Fp_Round_Int
  imports Main
begin

section \<open>Exact quotient/remainder rounding\<close>

text \<open>
  This theory isolates the integer rounding step used by
  \<open>src/data/fp.rs\<close>.  The numerator is a non-negative
  magnitude, the denominator is positive, and the Boolean argument records
  the sign of the original value.  Thus rounding upward below means increasing
  the magnitude by one.
\<close>

datatype fp_round_mode = RNE | RNA | RTZ | RTP | RTN

fun round_up :: "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "round_up RNE negative q r d = (d < 2 * r \<or> (d = 2 * r \<and> odd q))"
| "round_up RNA negative q r d = (d \<le> 2 * r)"
| "round_up RTZ negative q r d = False"
| "round_up RTP negative q r d = (\<not> negative)"
| "round_up RTN negative q r d = negative"

definition round_quotient ::
  "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "round_quotient rm negative q r d =
    (if r = 0 then q else if round_up rm negative q r d then q + 1 else q)"

definition round_integer ::
  "fp_round_mode \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "round_integer rm negative n d =
    round_quotient rm negative (n div d) (n mod d) d"

definition ceil_quotient :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ceil_quotient n d = (if n mod d = 0 then n div d else n div d + 1)"

text \<open>
  @{const round_quotient} is the direct counterpart of the Rust helper once
  @{term q} and @{term r} have been obtained by Euclidean division.  Keeping it
  separate makes the mode decision independent of any floating-point format.
\<close>

lemma round_quotient_exact [simp]:
  "round_quotient rm negative q 0 d = q"
  by (simp add: round_quotient_def)

lemma round_quotient_cases:
  "round_quotient rm negative q r d = q \<or>
   round_quotient rm negative q r d = q + 1"
  by (auto simp: round_quotient_def)

lemma round_quotient_bounds:
  "q \<le> round_quotient rm negative q r d \<and>
   round_quotient rm negative q r d \<le> q + 1"
  using round_quotient_cases[of rm negative q r d] by auto

lemma round_quotient_RTZ [simp]:
  "round_quotient RTZ negative q r d = q"
  by (simp add: round_quotient_def)

lemma round_quotient_RTP_positive [simp]:
  "round_quotient RTP False q r d = (if r = 0 then q else q + 1)"
  by (simp add: round_quotient_def)

lemma round_quotient_RTP_negative [simp]:
  "round_quotient RTP True q r d = q"
  by (simp add: round_quotient_def)

lemma round_quotient_RTN_positive [simp]:
  "round_quotient RTN False q r d = q"
  by (simp add: round_quotient_def)

lemma round_quotient_RTN_negative [simp]:
  "round_quotient RTN True q r d = (if r = 0 then q else q + 1)"
  by (simp add: round_quotient_def)

section \<open>Nearest-mode decisions\<close>

lemma nearest_below_half:
  assumes "2 * r < d"
  shows "round_quotient RNE negative q r d = q"
    and "round_quotient RNA negative q r d = q"
proof -
  have "\<not> d < 2 * r" and "d \<noteq> 2 * r" and "\<not> d \<le> 2 * r"
    using assms by linarith+
  then show "round_quotient RNE negative q r d = q"
    and "round_quotient RNA negative q r d = q"
    by (simp_all add: round_quotient_def)
qed

lemma nearest_above_half:
  assumes "d < 2 * r"
  shows "round_quotient RNE negative q r d = q + 1"
    and "round_quotient RNA negative q r d = q + 1"
proof -
  have "r \<noteq> 0" using assms by auto
  with assms show "round_quotient RNE negative q r d = q + 1"
    and "round_quotient RNA negative q r d = q + 1"
    by (simp_all add: round_quotient_def)
qed

lemma RNE_at_half:
  assumes "0 < d" "d = 2 * r"
  shows "round_quotient RNE negative q r d = (if odd q then q + 1 else q)"
proof -
  have "r \<noteq> 0" using assms by auto
  with assms show ?thesis by (simp add: round_quotient_def)
qed

lemma RNA_at_half:
  assumes "0 < d" "d = 2 * r"
  shows "round_quotient RNA negative q r d = q + 1"
proof -
  have "r \<noteq> 0" using assms by auto
  with assms show ?thesis by (simp add: round_quotient_def)
qed

lemma RNE_at_half_is_even:
  assumes "0 < d" "d = 2 * r"
  shows "even (round_quotient RNE negative q r d)"
proof (cases "odd q")
  case True
  with RNE_at_half[OF assms] show ?thesis by simp
next
  case False
  with RNE_at_half[OF assms] show ?thesis by simp
qed

definition quotient_error :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "quotient_error q r d m = (if m = q then r else d - r)"

lemma RNE_quotient_error_half:
  assumes "r < d"
  shows "2 * quotient_error q r d (round_quotient RNE negative q r d) \<le> d"
proof (cases "r = 0")
  case True
  then show ?thesis by (simp add: quotient_error_def)
next
  case False
  consider (below) "2 * r < d" | (tie) "2 * r = d" | (above) "d < 2 * r"
    by linarith
  then show ?thesis
  proof cases
    case below
    then have eq: "round_quotient RNE negative q r d = q"
      by (rule nearest_below_half(1))
    from below show ?thesis by (simp add: quotient_error_def eq)
  next
    case tie
    then have d: "d = 2 * r" by simp
    have dpos: "0 < d" using assms by auto
    show ?thesis
    proof (cases "odd q")
      case True
      with RNE_at_half[OF dpos d] tie show ?thesis
        by (simp add: quotient_error_def)
    next
      case False
      with RNE_at_half[OF dpos d] tie show ?thesis
        by (simp add: quotient_error_def)
    qed
  next
    case above
    then have eq: "round_quotient RNE negative q r d = q + 1"
      by (rule nearest_above_half(1))
    from assms above show ?thesis
      by (simp add: quotient_error_def eq; linarith)
  qed
qed

lemma RNA_quotient_error_half:
  assumes "r < d"
  shows "2 * quotient_error q r d (round_quotient RNA negative q r d) \<le> d"
proof (cases "r = 0")
  case True
  then show ?thesis by (simp add: quotient_error_def)
next
  case False
  consider (below) "2 * r < d" | (tie) "2 * r = d" | (above) "d < 2 * r"
    by linarith
  then show ?thesis
  proof cases
    case below
    then have eq: "round_quotient RNA negative q r d = q"
      by (rule nearest_below_half(2))
    from below show ?thesis by (simp add: quotient_error_def eq)
  next
    case tie
    then have d: "d = 2 * r" by simp
    have dpos: "0 < d" using assms by auto
    have eq: "round_quotient RNA negative q r d = q + 1"
      by (rule RNA_at_half[OF dpos d])
    from tie show ?thesis by (simp add: quotient_error_def eq)
  next
    case above
    then have eq: "round_quotient RNA negative q r d = q + 1"
      by (rule nearest_above_half(2))
    from assms above show ?thesis
      by (simp add: quotient_error_def eq; linarith)
  qed
qed

section \<open>Consequences for a numerator and denominator\<close>

lemma round_integer_exact [simp]:
  assumes "n mod d = 0"
  shows "round_integer rm negative n d = n div d"
  using assms by (simp add: round_integer_def)

lemma round_integer_zero [simp]:
  "round_integer rm negative 0 d = 0"
  by (simp add: round_integer_def)

lemma round_integer_multiple [simp]:
  assumes "0 < d"
  shows "round_integer rm negative (k * d) d = k"
  using assms by (simp add: round_integer_def)

lemma round_integer_cases:
  "round_integer rm negative n d = n div d \<or>
   round_integer rm negative n d = n div d + 1"
  unfolding round_integer_def by (rule round_quotient_cases)

lemma round_integer_cases_strict:
  "round_integer rm negative n d = n div d \<or>
   (round_integer rm negative n d = n div d + 1 \<and> n mod d \<noteq> 0)"
  by (auto simp: round_integer_def round_quotient_def)

lemma round_integer_bounds:
  "n div d \<le> round_integer rm negative n d \<and>
   round_integer rm negative n d \<le> n div d + 1"
  unfolding round_integer_def by (rule round_quotient_bounds)

lemma round_integer_RTZ [simp]:
  "round_integer RTZ negative n d = n div d"
  by (simp add: round_integer_def)

lemma round_integer_RTP_positive [simp]:
  "round_integer RTP False n d = ceil_quotient n d"
  by (simp add: round_integer_def ceil_quotient_def)

lemma round_integer_RTP_negative [simp]:
  "round_integer RTP True n d = n div d"
  by (simp add: round_integer_def)

lemma round_integer_RTN_positive [simp]:
  "round_integer RTN False n d = n div d"
  by (simp add: round_integer_def)

lemma round_integer_RTN_negative [simp]:
  "round_integer RTN True n d = ceil_quotient n d"
  by (simp add: round_integer_def ceil_quotient_def)

lemma nearest_integer_below_half:
  assumes "2 * (n mod d) < d"
  shows "round_integer RNE negative n d = n div d"
    and "round_integer RNA negative n d = n div d"
  unfolding round_integer_def using nearest_below_half[OF assms] by auto

lemma nearest_integer_above_half:
  assumes "d < 2 * (n mod d)"
  shows "round_integer RNE negative n d = n div d + 1"
    and "round_integer RNA negative n d = n div d + 1"
  unfolding round_integer_def using nearest_above_half[OF assms] by auto

lemma RNE_integer_at_half:
  assumes "0 < d" "d = 2 * (n mod d)"
  shows "round_integer RNE negative n d =
    (if odd (n div d) then n div d + 1 else n div d)"
  unfolding round_integer_def by (rule RNE_at_half[OF assms])

lemma RNA_integer_at_half:
  assumes "0 < d" "d = 2 * (n mod d)"
  shows "round_integer RNA negative n d = n div d + 1"
  unfolding round_integer_def by (rule RNA_at_half[OF assms])

lemma RNE_integer_at_half_is_even:
  assumes "0 < d" "d = 2 * (n mod d)"
  shows "even (round_integer RNE negative n d)"
  unfolding round_integer_def by (rule RNE_at_half_is_even[OF assms])

section \<open>Error and directed-rounding properties\<close>

definition scaled_error :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "scaled_error n d m = (if m * d \<le> n then n - m * d else m * d - n)"

lemma scaled_error_floor:
  "scaled_error n d (n div d) = n mod d"
proof -
  have diff: "n - n div d * d = n mod d"
    by (rule minus_div_mult_eq_mod)
  show ?thesis
    using diff by (simp add: scaled_error_def)
qed

lemma scaled_error_upper:
  assumes "0 < d"
  shows "scaled_error n d (n div d + 1) = d - n mod d"
proof -
  have upper: "n < (n div d + 1) * d"
    using dividend_less_div_times[OF assms, of n]
    by (simp add: add_mult_distrib ac_simps)
  have decomp: "n div d * d + n mod d = n"
    by (rule div_mult_mod_eq)
  have expand: "(n div d + 1) * d = n div d * d + d"
    by (simp add: add_mult_distrib)
  have diff: "(n div d + 1) * d - n = d - n mod d"
  proof -
    have cancel:
      "(n div d * d + d) - (n div d * d + n mod d) = d - n mod d"
      by (rule add_diff_cancel_left)
    from expand decomp cancel show ?thesis by metis
  qed
  from upper diff show ?thesis by (simp add: scaled_error_def)
qed

lemma RNE_scaled_error_half:
  assumes "0 < d"
  shows "2 * scaled_error n d (round_integer RNE negative n d) \<le> d"
proof -
  have rem: "n mod d < d" using assms by simp
  have core:
    "2 * quotient_error (n div d) (n mod d) d
      (round_integer RNE negative n d) \<le> d"
    unfolding round_integer_def by (rule RNE_quotient_error_half[OF rem])
  have err:
    "scaled_error n d (round_integer RNE negative n d) =
      quotient_error (n div d) (n mod d) d
        (round_integer RNE negative n d)"
  proof (cases "round_integer RNE negative n d = n div d")
    case True
    then show ?thesis by (simp add: quotient_error_def scaled_error_floor)
  next
    case False
    with round_integer_cases[of RNE negative n d]
    have eq: "round_integer RNE negative n d = n div d + 1" by auto
    have scaled:
      "scaled_error n d (round_integer RNE negative n d) = d - n mod d"
      using eq scaled_error_upper[OF assms] by simp
    have quotient:
      "quotient_error (n div d) (n mod d) d
        (round_integer RNE negative n d) = d - n mod d"
      using False by (simp add: quotient_error_def)
    from scaled quotient show ?thesis by simp
  qed
  from core show ?thesis by (simp add: err)
qed

lemma RNA_scaled_error_half:
  assumes "0 < d"
  shows "2 * scaled_error n d (round_integer RNA negative n d) \<le> d"
proof -
  have rem: "n mod d < d" using assms by simp
  have core:
    "2 * quotient_error (n div d) (n mod d) d
      (round_integer RNA negative n d) \<le> d"
    unfolding round_integer_def by (rule RNA_quotient_error_half[OF rem])
  have err:
    "scaled_error n d (round_integer RNA negative n d) =
      quotient_error (n div d) (n mod d) d
        (round_integer RNA negative n d)"
  proof (cases "round_integer RNA negative n d = n div d")
    case True
    then show ?thesis by (simp add: quotient_error_def scaled_error_floor)
  next
    case False
    with round_integer_cases[of RNA negative n d]
    have eq: "round_integer RNA negative n d = n div d + 1" by auto
    have scaled:
      "scaled_error n d (round_integer RNA negative n d) = d - n mod d"
      using eq scaled_error_upper[OF assms] by simp
    have quotient:
      "quotient_error (n div d) (n mod d) d
        (round_integer RNA negative n d) = d - n mod d"
      using False by (simp add: quotient_error_def)
    from scaled quotient show ?thesis by simp
  qed
  from core show ?thesis by (simp add: err)
qed

lemma ceil_quotient_scaled_ge:
  assumes "0 < d"
  shows "n \<le> ceil_quotient n d * d"
proof (cases "n mod d = 0")
  case True
  have "n div d * d + n mod d = n" by (rule div_mult_mod_eq)
  with True show ?thesis by (simp add: ceil_quotient_def)
next
  case False
  have "n < (n div d + 1) * d"
    using dividend_less_div_times[OF assms, of n]
    by (simp add: add_mult_distrib ac_simps)
  with False show ?thesis by (simp add: ceil_quotient_def)
qed

lemma RTZ_magnitude_toward_zero:
  "round_integer RTZ negative n d * d \<le> n"
  by simp

definition signed_mag :: "bool \<Rightarrow> nat \<Rightarrow> int" where
  "signed_mag negative n = (if negative then - int n else int n)"

lemma signed_mag_positive_le_iff [simp]:
  "signed_mag False a \<le> signed_mag False b \<longleftrightarrow> a \<le> b"
  by (simp add: signed_mag_def)

lemma signed_mag_negative_le_iff [simp]:
  "signed_mag True a \<le> signed_mag True b \<longleftrightarrow> b \<le> a"
  by (simp add: signed_mag_def)

lemma RTP_directed:
  assumes "0 < d"
  shows "signed_mag negative n \<le>
    signed_mag negative (round_integer RTP negative n d * d)"
proof (cases negative)
  case False
  with ceil_quotient_scaled_ge[OF assms, of n] show ?thesis
    by simp
next
  case True
  then show ?thesis by simp
qed

lemma RTN_directed:
  assumes "0 < d"
  shows "signed_mag negative (round_integer RTN negative n d * d) \<le>
    signed_mag negative n"
proof (cases negative)
  case False
  then show ?thesis by simp
next
  case True
  with ceil_quotient_scaled_ge[OF assms, of n] show ?thesis
    by simp
qed

lemma RTZ_directed:
  shows "if negative
    then signed_mag negative n \<le>
      signed_mag negative (round_integer RTZ negative n d * d)
    else signed_mag negative (round_integer RTZ negative n d * d) \<le>
      signed_mag negative n"
  by (cases negative) simp_all

lemma round_integer_unit_interval:
  assumes "0 < d"
  shows "round_integer rm negative n d * d < n + d"
    and "n < (round_integer rm negative n d + 1) * d"
proof -
  have cases:
    "round_integer rm negative n d = n div d \<or>
     (round_integer rm negative n d = n div d + 1 \<and> n mod d \<noteq> 0)"
    using round_integer_cases_strict[of rm negative n d] by blast
  then show "round_integer rm negative n d * d < n + d"
  proof
    assume eq: "round_integer rm negative n d = n div d"
    have "n div d * d \<le> n" by simp
    also have "n < n + d" using assms by simp
    finally show ?thesis using eq by simp
  next
    assume upper:
      "round_integer rm negative n d = n div d + 1 \<and> n mod d \<noteq> 0"
    have decomp: "n div d * d + n mod d = n" by (rule div_mult_mod_eq)
    have rempos: "0 < n mod d" using upper by simp
    have quotient_lt: "n div d * d < n"
    proof -
      have "n div d * d < n div d * d + n mod d"
        using rempos by (rule less_add_same_cancel1[THEN iffD2])
      also have "... = n" by (rule decomp)
      finally show ?thesis .
    qed
    have expand: "(n div d + 1) * d = n div d * d + d"
      by (simp add: add_mult_distrib)
    have "(n div d + 1) * d < n + d"
      using quotient_lt expand by simp
    with upper show ?thesis by simp
  qed
  show "n < (round_integer rm negative n d + 1) * d"
  proof (cases "round_integer rm negative n d = n div d")
    case True
    with dividend_less_div_times[OF assms, of n] show ?thesis
      by (simp add: add_mult_distrib ac_simps)
  next
    case False
    with round_integer_cases[of rm negative n d]
    have eq: "round_integer rm negative n d = n div d + 1" by auto
    have base: "n < (n div d + 1) * d"
      using dividend_less_div_times[OF assms, of n]
      by (simp add: add_mult_distrib ac_simps)
    have "(n div d + 1) * d < (n div d + 2) * d"
      using assms by simp
    with base eq show ?thesis by simp
  qed
qed

end

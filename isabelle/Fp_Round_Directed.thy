(* SPDX-License-Identifier: MIT *)

section \<open>Global correctness of directed rational rounding\<close>

theory Fp_Round_Directed
  imports Fp_Round_Local Fp_Finite_Grid
begin

text \<open>
  Directed rounding is first characterized on an arbitrary power-of-two grid.
  The result is not merely on the requested side of the exact rational: it is
  the extremal grid point on that side.  These lemmas are the directed-mode
  analogue of the nearest-grid-point results in \<open>Fp_Round_Value\<close>.
\<close>

lemma scaled_RTP_value_least:
  assumes denominator: "0 < d"
      and competitor:
        "scaled_exact_value negative n d k \<le>
          signed_rat negative (of_nat z)"
  shows "scaled_rounded_value RTP negative n d k \<le>
    signed_rat negative (of_nat z)"
proof (cases negative)
  case False
  let ?m = "scaled_round_integer RTP False n d k"
  let ?x = "(of_nat n / of_nat d) * rat_pow2 k"
  have upper: "(of_nat ?m :: rat) < ?x + 1"
    by (rule scaled_round_value_unit_interval(1)[OF denominator])
  show ?thesis
  proof (rule ccontr)
    assume not_le: "\<not> scaled_rounded_value RTP negative n d k \<le>
      signed_rat negative (of_nat z)"
    with False have strict: "z < ?m"
      by (simp add: scaled_rounded_value_def)
    then have successor: "z + 1 \<le> ?m" by simp
    have cast_successor: "(of_nat z :: rat) + 1 \<le> of_nat ?m"
      using successor by simp
    from competitor False have "?x \<le> (of_nat z :: rat)"
      by (simp add: scaled_exact_value_def)
    with cast_successor upper show False by linarith
  qed
next
  case True
  let ?m = "scaled_round_integer RTP True n d k"
  let ?x = "(of_nat n / of_nat d) * rat_pow2 k"
  have lower: "?x < (of_nat ?m :: rat) + 1"
    by (rule scaled_round_value_unit_interval(2)[OF denominator])
  show ?thesis
  proof (rule ccontr)
    assume not_le: "\<not> scaled_rounded_value RTP negative n d k \<le>
      signed_rat negative (of_nat z)"
    with True have strict: "?m < z"
      by (simp add: scaled_rounded_value_def)
    then have successor: "?m + 1 \<le> z" by simp
    have cast_successor: "(of_nat ?m :: rat) + 1 \<le> of_nat z"
      using successor by simp
    from competitor True have "(of_nat z :: rat) \<le> ?x"
      by (simp add: scaled_exact_value_def)
    with cast_successor lower show False by linarith
  qed
qed

lemma scaled_RTN_value_greatest:
  assumes denominator: "0 < d"
      and competitor:
        "signed_rat negative (of_nat z) \<le>
          scaled_exact_value negative n d k"
  shows "signed_rat negative (of_nat z) \<le>
    scaled_rounded_value RTN negative n d k"
proof (cases negative)
  case False
  let ?m = "scaled_round_integer RTN False n d k"
  let ?x = "(of_nat n / of_nat d) * rat_pow2 k"
  have lower: "?x < (of_nat ?m :: rat) + 1"
    by (rule scaled_round_value_unit_interval(2)[OF denominator])
  show ?thesis
  proof (rule ccontr)
    assume not_le: "\<not> signed_rat negative (of_nat z) \<le>
      scaled_rounded_value RTN negative n d k"
    with False have strict: "?m < z"
      by (simp add: scaled_rounded_value_def)
    then have successor: "?m + 1 \<le> z" by simp
    have cast_successor: "(of_nat ?m :: rat) + 1 \<le> of_nat z"
      using successor by simp
    from competitor False have "(of_nat z :: rat) \<le> ?x"
      by (simp add: scaled_exact_value_def)
    with cast_successor lower show False by linarith
  qed
next
  case True
  let ?m = "scaled_round_integer RTN True n d k"
  let ?x = "(of_nat n / of_nat d) * rat_pow2 k"
  have upper: "(of_nat ?m :: rat) < ?x + 1"
    by (rule scaled_round_value_unit_interval(1)[OF denominator])
  show ?thesis
  proof (rule ccontr)
    assume not_le: "\<not> signed_rat negative (of_nat z) \<le>
      scaled_rounded_value RTN negative n d k"
    with True have strict: "z < ?m"
      by (simp add: scaled_rounded_value_def)
    then have successor: "z + 1 \<le> ?m" by simp
    have cast_successor: "(of_nat z :: rat) + 1 \<le> of_nat ?m"
      using successor by simp
    from competitor True have "?x \<le> (of_nat z :: rat)"
      by (simp add: scaled_exact_value_def)
    with cast_successor upper show False by linarith
  qed
qed

lemma scaled_RTZ_value_extremal:
  assumes denominator: "0 < d"
  shows
    "if negative then
       scaled_exact_value negative n d k \<le>
         signed_rat negative (of_nat z) \<longrightarrow>
       scaled_rounded_value RTZ negative n d k \<le>
         signed_rat negative (of_nat z)
     else
       signed_rat negative (of_nat z) \<le>
         scaled_exact_value negative n d k \<longrightarrow>
       signed_rat negative (of_nat z) \<le>
         scaled_rounded_value RTZ negative n d k"
proof (cases negative)
  case True
  have identity:
    "scaled_rounded_value RTZ True n d k =
      scaled_rounded_value RTP True n d k"
    by (simp add: scaled_rounded_value_def scaled_round_integer_def)
  with True show ?thesis
    using scaled_RTP_value_least[OF denominator, of True n k z]
    by simp
next
  case False
  have identity:
    "scaled_rounded_value RTZ False n d k =
      scaled_rounded_value RTN False n d k"
    by (simp add: scaled_rounded_value_def scaled_round_integer_def)
  with False show ?thesis
    using scaled_RTN_value_greatest[OF denominator, of False z n k]
    by simp
qed

lemma grid_RTP_value_least:
  assumes denominator: "0 < d"
      and competitor:
        "exact_input_value negative n d \<le> grid_point_value negative k z"
  shows "rounded_grid_value RTP negative n d k \<le>
    grid_point_value negative k z"
proof -
  have step_pos: "0 < rat_pow2 (- k)" by simp
  have competitor_scaled:
    "scaled_exact_value negative n d k \<le>
      signed_rat negative (of_nat z)"
  proof -
    have "scaled_exact_value negative n d k * rat_pow2 (- k) \<le>
      signed_rat negative (of_nat z) * rat_pow2 (- k)"
      using competitor
      by (simp only: scaled_exact_value_unscale signed_grid_point_unscale)
    then show ?thesis using step_pos by simp
  qed
  have extremal:
    "scaled_rounded_value RTP negative n d k \<le>
      signed_rat negative (of_nat z)"
    by (rule scaled_RTP_value_least[OF denominator competitor_scaled])
  have "scaled_rounded_value RTP negative n d k * rat_pow2 (- k) \<le>
      signed_rat negative (of_nat z) * rat_pow2 (- k)"
    by (rule mult_right_mono[OF extremal]) simp
  then show ?thesis
    by (simp only: scaled_rounded_value_unscale signed_grid_point_unscale)
qed

lemma grid_RTN_value_greatest:
  assumes denominator: "0 < d"
      and competitor:
        "grid_point_value negative k z \<le> exact_input_value negative n d"
  shows "grid_point_value negative k z \<le>
    rounded_grid_value RTN negative n d k"
proof -
  have step_pos: "0 < rat_pow2 (- k)" by simp
  have competitor_scaled:
    "signed_rat negative (of_nat z) \<le>
      scaled_exact_value negative n d k"
  proof -
    have "signed_rat negative (of_nat z) * rat_pow2 (- k) \<le>
      scaled_exact_value negative n d k * rat_pow2 (- k)"
      using competitor
      by (simp only: signed_grid_point_unscale scaled_exact_value_unscale)
    then show ?thesis using step_pos by simp
  qed
  have extremal:
    "signed_rat negative (of_nat z) \<le>
      scaled_rounded_value RTN negative n d k"
    by (rule scaled_RTN_value_greatest[OF denominator competitor_scaled])
  have "signed_rat negative (of_nat z) * rat_pow2 (- k) \<le>
      scaled_rounded_value RTN negative n d k * rat_pow2 (- k)"
    by (rule mult_right_mono[OF extremal]) simp
  then show ?thesis
    by (simp only: signed_grid_point_unscale scaled_rounded_value_unscale)
qed

lemma grid_RTZ_value_extremal:
  assumes denominator: "0 < d"
  shows
    "if negative then
       exact_input_value negative n d \<le> grid_point_value negative k z \<longrightarrow>
       rounded_grid_value RTZ negative n d k \<le>
         grid_point_value negative k z
     else
       grid_point_value negative k z \<le> exact_input_value negative n d \<longrightarrow>
       grid_point_value negative k z \<le>
         rounded_grid_value RTZ negative n d k"
proof (cases negative)
  case True
  have identity:
    "rounded_grid_value RTZ True n d k =
      rounded_grid_value RTP True n d k"
    by (simp add: rounded_grid_value_def scaled_round_integer_def)
  with True show ?thesis
    using grid_RTP_value_least[OF denominator, of True n k z]
    by simp
next
  case False
  have identity:
    "rounded_grid_value RTZ False n d k =
      rounded_grid_value RTN False n d k"
    by (simp add: rounded_grid_value_def scaled_round_integer_def)
  with False show ?thesis
    using grid_RTN_value_greatest[OF denominator, of False k z n]
    by simp
qed

section \<open>Representable competitors on the algorithm's grid\<close>

lemma finite_magnitude_as_minimum_grid_point:
  obtains m :: nat where
    "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
proof -
  obtain m :: nat where magnitude:
    "finite_magnitude f b = of_nat m * minimum_subnormal_step f"
    by (rule finite_magnitude_on_minimum_subnormal_grid)
  show thesis
  proof (rule that[of m])
    show "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
      using magnitude
      by (cases negative)
        (simp_all add: grid_point_value_def minimum_subnormal_step_def
          pow2_rat_eq_rat_pow2)
  qed
qed

lemma finite_magnitude_above_power_as_grid_point:
  assumes valid: "valid_format f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and exponent_lower: "format_emin f \<le> e"
      and magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
  obtains m :: nat where
    "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative (int (fraction_bits f) - e) m"
proof -
  obtain m :: nat where magnitude:
    "finite_magnitude f b =
      of_nat m * pow2_rat (e - int (fraction_bits f))"
    by (rule finite_magnitude_above_power_on_grid[
          OF valid well_formed finite_exponent exponent_lower magnitude_lower])
  show thesis
  proof (rule that[of m])
    show "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative (int (fraction_bits f) - e) m"
      using magnitude
      by (cases negative)
        (simp_all add: grid_point_value_def pow2_rat_eq_rat_pow2)
  qed
qed

lemma normal_rounded_grid_magnitude_lower:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
  shows "pow2_rat e \<le>
    of_nat (scaled_round_integer rm negative n d
      (int (fraction_bits f) - e)) *
      pow2_rat (e - int (fraction_bits f))"
proof -
  have significand_lower:
    "2 ^ fraction_bits f \<le>
      scaled_round_integer rm negative n d
        (int (fraction_bits f) - e)"
    using normal_rounded_significand_bounds[OF valid denominator rel]
    by blast
  have coefficient:
    "(of_nat (2 ^ fraction_bits f) :: rat) \<le>
      of_nat (scaled_round_integer rm negative n d
        (int (fraction_bits f) - e))"
    using significand_lower by simp
  have scaled:
    "(of_nat (2 ^ fraction_bits f) :: rat) *
        pow2_rat (e - int (fraction_bits f)) \<le>
      of_nat (scaled_round_integer rm negative n d
        (int (fraction_bits f) - e)) *
        pow2_rat (e - int (fraction_bits f))"
    by (rule mult_right_mono[OF coefficient]) simp
  show ?thesis
    using scaled pow2_rat_split_fraction_width[of e f] by simp
qed

lemma normal_rounded_grid_boundary:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
  shows
    "if negative then
       rounded_grid_value rm negative n d
          (int (fraction_bits f) - e) \<le> - pow2_rat e
     else
       pow2_rat e \<le>
         rounded_grid_value rm negative n d
           (int (fraction_bits f) - e)"
proof -
  have lower:
    "pow2_rat e \<le>
      of_nat (scaled_round_integer rm negative n d
        (int (fraction_bits f) - e)) *
        pow2_rat (e - int (fraction_bits f))"
    by (rule normal_rounded_grid_magnitude_lower[OF valid denominator rel])
  show ?thesis
    using lower
    by (cases negative)
      (simp_all add: rounded_grid_value_def grid_point_value_def
        pow2_rat_eq_rat_pow2)
qed

section \<open>Rounded-core direction and finite extremality\<close>

lemma round_rational_core_at_RTP_directed:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
  shows "exact_input_value negative n d \<le>
    rounded_core_value f negative
      (round_rational_core_at f RTP negative n d e)"
proof -
  have normal:
    "exact_input_value negative n d \<le>
      rounded_grid_value RTP negative n d
        (int (fraction_bits f) - e)"
    by (rule grid_RTP_value_directed[OF denominator])
  have subnormal:
    "exact_input_value negative n d \<le>
      rounded_grid_value RTP negative n d
        (int (fraction_bits f) - format_emin f)"
    by (rule grid_RTP_value_directed[OF denominator])
  show ?thesis
    using round_rational_core_at_value[OF valid,
      of negative RTP n d e] normal subnormal
    by (cases "format_emin f \<le> e") simp_all
qed

lemma round_rational_core_at_RTN_directed:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
  shows "rounded_core_value f negative
      (round_rational_core_at f RTN negative n d e) \<le>
    exact_input_value negative n d"
proof -
  have normal:
    "rounded_grid_value RTN negative n d
        (int (fraction_bits f) - e) \<le>
      exact_input_value negative n d"
    by (rule grid_RTN_value_directed[OF denominator])
  have subnormal:
    "rounded_grid_value RTN negative n d
        (int (fraction_bits f) - format_emin f) \<le>
      exact_input_value negative n d"
    by (rule grid_RTN_value_directed[OF denominator])
  show ?thesis
    using round_rational_core_at_value[OF valid,
      of negative RTN n d e] normal subnormal
    by (cases "format_emin f \<le> e") simp_all
qed

lemma round_rational_core_at_RTZ_directed:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         rounded_core_value f negative
           (round_rational_core_at f RTZ negative n d e)
     else
       rounded_core_value f negative
           (round_rational_core_at f RTZ negative n d e) \<le>
         exact_input_value negative n d"
proof -
  have normal:
    "if negative then
       exact_input_value negative n d \<le>
         rounded_grid_value RTZ negative n d
           (int (fraction_bits f) - e)
     else
       rounded_grid_value RTZ negative n d
           (int (fraction_bits f) - e) \<le>
         exact_input_value negative n d"
    by (rule grid_RTZ_value_directed[OF denominator])
  have subnormal:
    "if negative then
       exact_input_value negative n d \<le>
         rounded_grid_value RTZ negative n d
           (int (fraction_bits f) - format_emin f)
     else
       rounded_grid_value RTZ negative n d
           (int (fraction_bits f) - format_emin f) \<le>
         exact_input_value negative n d"
    by (rule grid_RTZ_value_directed[OF denominator])
  show ?thesis
    using round_rational_core_at_value[OF valid,
      of negative RTZ n d e] normal subnormal
    by (cases "format_emin f \<le> e"; cases negative) simp_all
qed

lemma round_rational_core_at_subnormal_RTP_least_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and subnormal: "e < format_emin f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat negative (finite_magnitude f b)"
  shows "rounded_core_value f negative
      (round_rational_core_at f RTP negative n d e) \<le>
    signed_rat negative (finite_magnitude f b)"
proof -
  obtain m :: nat where grid:
    "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
    by (rule finite_magnitude_as_minimum_grid_point)
  have extremal:
    "rounded_grid_value RTP negative n d
        (int (fraction_bits f) - format_emin f) \<le>
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
    by (rule grid_RTP_value_least[OF denominator])
      (use competitor grid in simp)
  show ?thesis
    using round_rational_core_at_value[OF valid,
      of negative RTP n d e] subnormal extremal grid
    by simp
qed

lemma round_rational_core_at_subnormal_RTN_greatest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and subnormal: "e < format_emin f"
      and competitor:
        "signed_rat negative (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat negative (finite_magnitude f b) \<le>
    rounded_core_value f negative
      (round_rational_core_at f RTN negative n d e)"
proof -
  obtain m :: nat where grid:
    "signed_rat negative (finite_magnitude f b) =
      grid_point_value negative
        (int (fraction_bits f) - format_emin f) m"
    by (rule finite_magnitude_as_minimum_grid_point)
  have extremal:
    "grid_point_value negative
        (int (fraction_bits f) - format_emin f) m \<le>
      rounded_grid_value RTN negative n d
        (int (fraction_bits f) - format_emin f)"
    by (rule grid_RTN_value_greatest[OF denominator])
      (use competitor grid in simp)
  show ?thesis
    using round_rational_core_at_value[OF valid,
      of negative RTN n d e] subnormal extremal grid
    by simp
qed

lemma round_rational_core_at_normal_RTP_least_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat negative (finite_magnitude f b)"
  shows "rounded_core_value f negative
      (round_rational_core_at f RTP negative n d e) \<le>
    signed_rat negative (finite_magnitude f b)"
proof -
  let ?k = "int (fraction_bits f) - e"
  have core_value:
    "rounded_core_value f negative
        (round_rational_core_at f RTP negative n d e) =
      rounded_grid_value RTP negative n d ?k"
    using round_rational_core_at_value[OF valid,
      of negative RTP n d e] normal by simp
  have exact_lower: "pow2_rat e \<le> exact_magnitude n d"
    using rel by (simp add: floor_log2_rel_def)
  show ?thesis
  proof (cases negative)
    case positive: False
    from competitor positive have exact_to_competitor:
      "exact_magnitude n d \<le> finite_magnitude f b"
      by (simp add: exact_input_value_def exact_magnitude_def)
    have magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
      using exact_lower exact_to_competitor by linarith
    obtain m :: nat where grid:
      "signed_rat False (finite_magnitude f b) =
        grid_point_value False ?k m"
      by (rule finite_magnitude_above_power_as_grid_point[
          OF valid well_formed finite_exponent normal magnitude_lower])
    have extremal:
      "rounded_grid_value RTP False n d ?k \<le>
        grid_point_value False ?k m"
      by (rule grid_RTP_value_least[OF denominator])
        (use competitor positive grid in simp)
    show ?thesis using positive core_value grid extremal by simp
  next
    case negative: True
    show ?thesis
    proof (cases "pow2_rat e \<le> finite_magnitude f b")
      case above: True
      obtain m :: nat where grid:
        "signed_rat True (finite_magnitude f b) =
          grid_point_value True ?k m"
        by (rule finite_magnitude_above_power_as_grid_point[
            OF valid well_formed finite_exponent normal above])
      have extremal:
        "rounded_grid_value RTP True n d ?k \<le>
          grid_point_value True ?k m"
        by (rule grid_RTP_value_least[OF denominator])
          (use competitor negative grid in simp)
      show ?thesis using negative core_value grid extremal by simp
    next
      case below: False
      then have magnitude_below:
        "finite_magnitude f b < pow2_rat e" by simp
      have result_boundary:
        "rounded_grid_value RTP True n d ?k \<le> - pow2_rat e"
        using normal_rounded_grid_boundary[
          OF valid denominator rel, of True RTP]
        by simp
      have boundary_competitor:
        "- pow2_rat e \<le> signed_rat True (finite_magnitude f b)"
        using magnitude_below by simp
      show ?thesis
        using negative core_value result_boundary boundary_competitor
        by simp
    qed
  qed
qed

lemma round_rational_core_at_normal_RTN_greatest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and normal: "format_emin f \<le> e"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat negative (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat negative (finite_magnitude f b) \<le>
    rounded_core_value f negative
      (round_rational_core_at f RTN negative n d e)"
proof -
  let ?k = "int (fraction_bits f) - e"
  have core_value:
    "rounded_core_value f negative
        (round_rational_core_at f RTN negative n d e) =
      rounded_grid_value RTN negative n d ?k"
    using round_rational_core_at_value[OF valid,
      of negative RTN n d e] normal by simp
  have exact_lower: "pow2_rat e \<le> exact_magnitude n d"
    using rel by (simp add: floor_log2_rel_def)
  show ?thesis
  proof (cases negative)
    case negative: True
    from competitor negative have exact_to_competitor:
      "exact_magnitude n d \<le> finite_magnitude f b"
      by (simp add: exact_input_value_def exact_magnitude_def)
    have magnitude_lower: "pow2_rat e \<le> finite_magnitude f b"
      using exact_lower exact_to_competitor by linarith
    obtain m :: nat where grid:
      "signed_rat True (finite_magnitude f b) =
        grid_point_value True ?k m"
      by (rule finite_magnitude_above_power_as_grid_point[
          OF valid well_formed finite_exponent normal magnitude_lower])
    have extremal:
      "grid_point_value True ?k m \<le>
        rounded_grid_value RTN True n d ?k"
      by (rule grid_RTN_value_greatest[OF denominator])
        (use competitor negative grid in simp)
    show ?thesis using negative core_value grid extremal by simp
  next
    case positive: False
    show ?thesis
    proof (cases "pow2_rat e \<le> finite_magnitude f b")
      case above: True
      obtain m :: nat where grid:
        "signed_rat False (finite_magnitude f b) =
          grid_point_value False ?k m"
        by (rule finite_magnitude_above_power_as_grid_point[
            OF valid well_formed finite_exponent normal above])
      have extremal:
        "grid_point_value False ?k m \<le>
          rounded_grid_value RTN False n d ?k"
        by (rule grid_RTN_value_greatest[OF denominator])
          (use competitor positive grid in simp)
      show ?thesis using positive core_value grid extremal by simp
    next
      case below: False
      then have magnitude_below:
        "finite_magnitude f b < pow2_rat e" by simp
      have result_boundary:
        "pow2_rat e \<le> rounded_grid_value RTN False n d ?k"
        using normal_rounded_grid_boundary[
          OF valid denominator rel, of False RTN]
        by simp
      have competitor_boundary:
        "signed_rat False (finite_magnitude f b) \<le> pow2_rat e"
        using magnitude_below by simp
      show ?thesis
        using positive core_value result_boundary competitor_boundary
        by simp
    qed
  qed
qed

theorem round_rational_core_at_RTP_least_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat negative (finite_magnitude f b)"
  shows "rounded_core_value f negative
      (round_rational_core_at f RTP negative n d e) \<le>
    signed_rat negative (finite_magnitude f b)"
proof (cases "format_emin f \<le> e")
  case True
  show ?thesis
    by (rule round_rational_core_at_normal_RTP_least_finite[
      OF valid denominator rel True well_formed finite_exponent competitor])
next
  case False
  then have subnormal: "e < format_emin f" by simp
  show ?thesis
    by (rule round_rational_core_at_subnormal_RTP_least_finite[
      OF valid denominator subnormal competitor])
qed

theorem round_rational_core_at_RTN_greatest_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat negative (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat negative (finite_magnitude f b) \<le>
    rounded_core_value f negative
      (round_rational_core_at f RTN negative n d e)"
proof (cases "format_emin f \<le> e")
  case True
  show ?thesis
    by (rule round_rational_core_at_normal_RTN_greatest_finite[
      OF valid denominator rel True well_formed finite_exponent competitor])
next
  case False
  then have subnormal: "e < format_emin f" by simp
  show ?thesis
    by (rule round_rational_core_at_subnormal_RTN_greatest_finite[
      OF valid denominator subnormal competitor])
qed

lemma round_rational_core_at_RTZ_mode_identity:
  "round_rational_core_at f RTZ negative n d e =
    (if negative then round_rational_core_at f RTP negative n d e
     else round_rational_core_at f RTN negative n d e)"
  by (cases negative)
    (simp_all add: round_rational_core_at_def scaled_round_integer_def)

theorem round_rational_core_at_RTZ_extremal_finite:
  assumes valid: "valid_format f"
      and denominator: "0 < d"
      and rel: "floor_log2_rel n d e"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat negative (finite_magnitude f b) \<longrightarrow>
       rounded_core_value f negative
           (round_rational_core_at f RTZ negative n d e) \<le>
         signed_rat negative (finite_magnitude f b)
     else
       signed_rat negative (finite_magnitude f b) \<le>
         exact_input_value negative n d \<longrightarrow>
       signed_rat negative (finite_magnitude f b) \<le>
         rounded_core_value f negative
           (round_rational_core_at f RTZ negative n d e)"
proof (cases negative)
  case True
  show ?thesis
    using True round_rational_core_at_RTP_least_finite[
      OF valid denominator rel well_formed finite_exponent,
      of True]
      round_rational_core_at_RTZ_mode_identity[
        of f True n d e]
    by simp
next
  case False
  show ?thesis
    using False round_rational_core_at_RTN_greatest_finite[
      OF valid denominator rel well_formed finite_exponent,
      of False]
      round_rational_core_at_RTZ_mode_identity[
        of f False n d e]
    by simp
qed

section \<open>Complete positive-rational algorithm and finite encoding\<close>

corollary round_rational_core_RTP_directed:
  assumes "valid_format f" "0 < d"
  shows "exact_input_value negative n d \<le>
    rounded_core_value f negative
      (round_rational_core f RTP negative n d)"
  unfolding round_rational_core_def
  by (rule round_rational_core_at_RTP_directed[OF assms])

corollary round_rational_core_RTN_directed:
  assumes "valid_format f" "0 < d"
  shows "rounded_core_value f negative
      (round_rational_core f RTN negative n d) \<le>
    exact_input_value negative n d"
  unfolding round_rational_core_def
  by (rule round_rational_core_at_RTN_directed[OF assms])

corollary round_rational_core_RTZ_directed:
  assumes "valid_format f" "0 < d"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         rounded_core_value f negative
           (round_rational_core f RTZ negative n d)
     else
       rounded_core_value f negative
           (round_rational_core f RTZ negative n d) \<le>
         exact_input_value negative n d"
  unfolding round_rational_core_def
  by (rule round_rational_core_at_RTZ_directed[OF assms])

theorem round_rational_core_RTP_least_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat negative (finite_magnitude f b)"
  shows "rounded_core_value f negative
      (round_rational_core f RTP negative n d) \<le>
    signed_rat negative (finite_magnitude f b)"
proof -
  have rel:
    "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  show ?thesis
    unfolding round_rational_core_def
    by (rule round_rational_core_at_RTP_least_finite[
      OF valid denominator rel well_formed finite_exponent competitor])
qed

theorem round_rational_core_RTN_greatest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat negative (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat negative (finite_magnitude f b) \<le>
    rounded_core_value f negative
      (round_rational_core f RTN negative n d)"
proof -
  have rel:
    "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  show ?thesis
    unfolding round_rational_core_def
    by (rule round_rational_core_at_RTN_greatest_finite[
      OF valid denominator rel well_formed finite_exponent competitor])
qed

theorem round_rational_core_RTZ_extremal_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat negative (finite_magnitude f b) \<longrightarrow>
       rounded_core_value f negative
           (round_rational_core f RTZ negative n d) \<le>
         signed_rat negative (finite_magnitude f b)
     else
       signed_rat negative (finite_magnitude f b) \<le>
         exact_input_value negative n d \<longrightarrow>
       signed_rat negative (finite_magnitude f b) \<le>
         rounded_core_value f negative
           (round_rational_core f RTZ negative n d)"
proof -
  have rel:
    "floor_log2_rel n d (floor_log2_spec n d)"
    by (rule floor_log2_spec_correct_positive[OF numerator denominator])
  show ?thesis
    unfolding round_rational_core_def
    by (rule round_rational_core_at_RTZ_extremal_finite[
      OF valid denominator rel well_formed finite_exponent])
qed

text \<open>
  The preceding extremality lemmas compare magnitudes interpreted with the
  input sign.  The next forms use the sign actually stored in the competitor.
  Opposite-sign competitors are either impossible on the requested side, or
  are separated from the result by zero.
\<close>

theorem round_rational_core_RTP_least_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat (negative_bit b) (finite_magnitude f b)"
  shows "rounded_core_value f negative
      (round_rational_core f RTP negative n d) \<le>
    signed_rat (negative_bit b) (finite_magnitude f b)"
proof (cases negative)
  case input_negative: True
  show ?thesis
  proof (cases "negative_bit b")
    case competitor_negative: True
    have same_sign:
      "rounded_core_value f True
          (round_rational_core f RTP True n d) \<le>
        signed_rat True (finite_magnitude f b)"
      by (rule round_rational_core_RTP_least_finite[
        OF valid numerator denominator well_formed finite_exponent])
        (use competitor input_negative competitor_negative in simp)
    show ?thesis
      using input_negative competitor_negative same_sign by simp
  next
    case competitor_positive: False
    have result_nonpositive:
      "rounded_core_value f True
        (round_rational_core f RTP True n d) \<le> 0"
      by (simp add: rounded_core_value_def)
    have competitor_nonnegative:
      "0 \<le> signed_rat False (finite_magnitude f b)" by simp
    show ?thesis
      using input_negative competitor_positive result_nonpositive
        competitor_nonnegative finite_magnitude_nonnegative[of f b]
      by (simp add: input_negative competitor_positive; linarith)
  qed
next
  case input_positive: False
  show ?thesis
  proof (cases "negative_bit b")
    case competitor_negative: True
    have input_positive_value:
      "0 < exact_input_value False n d"
      using numerator denominator
      by (simp add: exact_input_value_def)
    have competitor_nonpositive:
      "signed_rat True (finite_magnitude f b) \<le> 0" by simp
    show ?thesis
      using competitor input_positive competitor_negative
        input_positive_value competitor_nonpositive
        finite_magnitude_nonnegative[of f b]
      by (simp add: input_positive competitor_negative; linarith)
  next
    case competitor_positive: False
    have same_sign:
      "rounded_core_value f False
          (round_rational_core f RTP False n d) \<le>
        signed_rat False (finite_magnitude f b)"
      by (rule round_rational_core_RTP_least_finite[
        OF valid numerator denominator well_formed finite_exponent])
        (use competitor input_positive competitor_positive in simp)
    show ?thesis
      using input_positive competitor_positive same_sign by simp
  qed
qed

theorem round_rational_core_RTN_greatest_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat (negative_bit b) (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat (negative_bit b) (finite_magnitude f b) \<le>
    rounded_core_value f negative
      (round_rational_core f RTN negative n d)"
proof (cases negative)
  case input_negative: True
  show ?thesis
  proof (cases "negative_bit b")
    case competitor_negative: True
    have same_sign:
      "signed_rat True (finite_magnitude f b) \<le>
        rounded_core_value f True
          (round_rational_core f RTN True n d)"
      by (rule round_rational_core_RTN_greatest_finite[
        OF valid numerator denominator well_formed finite_exponent])
        (use competitor input_negative competitor_negative in simp)
    show ?thesis
      using input_negative competitor_negative same_sign by simp
  next
    case competitor_positive: False
    have input_negative_value:
      "exact_input_value True n d < 0"
      using numerator denominator
      by (simp add: exact_input_value_def)
    have competitor_nonnegative:
      "0 \<le> signed_rat False (finite_magnitude f b)" by simp
    show ?thesis
      using competitor input_negative competitor_positive
        input_negative_value competitor_nonnegative
        finite_magnitude_nonnegative[of f b]
      by (simp add: input_negative competitor_positive; linarith)
  qed
next
  case input_positive: False
  show ?thesis
  proof (cases "negative_bit b")
    case competitor_negative: True
    have competitor_nonpositive:
      "signed_rat True (finite_magnitude f b) \<le> 0" by simp
    have result_nonnegative:
      "0 \<le> rounded_core_value f False
        (round_rational_core f RTN False n d)"
      by (simp add: rounded_core_value_def)
    have opposite_sign:
      "signed_rat True (finite_magnitude f b) \<le>
        rounded_core_value f False
          (round_rational_core f RTN False n d)"
      using competitor_nonpositive result_nonnegative by linarith
    show ?thesis
      using input_positive competitor_negative opposite_sign by simp
  next
    case competitor_positive: False
    have same_sign:
      "signed_rat False (finite_magnitude f b) \<le>
        rounded_core_value f False
          (round_rational_core f RTN False n d)"
      by (rule round_rational_core_RTN_greatest_finite[
        OF valid numerator denominator well_formed finite_exponent])
        (use competitor input_positive competitor_positive in simp)
    show ?thesis
      using input_positive competitor_positive same_sign by simp
  qed
qed

theorem round_rational_core_RTZ_extremal_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat (negative_bit b) (finite_magnitude f b) \<longrightarrow>
       rounded_core_value f negative
           (round_rational_core f RTZ negative n d) \<le>
         signed_rat (negative_bit b) (finite_magnitude f b)
     else
       signed_rat (negative_bit b) (finite_magnitude f b) \<le>
         exact_input_value negative n d \<longrightarrow>
       signed_rat (negative_bit b) (finite_magnitude f b) \<le>
         rounded_core_value f negative
           (round_rational_core f RTZ negative n d)"
proof (cases negative)
  case True
  show ?thesis
    using True round_rational_core_RTP_least_finite_bits[
      OF valid numerator denominator well_formed finite_exponent,
      of True]
      round_rational_core_at_RTZ_mode_identity[
        of f True n d "floor_log2_spec n d"]
    unfolding round_rational_core_def
    by simp
next
  case False
  show ?thesis
    using False round_rational_core_RTN_greatest_finite_bits[
      OF valid numerator denominator well_formed finite_exponent,
      of False]
      round_rational_core_at_RTZ_mode_identity[
        of f False n d "floor_log2_spec n d"]
    unfolding round_rational_core_def
    by simp
qed

lemma decode_round_rational_to_format_bits_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f rm negative n d) \<or>
         core_exponent (round_rational_core f rm negative n d) \<le>
           format_emax f"
  shows "decode_bits f
      (round_rational_to_format_bits f rm negative n d) =
    Dynamic_Finite negative
      (rounded_core_magnitude f
        (round_rational_core f rm negative n d))"
proof -
  have invariant:
    "core_encoding_invariant f
      (round_rational_core f rm negative n d)"
    by (rule round_rational_core_invariant[
      OF valid numerator denominator])
  show ?thesis
    unfolding round_rational_to_format_bits_def
    by (rule decode_encode_rounded_core_finite[
      OF valid invariant no_overflow])
qed

lemma round_rational_to_format_bits_finite_signed_value:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f rm negative n d) \<or>
         core_exponent (round_rational_core f rm negative n d) \<le>
           format_emax f"
  shows "signed_rat negative
      (finite_magnitude f
        (round_rational_to_format_bits f rm negative n d)) =
    rounded_core_value f negative
      (round_rational_core f rm negative n d)"
proof -
  let ?out = "round_rational_to_format_bits f rm negative n d"
  let ?c = "round_rational_core f rm negative n d"
  have decoded:
    "decode_bits f ?out =
      Dynamic_Finite negative (rounded_core_magnitude f ?c)"
    by (rule decode_round_rational_to_format_bits_finite[
      OF valid numerator denominator no_overflow])
  have magnitude:
    "finite_magnitude f ?out = rounded_core_magnitude f ?c"
    using decoded
    by (auto simp: decode_bits_def split: if_splits)
  show ?thesis
    using magnitude by (simp add: rounded_core_value_def)
qed

lemma round_rational_to_format_bits_finite_actual_signed_value:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f rm negative n d) \<or>
         core_exponent (round_rational_core f rm negative n d) \<le>
           format_emax f"
  shows "signed_rat
      (negative_bit (round_rational_to_format_bits f rm negative n d))
      (finite_magnitude f
        (round_rational_to_format_bits f rm negative n d)) =
    rounded_core_value f negative
      (round_rational_core f rm negative n d)"
  using round_rational_to_format_bits_finite_signed_value[
    OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTP_directed_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTP negative n d) \<or>
         core_exponent (round_rational_core f RTP negative n d) \<le>
           format_emax f"
  shows "exact_input_value negative n d \<le>
    signed_rat negative
      (finite_magnitude f
        (round_rational_to_format_bits f RTP negative n d))"
  using round_rational_core_RTP_directed[OF valid denominator,
      of negative n]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by (cases negative) simp_all

theorem round_rational_to_format_bits_RTP_least_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTP negative n d) \<or>
         core_exponent (round_rational_core f RTP negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat negative (finite_magnitude f b)"
  shows "signed_rat negative
      (finite_magnitude f
        (round_rational_to_format_bits f RTP negative n d)) \<le>
    signed_rat negative (finite_magnitude f b)"
  using round_rational_core_RTP_least_finite[
      OF valid numerator denominator well_formed finite_exponent competitor]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTN_directed_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTN negative n d) \<or>
         core_exponent (round_rational_core f RTN negative n d) \<le>
           format_emax f"
  shows "signed_rat negative
      (finite_magnitude f
        (round_rational_to_format_bits f RTN negative n d)) \<le>
    exact_input_value negative n d"
  using round_rational_core_RTN_directed[OF valid denominator,
      of negative n]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTN_greatest_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTN negative n d) \<or>
         core_exponent (round_rational_core f RTN negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat negative (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat negative (finite_magnitude f b) \<le>
    signed_rat negative
      (finite_magnitude f
        (round_rational_to_format_bits f RTN negative n d))"
  using round_rational_core_RTN_greatest_finite[
      OF valid numerator denominator well_formed finite_exponent competitor]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTZ_directed_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTZ negative n d) \<or>
         core_exponent (round_rational_core f RTZ negative n d) \<le>
           format_emax f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat negative
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d))
     else
       signed_rat negative
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d)) \<le>
         exact_input_value negative n d"
  using round_rational_core_RTZ_directed[OF valid denominator,
      of negative n]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by (cases negative) simp_all

theorem round_rational_to_format_bits_RTZ_extremal_finite:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTZ negative n d) \<or>
         core_exponent (round_rational_core f RTZ negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat negative (finite_magnitude f b) \<longrightarrow>
       signed_rat negative
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d)) \<le>
         signed_rat negative (finite_magnitude f b)
     else
       signed_rat negative (finite_magnitude f b) \<le>
         exact_input_value negative n d \<longrightarrow>
       signed_rat negative (finite_magnitude f b) \<le>
         signed_rat negative
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d))"
  using round_rational_core_RTZ_extremal_finite[
      OF valid numerator denominator well_formed finite_exponent,
      of negative]
    round_rational_to_format_bits_finite_signed_value[
      OF valid numerator denominator no_overflow]
  by (cases negative) simp_all

theorem round_rational_to_format_bits_RTP_least_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTP negative n d) \<or>
         core_exponent (round_rational_core f RTP negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "exact_input_value negative n d \<le>
          signed_rat (negative_bit b) (finite_magnitude f b)"
  shows "signed_rat
      (negative_bit
        (round_rational_to_format_bits f RTP negative n d))
      (finite_magnitude f
        (round_rational_to_format_bits f RTP negative n d)) \<le>
    signed_rat (negative_bit b) (finite_magnitude f b)"
  using round_rational_core_RTP_least_finite_bits[
      OF valid numerator denominator well_formed finite_exponent competitor]
    round_rational_to_format_bits_finite_actual_signed_value[
      OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTN_greatest_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTN negative n d) \<or>
         core_exponent (round_rational_core f RTN negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
      and competitor:
        "signed_rat (negative_bit b) (finite_magnitude f b) \<le>
          exact_input_value negative n d"
  shows "signed_rat (negative_bit b) (finite_magnitude f b) \<le>
    signed_rat
      (negative_bit
        (round_rational_to_format_bits f RTN negative n d))
      (finite_magnitude f
        (round_rational_to_format_bits f RTN negative n d))"
  using round_rational_core_RTN_greatest_finite_bits[
      OF valid numerator denominator well_formed finite_exponent competitor]
    round_rational_to_format_bits_finite_actual_signed_value[
      OF valid numerator denominator no_overflow]
  by simp

theorem round_rational_to_format_bits_RTZ_extremal_finite_bits:
  assumes valid: "valid_format f"
      and numerator: "0 < n"
      and denominator: "0 < d"
      and no_overflow:
        "core_is_subnormal (round_rational_core f RTZ negative n d) \<or>
         core_exponent (round_rational_core f RTZ negative n d) \<le>
           format_emax f"
      and well_formed: "bits_well_formed f b"
      and finite_exponent: "exponent_field b < exponent_all_ones f"
  shows
    "if negative then
       exact_input_value negative n d \<le>
         signed_rat (negative_bit b) (finite_magnitude f b) \<longrightarrow>
       signed_rat
           (negative_bit
             (round_rational_to_format_bits f RTZ negative n d))
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d)) \<le>
         signed_rat (negative_bit b) (finite_magnitude f b)
     else
       signed_rat (negative_bit b) (finite_magnitude f b) \<le>
         exact_input_value negative n d \<longrightarrow>
       signed_rat (negative_bit b) (finite_magnitude f b) \<le>
         signed_rat
           (negative_bit
             (round_rational_to_format_bits f RTZ negative n d))
           (finite_magnitude f
             (round_rational_to_format_bits f RTZ negative n d))"
  using round_rational_core_RTZ_extremal_finite_bits[
      OF valid numerator denominator well_formed finite_exponent,
      of negative]
    round_rational_to_format_bits_finite_actual_signed_value[
      OF valid numerator denominator no_overflow]
  by (cases negative) simp_all

end

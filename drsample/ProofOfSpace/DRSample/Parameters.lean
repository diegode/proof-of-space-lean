import ProofOfSpace.DRSample.ParameterLimits

/-! # Rounding and the explicit conjecture constants -/
namespace ProofOfSpace.DRSample
open Filter

set_option maxHeartbeats 1000000 in
theorem finite_parameters_of_log_bounds {n : ℕ} (hn : 16 ≤ n)
    (hy : 1 ≤ Real.logb 2 (Real.logb 2 n))
    (hyx : Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n)
    (hsmall : 65536 * Real.logb 2 n ≤ (n : ℝ))
    (hroot : 24 * Real.logb 2 (Real.logb 2 n) ≤
      (Real.logb 2 n) ^ (1 / 32 : ℝ)) :
    12 ≤ blockWidth n ∧ blockWidth n ≤ n ∧ intervalWidth n ≤ blockWidth n ∧
    0 < intervalWidth n ∧ 2 * deletionBudget n ≤ (n / blockWidth n) / 3 ∧
    targetDepth n ≤ ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 18) *
      Real.exp (-(160 * blockWidth n * (Real.logb 2 n + 1) / (blockWidth n / 3 : ℕ) ^ 2)) ∧
    targetDepth n / 3300 ≤ (n / blockWidth n : ℕ) := by
  let x := Real.logb 2 n
  let y := Real.logb 2 x
  let m := blockWidth n
  change 1 ≤ y at hy
  change y ≤ x at hyx
  change 65536 * x ≤ (n : ℝ) at hsmall
  change 24 * y ≤ x ^ (1 / 32 : ℝ) at hroot
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ x := hy.trans hyx
  have hx0 : 0 < x := by linarith
  have hscale : (3072 : ℝ) ≤ 3072 * x / y := (le_div_iff₀ hy0).mpr (by nlinarith)
  have hlo : 3072 * x / y ≤ (m : ℝ) := Nat.le_ceil _
  have hhi : (m : ℝ) < 3072 * x / y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm12 : 12 ≤ m := by exact_mod_cast (show (12 : ℝ) ≤ m by linarith)
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmy : (m : ℝ) * y ≤ 3073 * x := by
    have hh := (lt_div_iff₀ hy0).mp (show (m : ℝ) - 1 < 3072 * x / y by linarith)
    nlinarith
  have hscaleupper : 3072 * x / y ≤ 3072 * x := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : 16 * m ≤ n := by
    exact_mod_cast (show (16 : ℝ) * m ≤ n by linarith)
  have hmle : m ≤ n := by omega
  have hquot : 16 ≤ n / m := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
  have hquotR : (16 : ℝ) ≤ (n / m : ℕ) := by exact_mod_cast hquot
  have hdivision : n < m * (n / m + 1) := by
    have hmod := Nat.mod_lt n hm0
    have heq := Nat.mod_add_div n m
    nlinarith
  have hdivisionR : (n : ℝ) < (m : ℝ) * ((n / m : ℕ) + 1) := by exact_mod_cast hdivision
  have hcomplete : (n : ℝ) ≤ (4 / 3 : ℝ) * m * (n / m : ℕ) := by nlinarith
  have hcomplete_sharp : (n : ℝ) ≤ (17 / 16 : ℝ) * m * (n / m : ℕ) := by nlinarith
  have hbudget : (deletionBudget n : ℝ) ≤ (n : ℝ) * y / (20000 * x) :=
    Nat.floor_le (by positivity)
  have hbudgetmul := (le_div_iff₀ (by positivity : 0 < 20000 * x)).mp hbudget
  have hny : (n : ℝ) * y ≤ 3300 * x * (n / m : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_right hcomplete_sharp hy0.le
    have h2 := mul_le_mul_of_nonneg_right hmy (Nat.cast_nonneg (n / m))
    nlinarith
  have he6 : 6 * deletionBudget n ≤ n / m := by
    have hR : (6 : ℝ) * deletionBudget n ≤ (n / m : ℕ) := by
      by_contra! hbad
      have hpos := mul_pos hx0 (sub_pos.mpr hbad)
      nlinarith
    exact_mod_cast hR
  have hcount : targetDepth n / 3300 ≤ (n / m : ℕ) := by
    change ((n : ℝ) * y / x) / 3300 ≤ (n / m : ℕ)
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < x * 3300)).mpr
    nlinarith
  have hb : intervalWidth n ≤ m := Nat.floor_le_ceil _
  have hbpos : 0 < intervalWidth n := by
    have hge : 1 ≤ intervalWidth n := by
      apply Nat.le_floor
      norm_num only [Nat.cast_one]
      change (1 : ℝ) ≤ 3072 * x / y
      linarith
    omega
  refine ⟨hm12, hmle, hb, hbpos, ?_, ?_, hcount⟩
  · change 2 * deletionBudget n ≤ (n / m) / 3
    omega
  have hpowpos : 0 < x ^ (31 / 32 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hpoweq : x ^ (1 / 32 : ℝ) / x = 1 / x ^ (31 / 32 : ℝ) := by
    rw [← Real.rpow_sub_one hx0.ne']
    norm_num
    rw [Real.rpow_neg hx0.le]
  have htarget : (n : ℝ) * y / x ≤ ((n : ℝ) / 24) * (1 / x ^ (31 / 32 : ℝ)) := by
    have hscaled := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg n)
    rw [← hpoweq]
    have hnum : (n : ℝ) * y ≤ (n : ℝ) * x ^ (1 / 32 : ℝ) / 24 := by nlinarith
    calc
      (n : ℝ) * y / x ≤ ((n : ℝ) * x ^ (1 / 32 : ℝ) / 24) / x :=
        (div_le_div_iff_of_pos_right hx0).mpr hnum
      _ = ((n : ℝ) / 24) * (x ^ (1 / 32 : ℝ) / x) := by ring
  have hm3072 : 3072 ≤ m := by exact_mod_cast (show (3072 : ℝ) ≤ m by linarith)
  have ht : 5 * m ≤ 16 * (m / 3) := by omega
  have htR : (5 : ℝ) * m ≤ 16 * (m / 3 : ℕ) := by exact_mod_cast ht
  have htpos : 0 < m / 3 := by omega
  have htsq : (25 : ℝ) * (m : ℝ) ^ 2 ≤ 256 * ((m / 3 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (16 * ((m / 3 : ℕ) : ℝ) - 5 * m)]
  have hx4 : 4 ≤ x := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).mpr
    norm_num
    exact_mod_cast hn
  have hcoef : 160 * m * (x + 1) / ((m / 3 : ℕ) : ℝ) ^ 2 ≤ 2048 * x / m := by
    apply (div_le_div_iff₀ (by positivity) hmR).mpr
    have hprod := mul_le_mul_of_nonneg_right htsq hx0.le
    have hprod2 := mul_le_mul_of_nonneg_left (show x + 1 ≤ 5 * x / 4 by linarith)
      (sq_nonneg (m : ℝ))
    nlinarith
  have hexponent : -(2 * y / 3) ≤
      -(160 * m * (x + 1) / ((m / 3 : ℕ) : ℝ) ^ 2) := by
    have hxm := (div_le_iff₀ hy0).mp hlo
    apply neg_le_neg
    apply hcoef.trans
    apply (div_le_div_iff₀ hmR (by norm_num : (0 : ℝ) < 3)).mpr
    nlinarith
  have hexp : 1 / x ^ (31 / 32 : ℝ) ≤ Real.exp (-(160 * m * (x + 1) / (m / 3 : ℕ) ^ 2)) :=
    (exp_neg_two_thirds_logb_ge_inv_rpow hx1).trans (Real.exp_le_exp.mpr hexponent)
  change (n : ℝ) * y / x ≤ ((m : ℝ) * (n / m : ℕ) / 18) * Real.exp (-(160 * m * (x + 1) / (m / 3 : ℕ) ^ 2))
  calc _ ≤ ((n : ℝ) / 24) * (1 / x ^ (31 / 32 : ℝ)) := htarget
    _ ≤ ((m : ℝ) * (n / m : ℕ) / 18) * Real.exp (-(160 * m * (x + 1) / (m / 3 : ℕ) ^ 2)) := by
      apply mul_le_mul (by nlinarith : (n : ℝ) / 24 ≤ (m : ℝ) * (n / m : ℕ) / 18) hexp
        (by positivity) (by positivity)

theorem eventually_parameters : ∀ᶠ n : ℕ in atTop,
    12 ≤ blockWidth n ∧ blockWidth n ≤ n ∧ intervalWidth n ≤ blockWidth n ∧
    0 < intervalWidth n ∧ 2 * deletionBudget n ≤ (n / blockWidth n) / 3 ∧
    targetDepth n ≤ ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 18) *
      Real.exp (-(160 * blockWidth n * (Real.logb 2 n + 1) / (blockWidth n / 3 : ℕ) ^ 2)) ∧
    targetDepth n / 3300 ≤ (n / blockWidth n : ℕ) := by
  filter_upwards [eventually_log_parameters] with n hn
  exact finite_parameters_of_log_bounds hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.ParameterLimits

/-! # Rounding and the explicit conjecture constants -/
namespace ProofOfSpace.DRSample
open Filter

theorem finite_parameters {n : ℕ} (hn : 8 ≤ n)
    (hy : 1 ≤ Real.logb 2 (Real.logb 2 n))
    (hyx : Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n)
    (hsmall : 65536 * Real.logb 2 n ≤ (n : ℝ))
    (hsqrt : 8 * Real.logb 2 (Real.logb 2 n) ≤ Real.sqrt (Real.logb 2 n)) :
    12 ≤ blockWidth n ∧ blockWidth n ≤ n ∧ intervalWidth n ≤ blockWidth n ∧
    0 < intervalWidth n ∧ 2 * deletionBudget n ≤ (n / blockWidth n) / 48 ∧
    targetDepth n ≤ ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 4) *
      Real.exp (-(8192 * Real.logb 2 n / (3 * blockWidth n))) ∧
    targetDepth n / 16384 ≤ (n / blockWidth n : ℕ) := by
  let x := Real.logb 2 n
  let y := Real.logb 2 x
  let m := blockWidth n
  change 1 ≤ y at hy
  change y ≤ x at hyx
  change 65536 * x ≤ (n : ℝ) at hsmall
  change 8 * y ≤ Real.sqrt x at hsqrt
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ x := hy.trans hyx
  have hx0 : 0 < x := by linarith
  have hscale : (8192 : ℝ) ≤ 8192 * x / y := (le_div_iff₀ hy0).mpr (by nlinarith)
  have hlo : 8192 * x / y ≤ (m : ℝ) := Nat.le_ceil _
  have hhi : (m : ℝ) < 8192 * x / y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm12 : 12 ≤ m := by exact_mod_cast (show (12 : ℝ) ≤ m by linarith)
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmy : (m : ℝ) * y ≤ 12288 * x := by
    have hh := (lt_div_iff₀ hy0).mp (show (m : ℝ) - 1 < 8192 * x / y by linarith)
    nlinarith
  have hscaleupper : 8192 * x / y ≤ 8192 * x := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : 4 * m ≤ n := by
    exact_mod_cast (show (4 : ℝ) * m ≤ n by linarith)
  have hmle : m ≤ n := by omega
  have hquot : 4 ≤ n / m := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
  have hquotR : (4 : ℝ) ≤ (n / m : ℕ) := by exact_mod_cast hquot
  have hdivision : n < m * (n / m + 1) := by
    have hmod := Nat.mod_lt n hm0
    have heq := Nat.mod_add_div n m
    nlinarith
  have hdivisionR : (n : ℝ) < (m : ℝ) * ((n / m : ℕ) + 1) := by exact_mod_cast hdivision
  have hcomplete : (n : ℝ) ≤ (4 / 3 : ℝ) * m * (n / m : ℕ) := by nlinarith
  have hbudget : (deletionBudget n : ℝ) ≤ (n : ℝ) * y / (1572864 * x) :=
    Nat.floor_le (by positivity)
  have hbudgetmul := (le_div_iff₀ (by positivity : 0 < 1572864 * x)).mp hbudget
  have hny : (n : ℝ) * y ≤ 16384 * x * (n / m : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_right hcomplete hy0.le
    have h2 := mul_le_mul_of_nonneg_right hmy (Nat.cast_nonneg (n / m))
    nlinarith
  have he96 : 96 * deletionBudget n ≤ n / m := by
    have hR : (96 : ℝ) * deletionBudget n ≤ (n / m : ℕ) := by
      by_contra! hbad
      have hpos := mul_pos hx0 (sub_pos.mpr hbad)
      nlinarith
    exact_mod_cast hR
  have hcount : targetDepth n / 16384 ≤ (n / m : ℕ) := by
    change ((n : ℝ) * y / x) / 16384 ≤ (n / m : ℕ)
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < x * 16384)).mpr
    nlinarith
  have hb : intervalWidth n ≤ m := Nat.floor_le_ceil _
  have hbpos : 0 < intervalWidth n := by
    have hge : 1 ≤ intervalWidth n := by
      apply Nat.le_floor
      norm_num only [Nat.cast_one]
      change (1 : ℝ) ≤ 8192 * x / y
      linarith
    omega
  refine ⟨hm12, hmle, hb, hbpos, ?_, ?_, hcount⟩
  · change 2 * deletionBudget n ≤ (n / m) / 48
    omega
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsqr : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  have htarget : (n : ℝ) * y / x ≤ ((n : ℝ) / 8) * (1 / Real.sqrt x) := by
    rw [div_mul_div_comm, mul_one]
    apply (div_le_div_iff₀ hx0 (by positivity)).mpr
    have hybound := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg x)
    have hscaled := mul_le_mul_of_nonneg_left hybound (Nat.cast_nonneg n)
    nlinarith
  have hexponent : -y / 3 ≤ -(8192 * x / (3 * m)) := by
    have hxm := (div_le_iff₀ hy0).mp hlo
    rw [neg_div]
    apply neg_le_neg
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * m) (by norm_num : (0 : ℝ) < 3)).mpr
    nlinarith
  have hexp : 1 / Real.sqrt x ≤ Real.exp (-(8192 * x / (3 * m))) :=
    (exp_neg_logb_third_ge_inv_sqrt hx1).trans (Real.exp_le_exp.mpr hexponent)
  change (n : ℝ) * y / x ≤ ((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * x / (3 * m)))
  calc _ ≤ ((n : ℝ) / 8) * (1 / Real.sqrt x) := htarget
    _ ≤ ((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * x / (3 * m))) := by
      apply mul_le_mul (by nlinarith : (n : ℝ) / 8 ≤ (m : ℝ) * (n / m : ℕ) / 4) hexp
        (by positivity) (by positivity)

theorem eventually_parameters : ∀ᶠ n : ℕ in atTop,
    12 ≤ blockWidth n ∧ blockWidth n ≤ n ∧ intervalWidth n ≤ blockWidth n ∧
    0 < intervalWidth n ∧ 2 * deletionBudget n ≤ (n / blockWidth n) / 48 ∧
    targetDepth n ≤ ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 4) *
      Real.exp (-(8192 * Real.logb 2 n / (3 * blockWidth n))) ∧
    targetDepth n / 16384 ≤ (n / blockWidth n : ℕ) := by
  filter_upwards [eventually_log_parameters] with n hn
  exact finite_parameters hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2

end ProofOfSpace.DRSample

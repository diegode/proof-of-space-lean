import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace ProofOfSpace.DRSample

/-- A tangent bound which also proves monotonicity of the exponential-to-linear ratio. -/
theorem exp_linear_lower {a t t₀ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (ha : 1 ≤ a * t₀) :
    t / t₀ * Real.exp (a * t₀) ≤ Real.exp (a * t) := by
  have hlin : t / t₀ ≤ a * (t - t₀) + 1 := by
    apply (div_le_iff₀ ht₀).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ht)]
  calc
    _ ≤ Real.exp (a * (t - t₀)) * Real.exp (a * t₀) :=
      mul_le_mul_of_nonneg_right (hlin.trans (Real.add_one_le_exp _)) (by positivity)
    _ = Real.exp (a * t) := by rw [← Real.exp_add]; congr 1; ring

theorem exp_nat_log_two (k : ℕ) :
    Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Rational bounds at the logarithmic base case `log₂ n = 120`. -/
theorem logb_120_bounds :
    (6 : ℝ) ≤ Real.logb 2 120 ∧ Real.logb 2 120 ≤ 691 / 100 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (6 : ℝ) ≤ Real.logb 2 120 := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hsmall := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
  norm_num at hsmall
  have hsum : Real.log (120 : ℝ) + Real.log (16 / 15 : ℝ) = 7 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    have h := Real.log_pow (2 : ℝ) 7
    norm_num at h
    exact h
  refine ⟨hlo, ?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ hl2).mpr
  linarith [Real.log_two_lt_d9]

theorem log_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    120 ≤ Real.logb 2 n ∧
    6 ≤ Real.logb 2 (Real.logb 2 n) ∧
    16 * Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n ∧
    3201000 * Real.logb 2 n ≤ (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : (120 : ℝ) ≤ Real.logb 2 n := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) hn0).mpr
    norm_cast
  have hx0 : 0 < Real.logb 2 n := by linarith
  let y₀ := Real.logb 2 120
  have hy₀ : (6 : ℝ) ≤ y₀ := logb_120_bounds.1
  have hy₀0 : 0 < y₀ := by linarith
  have hy : y₀ ≤ Real.logb 2 (Real.logb 2 n) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
  have hex (x : ℝ) (hx : 0 < x) : Real.exp (Real.log 2 * Real.logb 2 x) = x := by
    rw [Real.logb, mul_div_cancel₀ _ hl2.ne', Real.exp_log hx]
  have hxy := exp_linear_lower (a := Real.log 2) hy₀0 hy
    (by nlinarith [Real.log_two_gt_d9])
  rw [hex _ hx0, hex 120 (by norm_num)] at hxy
  have hprod := mul_le_mul_of_nonneg_right hxy hy₀0.le
  have hcancel := div_mul_cancel₀ (Real.logb 2 (Real.logb 2 n)) hy₀0.ne'
  have hupper := mul_le_mul_of_nonneg_left logb_120_bounds.2 hx0.le
  have hxn := exp_linear_lower (a := Real.log 2) (by norm_num : (0 : ℝ) < 120) hx
    (by linarith [Real.log_two_gt_d9])
  have h120 := exp_nat_log_two 120
  norm_num at h120
  rw [hex _ hn0, mul_comm (Real.log 2) 120, h120] at hxn
  exact ⟨hx, hy₀.trans hy, by dsimp [y₀] at *; nlinarith, by linarith⟩


end ProofOfSpace.DRSample

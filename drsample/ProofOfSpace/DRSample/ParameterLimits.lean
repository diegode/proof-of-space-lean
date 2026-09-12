import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # The explicit logarithmic parameters eventually satisfy the finite bounds -/
namespace ProofOfSpace.DRSample
open Filter

noncomputable def blockWidth (n : ℕ) : ℕ :=
  Nat.ceil (3200 * Real.logb 2 n / Real.logb 2 (Real.logb 2 n))

noncomputable def intervalWidth (n : ℕ) : ℕ :=
  Nat.floor (3200 * Real.logb 2 n / Real.logb 2 (Real.logb 2 n))

noncomputable def deletionBudget (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * Real.logb 2 (Real.logb 2 n) / (20000 * Real.logb 2 n))

/-- The logarithmic depth scale `n/L(n)`, before the final factor `1.01`. -/
noncomputable def targetDepth (n : ℕ) : ℝ :=
  n * Real.logb 2 (Real.logb 2 n) / Real.logb 2 n

theorem logb_eventually_le_rpow {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, C * Real.logb 2 x ≤ x ^ r := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (isLittleO_log_rpow_atTop hr).bound (div_pos hlog2 hC)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  have hmul := mul_le_mul_of_nonneg_left hx hC.le
  have hcancel : C * (Real.log 2 / C * x ^ r) = Real.log 2 * x ^ r := by field_simp
  rw [hcancel] at hmul
  unfold Real.logb
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hlog2).mpr (by nlinarith)

theorem eventually_log_parameters : ∀ᶠ n : ℕ in atTop,
    16 ≤ n ∧
    1 ≤ Real.logb 2 (Real.logb 2 n) ∧
    Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n ∧
    262144 * Real.logb 2 n ≤ (n : ℝ) ∧
    24 * Real.logb 2 (Real.logb 2 n) ≤ (Real.logb 2 n) ^ (1 / 32 : ℝ) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp hnat
  have hloglog : Tendsto (fun n : ℕ => Real.logb 2 (Real.logb 2 n)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp hlog
  have ha := hnat.eventually (logb_eventually_le_rpow (C := 262144) (r := 1) (by norm_num) (by norm_num))
  have hb := hlog.eventually (logb_eventually_le_rpow (C := 1) (r := 1) (by norm_num) (by norm_num))
  have hc := hlog.eventually (logb_eventually_le_rpow (C := 24) (r := 1 / 32) (by norm_num) (by norm_num))
  filter_upwards [eventually_ge_atTop 16, hloglog.eventually_ge_atTop 1, ha, hb, hc]
    with n hn hy ha hb hc
  exact ⟨hn, hy, by simpa using hb, by simpa using ha, by simpa using hc⟩

theorem exp_neg_logb_third_ge_inv_sqrt {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sqrt x ≤ Real.exp (-Real.logb 2 x / 3) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [one_div, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  unfold Real.logb
  have hl2 : 0 < Real.log 2 := by linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
  rw [← neg_div]
  apply (le_div_iff₀ hl2).mpr
  nlinarith

theorem exp_neg_two_thirds_logb_ge_inv_rpow {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ (31 / 32 : ℝ) ≤ Real.exp (-(2 * Real.logb 2 x / 3)) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : (64 / 93 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [one_div, Real.rpow_def_of_pos hx0, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  unfold Real.logb
  have hl2 : 0 < Real.log 2 := by linarith
  apply neg_le_neg
  have hcoef : 2 / (3 * Real.log 2) ≤ (31 / 32 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hlog
  convert hmul using 1 <;> ring

end ProofOfSpace.DRSample

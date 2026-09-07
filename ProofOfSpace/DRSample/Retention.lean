import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Harmonic retention weights

These elementary inequalities express the random-pivot estimate without
introducing an auxiliary probability space for binary search trees.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

noncomputable def retention (bad : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact Real.exp (-∑ k ∈ range N, if bad k then (1 : ℝ) / (k + 1) else 0)

@[simp] theorem retention_zero (bad : ℕ → Prop) : retention bad 0 = 1 := by
  simp [retention]

theorem retention_pos (bad : ℕ → Prop) (N : ℕ) : 0 < retention bad N :=
  Real.exp_pos _

theorem retention_le_one (bad : ℕ → Prop) (N : ℕ) : retention bad N ≤ 1 := by
  classical
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply sum_nonneg
  intro k _
  split_ifs <;> positivity

theorem retention_succ (bad : ℕ → Prop) (N : ℕ) :
    retention bad (N + 1) = retention bad N *
      Real.exp (if bad N then -(1 : ℝ) / (N + 1) else 0) := by
  classical
  unfold retention
  rw [sum_range_succ, neg_add, Real.exp_add]
  congr 2
  split_ifs <;> ring

private theorem exp_inverse_bound {x : ℝ} (hx : 0 < x) :
    (x + 1) * Real.exp (-1 / x) ≤ x := by
  have he := Real.add_one_le_exp (1 / x)
  have hmul := mul_le_mul_of_nonneg_left he hx.le
  have hxid : x * (1 / x) = 1 := by field_simp
  have haux : x + 1 ≤ x * Real.exp (1 / x) := by nlinarith
  calc (x + 1) * Real.exp (-1 / x) ≤
      (x * Real.exp (1 / x)) * Real.exp (-1 / x) :=
        mul_le_mul_of_nonneg_right haux (Real.exp_pos _).le
    _ = x := by
      rw [mul_assoc, ← Real.exp_add, show 1 / x + -1 / x = 0 by ring, Real.exp_zero, mul_one]

/-- Sum of retention weights at consistent pivots on one side. -/
theorem retention_sum_good (bad : ℕ → Prop) (N : ℕ) :
    (N + 1 : ℝ) * retention bad N - 1 ≤
      ∑ k ∈ range N, if bad k then 0 else retention bad k := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, retention_succ]
    by_cases hbad : bad N
    · rw [if_pos hbad, if_pos hbad, add_zero]
      have hstep := exp_inverse_bound (by positivity : (0 : ℝ) < N + 1)
      have hmul := mul_le_mul_of_nonneg_left hstep (retention_pos bad N).le
      push_cast
      nlinarith
    · rw [if_neg hbad, if_neg hbad, Real.exp_zero, mul_one]
      push_cast
      nlinarith

/-- The two one-sided sums combine into the binary-pivot recurrence. -/
theorem retention_pivot_bound (badLeft badRight : ℕ → Prop) (l r : ℕ) :
    (l + r + 1 : ℝ) * (retention badLeft l * retention badRight r) ≤
      1 + retention badRight r * (∑ k ∈ range l, if badLeft k then 0 else retention badLeft k) +
      retention badLeft l * (∑ k ∈ range r, if badRight k then 0 else retention badRight k) := by
  have hl := retention_sum_good badLeft l
  have hr := retention_sum_good badRight r
  have hl0 := (retention_pos badLeft l).le
  have hr0 := (retention_pos badRight r).le
  have hl1 := retention_le_one badLeft l
  have hr1 := retention_le_one badRight r
  have hleft := mul_le_mul_of_nonneg_left hl hr0
  have hright := mul_le_mul_of_nonneg_left hr hl0
  nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hr1)]

end ProofOfSpace.DRSample

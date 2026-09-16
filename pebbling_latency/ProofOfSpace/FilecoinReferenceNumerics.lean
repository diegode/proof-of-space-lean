/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungFilecoinCurve
import ProofOfSpace.Delay

/-! Exact rational certificates for the reference-trajectory Filecoin bound. -/

namespace ProofOfSpace.FilecoinReference
open ChungCurve Set

noncomputable def free (x : ℝ) : ℝ := filecoinBeta x - 189 / 5000
noncomputable def y (i : ℕ) : ℝ := free^[i] (5089 / 100000)

@[simp] theorem y_zero : y 0 = 5089 / 100000 := rfl

@[simp] theorem y_one : y 1 = 811 / 5000 := by
  change filecoinBeta (5089 / 100000) - 189 / 5000 = _
  rw [filecoinBeta_affine_0 (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem y_two : y 2 = 857 / 2000 := by
  have h : y 2 = free (y 1) := Function.iterate_succ_apply' _ _ _
  rw [h, y_one, free, filecoinBeta_affine_4 (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem y_three : y 3 = 3669 / 5000 := by
  have h : y 3 = free (y 2) := Function.iterate_succ_apply' _ _ _
  rw [h, y_two, free, filecoinBeta_affine_7 (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem y_four : y 4 = 4443 / 5000 := by
  have h : y 4 = free (y 3) := Function.iterate_succ_apply' _ _ _
  rw [h, y_three, free, filecoinBeta_affine_10 (by norm_num) (by norm_num)]
  norm_num

theorem first_crossing {p : ℝ} (hp : p ∈ Icc ((4 : ℝ) / 5) (8001 / 10000)) :
    (∀ i < 4, y i < p) ∧ p ≤ y 4 := by
  constructor
  · intro i hi
    interval_cases i <;> simp only [y_zero, y_one, y_two, y_three] <;> linarith [hp.1]
  · rw [y_four]; linarith [hp.2]

theorem scale_at_p {p : ℝ} (hp : p ∈ Icc ((4 : ℝ) / 5) (8001 / 10000)) :
    Delay.scale y 4 p = 3 + (p - 3669 / 5000) / (774 / 5000) := by
  norm_num only [Delay.scale, y_one, y_two, y_three, y_four, y_zero,
    show ¬p ≤ 811 / 5000 by linarith [hp.1],
    show ¬p ≤ 857 / 2000 by linarith [hp.1],
    show ¬p ≤ 3669 / 5000 by linarith [hp.1],
    show p ≤ 4443 / 5000 by linarith [hp.2], if_false, if_true]
  ring

theorem scale_at_source {σ : ℝ} (hs : σ ∈ Icc ((39 : ℝ) / 200) (1951 / 10000)) :
    Delay.scale y 4 σ = 1 + (σ - 811 / 5000) / (2663 / 10000) := by
  norm_num only [Delay.scale, y_one, y_two, y_zero,
    show ¬σ ≤ 811 / 5000 by linarith [hs.1],
    show σ ≤ 857 / 2000 by linarith [hs.2], if_false, if_true]

theorem delay_le {p σ : ℝ} (hp : p ∈ Icc ((4 : ℝ) / 5) (8001 / 10000))
    (hs : σ ∈ Icc ((39 : ℝ) / 200) (1951 / 10000)) :
    Delay.scale y 4 p - Delay.scale y 4 σ ≤ 231 / 100 := by
  rw [scale_at_p hp, scale_at_source hs]
  linarith [hp.2, hs.1]

theorem source_lower : (4806 : ℝ) / 10000 ≤ free (39 / 200) := by
  rw [free, filecoinBeta_affine_4 (by norm_num) (by norm_num)]
  norm_num

theorem floor_gain : (11131 : ℝ) / 100000 ≤ free (5089 / 100000) - 5089 / 100000 := by
  have h := y_one
  change free (5089 / 100000) = 811 / 5000 at h
  rw [h]; norm_num

end ProofOfSpace.FilecoinReference

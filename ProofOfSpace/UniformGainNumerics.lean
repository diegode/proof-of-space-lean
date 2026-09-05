/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungFilecoinCurve
import ProofOfSpace.UniformGain

/-! Exact rational expansion estimates for the 18-layer Filecoin corollary. -/

namespace ProofOfSpace.UniformGain

open ChungCurve Set

/-- An affine function is convex on any convex set. -/
private theorem convexOn_add_const {s : Set ℝ} (hs : Convex ℝ s) (c : ℝ) :
    ConvexOn ℝ s (fun x => x + c) := by
  refine ⟨hs, ?_⟩
  intro x _ y _ a b ha hb hab
  have : a • (x + c) + b • (y + c) = (a • x + b • y) + c := by
    simp only [smul_eq_mul]; linear_combination c * hab
  exact le_of_eq this.symm


/-- The gain at `m/n` is the minimum throughout the Filecoin query interval. -/
theorem filecoin_gain_at_threshold {x y : ℝ}
    (hy : y ∈ Icc ((4 : ℝ) / 5) (8001 / 10000))
    (hx : x ∈ Icc ((311 : ℝ) / 5000) y) :
    filecoinBeta y - 189 / 5000 - y ≤ filecoinBeta x - 189 / 5000 - x := by
  have hlo : (311 : ℝ) / 5000 ∈ Icc 0 1 := by norm_num
  have hhi : y ∈ Icc 0 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun x => filecoinBeta x - (x + 189 / 5000)) :=
    filecoinBeta_concaveOn.sub
      (convexOn_add_const (convex_Icc 0 1) (189 / 5000))
  have hmin := hconc.min_le_of_mem_Icc hlo hhi hx
  have hl := filecoinBeta_affine_1
    (x := (311 : ℝ) / 5000) (by norm_num) (by norm_num)
  have hh := filecoinBeta_affine_11 hy.1 hhi.2
  rw [hl, hh] at hmin
  rw [hh]
  rw [min_eq_right (by linarith [hy.1])] at hmin
  linarith

theorem filecoin_source_0195 :
    (4806 : ℝ) / 10000 ≤ filecoinBeta (39 / 200) - 189 / 5000 := by
  rw [filecoinBeta_affine_4 (by norm_num) (by norm_num)]
  norm_num

end ProofOfSpace.UniformGain

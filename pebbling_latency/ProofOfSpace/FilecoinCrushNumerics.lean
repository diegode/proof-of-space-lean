/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.CrushAllowance
import ProofOfSpace.FilecoinReferenceNumerics

/-! # Exact Filecoin crush optimization for the certified rational profile

These are unrounded cost-model densities: `σ = απ = 1/5`. The entropy-defined
Chung curve gives a different, numerically evaluated allowance. No cost-model
graph theorem or improvement of the registered latency theorem is asserted.
-/

namespace ProofOfSpace.FilecoinCrush
open Crush

noncomputable def g : ℝ := 11131 / 100000
noncomputable def K : ℝ := FilecoinReference.free (1 / 5) - 5089 / 100000 - 2 * g
noncomputable def τ (x : ℝ) : ℝ :=
  Delay.scale FilecoinReference.y 4 (4 / 5) - Delay.scale FilecoinReference.y 4 x
noncomputable def A (B : ℝ) : ℝ := allowance τ (4 / 5) K g B
noncomputable def c₁ : ℝ := 1 - (9 / 10 - 189 / 5000 - 4 / 5) / g
noncomputable def cfrMax : ℝ := max (A (4 / 5)) (c₁ + A (4 / 5 - (1 - c₁) * g))

theorem K_eq : K = 7118449 / 33100000 := by
  rw [K, FilecoinReference.free, ChungCurve.filecoinBeta_affine_4 (by norm_num) (by norm_num)]
  norm_num [g]

theorem gain_eq : ChungCurve.filecoinBeta (4 / 5) - 189 / 5000 - 4 / 5 = g := by
  rw [ChungCurve.filecoinBeta_affine_11 (by norm_num) (by norm_num)]
  norm_num [g]

theorem worth_one : worth τ (4 / 5) K g 1 = -1860013853 / 2851695414 := by
  norm_num [worth, τ, K_eq, g, Delay.scale, FilecoinReference.y_zero,
    FilecoinReference.y_one, FilecoinReference.y_two, FilecoinReference.y_three,
    FilecoinReference.y_four]

theorem worth_two : worth τ (4 / 5) K g 2 = -4858501214239 / 18985162218705 := by
  norm_num [worth, τ, K_eq, g, Delay.scale, FilecoinReference.y_zero,
    FilecoinReference.y_one, FilecoinReference.y_two, FilecoinReference.y_three,
    FilecoinReference.y_four]

theorem worth_three : worth τ (4 / 5) K g 3 = 6154108398139 / 37970324437410 := by
  norm_num [worth, τ, K_eq, g, Delay.scale, FilecoinReference.y_zero,
    FilecoinReference.y_one, FilecoinReference.y_two, FilecoinReference.y_three,
    FilecoinReference.y_four]

theorem worth_four : worth τ (4 / 5) K g 4 = 6011005 / 8615394 := by
  norm_num [worth, τ, K_eq, g, Delay.scale, FilecoinReference.y_zero,
    FilecoinReference.y_one, FilecoinReference.y_two, FilecoinReference.y_three,
    FilecoinReference.y_four]

theorem admissible_cases {B : ℝ} (hB : B ≤ 4 / 5) {ms : List ℕ}
    (h : Admissible K g B ms) :
    ms = [] ∨ ∃ m, ms = [m] ∧ 1 ≤ m ∧ m ≤ 4 ∧ cost K g m < B := by
  have hcap : B ≤ 2 * (K + 2 * g) := by rw [K_eq]; norm_num [g] at *; linarith
  rcases at_most_one (by rw [K_eq]; norm_num) (by norm_num [g]) hcap h with he | ⟨m, he, hm, hc⟩
  · exact Or.inl he
  · right
    refine ⟨m, he, hm, ?_, hc⟩
    have hmreal : (m : ℝ) < 5 := by rw [cost, K_eq] at hc; norm_num [g] at hc; linarith
    have : m < 5 := by exact_mod_cast hmreal
    omega

theorem credit_le_four {ms : List ℕ} (h : Admissible K g (4 / 5) ms) :
    credit τ (4 / 5) K g ms ≤ 6011005 / 8615394 := by
  rcases admissible_cases le_rfl h with rfl | ⟨m, rfl, hm, htop, _⟩
  · norm_num [credit]
  · simp only [credit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    interval_cases m <;> norm_num [worth_one, worth_two, worth_three, worth_four]

theorem credit_le_three {ms : List ℕ} (h : Admissible K g (3689 / 5000) ms) :
    credit τ (4 / 5) K g ms ≤ 6154108398139 / 37970324437410 := by
  rcases admissible_cases (by norm_num : (3689 : ℝ) / 5000 ≤ 4 / 5) h with
    rfl | ⟨m, rfl, hm, _, hc⟩
  · norm_num [credit]
  · have hmreal : (m : ℝ) < 4 := by rw [cost, K_eq] at hc; norm_num [g] at hc; linarith
    have htop : m ≤ 3 := by
      have : m < 4 := by exact_mod_cast hmreal
      omega
    simp only [credit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    interval_cases m <;> norm_num [worth_one, worth_two, worth_three]

theorem allowance_rho : A (4 / 5) = 6011005 / 8615394 := by
  have hmax := allowance_isGreatest (K := K) (g := g) (by rw [K_eq]; norm_num)
    (by norm_num [g]) (by norm_num : (0 : ℝ) ≤ 4 / 5) τ (4 / 5)
  apply le_antisymm
  · obtain ⟨ms, hm, he⟩ := hmax.1
    change allowance τ (4 / 5) K g (4 / 5) ≤ _
    rw [← he]
    exact credit_le_four hm
  · have h : Admissible K g (4 / 5) [4] := by
      norm_num [Admissible, spending, cost, K_eq, g]
    have hh := credit_le_allowance (by rw [K_eq]; norm_num)
      (by norm_num [g]) (by norm_num : (0 : ℝ) ≤ 4 / 5) τ (4 / 5) h
    simpa only [A, credit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, worth_four] using hh

theorem allowance_remaining : A (3689 / 5000) = 6154108398139 / 37970324437410 := by
  have hmax := allowance_isGreatest (K := K) (g := g) (by rw [K_eq]; norm_num)
    (by norm_num [g]) (by norm_num : (0 : ℝ) ≤ 3689 / 5000) τ (4 / 5)
  apply le_antisymm
  · obtain ⟨ms, hm, he⟩ := hmax.1
    change allowance τ (4 / 5) K g (3689 / 5000) ≤ _
    rw [← he]
    exact credit_le_three hm
  · have h : Admissible K g (3689 / 5000) [3] := by
      norm_num [Admissible, spending, cost, K_eq, g]
    have hh := credit_le_allowance (by rw [K_eq]; norm_num)
      (by norm_num [g]) (by norm_num : (0 : ℝ) ≤ 3689 / 5000) τ (4 / 5) h
    simpa only [A, credit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, worth_three] using hh

/-- The exact maximum in the cost section for the certified rational profile. -/
theorem cfrMax_eq : cfrMax = 6011005 / 8615394 := by
  have hb : (4 : ℝ) / 5 - (1 - c₁) * g = 3689 / 5000 := by norm_num [c₁, g]
  rw [cfrMax, hb, allowance_rho, allowance_remaining]
  norm_num [c₁, g]

theorem bMax_eq : ⌈cfrMax + (4 / 5) / g⌉₊ = 8 := by
  rw [cfrMax_eq]
  apply (Nat.ceil_eq_iff (by norm_num)).mpr
  norm_num [g]

end ProofOfSpace.FilecoinCrush

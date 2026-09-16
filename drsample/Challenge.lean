import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-! # DRSample block depth robustness

This Mathlib-only challenge contains the main theorem and the definitions
needed to state it. Its proof and the remaining paper results are exposed
through `Solution`. See README.md for the full paper inventory.
-/
namespace ProofOfSpaceStatement
open Finset Filter

def drsampleBucket (v k : ℕ) : Finset (Fin (v + 1)) :=
  univ.filter fun r => max 2 ((min v (2 ^ k) + 1) / 2) ≤ r.val ∧
    r.val ≤ min v (2 ^ k)

noncomputable def drsampleParentProbability {n : ℕ} (v u : Fin n) : ℝ := by
  classical
  exact if 2 ≤ v.val then
    ∑ k : Fin (Nat.clog 2 (v.val + 1)),
      ((1 : ℝ) / (Nat.clog 2 (v.val + 1) : ℕ)) *
        ∑ r ∈ drsampleBucket v.val (k.val + 1),
          if v.val - r.val = u.val then
            (1 : ℝ) / (drsampleBucket v.val (k.val + 1)).card else 0
  else if u.val = 0 then 1 else 0

noncomputable def drsampleProbability (n : ℕ) (event : (Fin n → Fin n) → Prop) : ℝ := by
  classical
  exact ∑ parents : Fin n → Fin n,
    if event parents then ∏ v : Fin n, drsampleParentProbability v (parents v) else 0

/-- The ordered DRSample graph: the predecessor and the chosen random parent. -/
def drsampleEdge {n : ℕ} (parents : Fin n → Fin n) (u v : Fin n) : Prop :=
  u < v ∧ (u.val + 1 = v.val ∨ parents v = u)

def DRSampleBlockDepthRobust {n : ℕ} (parents : Fin n → Fin n)
    (e : ℕ) (d : ℝ) (b : ℕ) : Prop :=
  ∀ endpoints : Finset (Fin n), endpoints.card ≤ e →
    ∃ path : List (Fin n), path ≠ [] ∧ path.IsChain (drsampleEdge parents) ∧
      (∀ u ∈ path, ∀ v ∈ endpoints, ¬ (u ≤ v ∧ v.val < u.val + b)) ∧
      d ≤ (path.length : ℝ)

/-- Paper result `thm:dr-conjecture2`. -/
theorem drsample_conjecture2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e b : ℕ,
          c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          c * (L / ε) ≤ b ∧ (b : ℝ) ≤ C * (L / ε) ∧
          drsampleProbability n (fun parents => DRSampleBlockDepthRobust parents
            e (c * n / (Real.logb 2 n) ^ ε) b) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  sorry

end ProofOfSpaceStatement

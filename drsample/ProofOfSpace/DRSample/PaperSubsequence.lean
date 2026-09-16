import ProofOfSpace.DRSample.PaperDefinitions
import ProofOfSpace.DRSample.HarmonicSubsequence

namespace ProofOfSpaceStatement
open Finset ProofOfSpace.DRSample

/-- Lemma `lem:dr-subsequence`: a strictly increasing subsequence within any
chosen index set, with the paper's exponential reciprocal-distance bound. -/
theorem dr_subsequence {n : ℕ} (_hn : 1 ≤ n) (a : ℕ → ℤ)
    (T : Finset ℕ) (hT : T ⊆ range n) :
    ∃ I ⊆ T, (∀ i ∈ I, ∀ j ∈ I, i < j → a i < a j) ∧
      (∑ j ∈ T, Real.exp (-comparisonCost a n j)) ≤ (I.card : ℝ) := by
  obtain ⟨I, hIT, hI, hcard⟩ := increasingCapacity_witness (fun i => (a i : ℝ)) T
  refine ⟨I, hIT, ?_, ?_⟩
  · intro i hi j hj hij
    have hlt : (a i : ℝ) < (a j : ℝ) := hI i hi j hj hij
    exact_mod_cast hlt
  · rw [hcard]
    have h := sum_exp_inconsistentCost_le_capacity (fun i => (a i : ℝ)) 0 n T
      (by simpa using hT)
    simpa [comparisonCost, inconsistentCost] using h

end ProofOfSpaceStatement

import ProofOfSpace.DRSample.GeneralLabels
import ProofOfSpace.DRSample.Multiscale
import ProofOfSpace.DRSample.SampleMap

namespace ProofOfSpace.DRSample
open Finset

/-- Graph specialization of the multiscale bound at any fixed deletion fraction. -/
theorem multiscale_fraction {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, 0 < M →
      ∀ p : ℕ → FiniteLaw (Finset (Fin M)), ∀ lambda : ℝ, 0 < lambda →
      (∀ j < M, ∀ A : Finset (Fin M),
        (p j).probability (fun parents => Disjoint parents A) ≤
          Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) →
      (independentSamples p M).probability (fun s =>
        DepthRobust (exposedGraph M s) (Nat.floor (α * M))
          ((M : ℝ) / c * Real.exp (-c / lambda))) ≥
        1 - Real.exp (-(2 - Real.log 3) * M) := by
  obtain ⟨c, hc, hlabels⟩ := shallow_labels_fraction hα hα1
  refine ⟨4 * c, by positivity, ?_⟩
  intro M hM p lambda hlambda havoid
  have hmass := (independentSamples p M).uniform_mass_bound M lambda hlambda actualMass
    (actualMass_moment p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  have hsmall : ((natDeleted S).card : ℝ) ≤ α * M := by
    rw [natDeleted_card]
    exact (Nat.cast_le.mpr hS).trans (Nat.floor_le (by positivity))
  have hh : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := hlabels M (labelDepth S s) hM (natDeleted S)
    (natDeleted_subset S) hsmall (exposedLabels (natDeleted S) M s) hh
  apply path_of_le_labelDepth S s (by positivity)
  apply le_trans ?_ hshallow
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hexp : -(4 * c) / lambda ≤ -c * actualMass S s / M := by
    apply (div_le_div_iff₀ hlambda hM0).mpr
    have hb := (le_div_iff₀ hlambda).mp (hs S)
    nlinarith [mul_le_mul_of_nonneg_left hb hc.le]
  apply mul_le_mul _ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  apply div_le_div_of_nonneg_left hM0.le hc
  linarith

end ProofOfSpace.DRSample

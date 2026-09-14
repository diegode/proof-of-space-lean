import ProofOfSpace.DRSample.ExplicitParameters

namespace ProofOfSpaceStatement
open ProofOfSpace.DRSample

/-- Ordinary-path specialization of the revised multiscale height theorem. -/
theorem drsample_multiscale {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-48 / lambda))) ≥
      1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) :=
  multiscale_sharp hM p hlambda havoid

end ProofOfSpaceStatement

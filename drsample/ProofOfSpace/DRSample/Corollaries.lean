import ProofOfSpace.DRSample.ExplicitParameters

namespace ProofOfSpaceStatement

open ProofOfSpace.DRSample Filter

theorem drsample_multiscale {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 3)
        ((M / 6 : ℝ) * Real.exp (-160 / lambda))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  exact ProofOfSpace.DRSample.multiscale_third hM p hlambda havoid

theorem drsample_conjecture1 {n : ℕ} (hn : 2 ^ 128 ≤ n) :
    (drsampleLaw n (blockWidth n)).probability (fun s =>
      DepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n)) ≥ 1 - failureBound n := by
  exact ProofOfSpace.DRSample.drsample_conjecture1 hn

theorem filecoin_bucket6_finite {n m : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n) :
    (graphLaw m (filecoinIncomingLaw (by omega))).probability (fun s =>
      IndegreeAtMost (rowGraph (by omega) (n / m + 1) s) 6 ∧
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) ((n / m) / 6)
        (((m : ℝ) * (n / m : ℕ) / 18) * Real.exp (-(160 * m * (Real.logb 2 n + 1) / (m / 3 : ℕ) ^ 2))) m) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * (n / m : ℕ)) := by
  exact ProofOfSpace.DRSample.filecoin_bucket6_finite_sharp_with_degree hm hmn

theorem filecoin_bucket6_depth_robustness {n : ℕ} (hn : 2 ^ 128 ≤ n) :
    (filecoinBucket6Law n (blockWidth n)).probability (fun s =>
      IndegreeAtMost (sampledGraph n (blockWidth n) s) 6 ∧
      BlockDepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n) (intervalWidth n) ∧
      DepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n)) ≥ 1 - failureBound n := by
  exact ProofOfSpace.DRSample.filecoin_bucket6 hn

theorem drsample_failure_tends_to_zero : Tendsto failureBound atTop (nhds 0) := by
  exact ProofOfSpace.DRSample.failureBound_tendsto_zero

end ProofOfSpaceStatement

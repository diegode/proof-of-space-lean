import ProofOfSpace.DRSample.ExplicitParameters

namespace ProofOfSpaceStatement

/-- DRSample: Theorem `thm:dr-conjecture2` of the paper.
The depth counts vertices and the endpoint set may depend on the sampled graph. -/
theorem drsample_conjecture2 {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
    drsampleProbability n (fun parents => DRSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) / (18000 * L)))
      ((37 / 25 : ℝ) * n / L)
      (Nat.floor (3600 * L))) ≥
    1 - Real.exp (-(n : ℝ) / (11000 * L)) := by
  simpa only [ProofOfSpace.DRSample.paperBudget, ProofOfSpace.DRSample.paperWidth,
    ProofOfSpace.DRSample.paperFailure, ProofOfSpace.DRSample.paperScale] using
    ProofOfSpace.DRSample.paper_drsample hn

/-- BucketSample for every `r ≥ 1`: Theorem `thm:bucket-optimal`.
The depth counts vertices and the endpoint set may depend on the sampled graph. -/
theorem bucketSample_block_robustness {n r : ℕ} (hn : 2 ^ 120 ≤ n) (hr : 1 ≤ r) :
    let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
    bucketSampleProbability n r (fun parents => MultiSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) / (18000 * L)))
      ((37 / 25 : ℝ) * n / L)
      (Nat.floor (3600 * L))) ≥
    1 - Real.exp (-(n : ℝ) / (11000 * L)) := by
  simpa only [ProofOfSpace.DRSample.paperBudget, ProofOfSpace.DRSample.paperWidth,
    ProofOfSpace.DRSample.paperFailure, ProofOfSpace.DRSample.paperScale] using
    ProofOfSpace.DRSample.paper_bucketSample hn hr

/-- HarmonicSample for every `r ≥ 1`: Theorem `thm:harmonic-block-robustness`.
The depth counts vertices and the endpoint set may depend on the sampled graph. -/
theorem harmonicSample_block_robustness {n r : ℕ} (hn : 2 ^ 120 ≤ n) (hr : 1 ≤ r) :
    let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
    harmonicSampleProbability n r (fun parents => MultiSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) / (18000 * L)))
      ((2 : ℝ) * n / L)
      (Nat.floor (3600 * L))) ≥
    1 - Real.exp (-(n : ℝ) / (11000 * L)) := by
  simpa only [ProofOfSpace.DRSample.paperBudget, ProofOfSpace.DRSample.paperWidth,
    ProofOfSpace.DRSample.paperFailure, ProofOfSpace.DRSample.paperScale] using
    ProofOfSpace.DRSample.paper_harmonicSample hn hr

end ProofOfSpaceStatement

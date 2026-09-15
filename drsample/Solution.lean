import ProofOfSpace.DRSample.PaperRobustness

/-! # Sampler results proved in the paper

DRSample is the sole Challenge theorem. BucketSample is the paper's corollary
for every positive number of draws. Both follow from the same avoidance lemma.
-/

namespace ProofOfSpaceStatement
open ProofOfSpace.DRSample

/-- DRSample: Theorem `thm:dr-conjecture2` of the paper.
The depth counts vertices and the endpoint set may depend on the sampled graph. -/
theorem drsample_conjecture2 {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
    drsampleProbability n (fun parents => DRSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) / (18000 * L)))
      ((37 / 25 : ℝ) * n / L)
      (Nat.floor (3600 * L))) ≥
    1 - Real.exp (-(n : ℝ) / (11000 * L)) := by
  have hn0 : 0 < n := by omega
  have h := concrete_avoidance_criterion hn (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp_rw [drIncomingLaw_as_map] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  simp_rw [incomingGraph_block_statement] at h
  rw [← drsampleProbability_eq hn0] at h
  exact h

/-- BucketSample for every `r ≥ 1`: Corollary `cor:bucket-optimal` of the paper.
The depth counts vertices and the endpoint set may depend on the sampled graph. -/
theorem bucketSample_block_robustness {n r : ℕ} (hn : 2 ^ 120 ≤ n) (hr : 1 ≤ r) :
    let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
    bucketSampleProbability n r (fun parents => MultiSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) / (18000 * L)))
      ((37 / 25 : ℝ) * n / L)
      (Nat.floor (3600 * L))) ≥
    1 - Real.exp (-(n : ℝ) / (11000 * L)) := by
  have hn0 : 0 < n := by omega
  have hr0 : 0 < r := by omega
  have h := concrete_avoidance_criterion hn (bucketIncomingLaw hn0 hr0)
    (fun _ hv A => bucketIncomingLaw_avoidance_sharp (by omega) hr0 hv A)
  simp only [bucketIncomingLaw] at h
  rw [parentSetLaw_block_probability] at h
  rw [← bucketSampleProbability_eq hn0 hr0] at h
  exact h

end ProofOfSpaceStatement

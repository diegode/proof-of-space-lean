import ProofOfSpace.DRSample.ConditionalLabels
import ProofOfSpace.DRSample.PaperOptimality
import ProofOfSpace.DRSample.AsymptoticRobustness
import ProofOfSpace.DRSample.PaperAvoidance
import ProofOfSpace.DRSample.PaperSubsequence
import ProofOfSpace.DRSample.GeneralLabels
import ProofOfSpace.DRSample.PaperFractional

/-! # Sampler results in the current paper

The DRSample theorem and BucketSample corollary hold for every fixed exponent
`0 < ε < 1`, with deletion budget `Θ(ε n / L(n))`, depth
`Ω(n / (log₂ n)^ε)`, block width `Θ(L(n) / ε)`, and failure probability
`exp(-Ω(ε n / L(n)))`. Positive constants explicitly witness these orders.

The imports also prove `sampler_avoidance`, `dr_subsequence`, `dr_labels`,
`block_to_fractional`, and fractional robustness for both samplers.
The imports also prove Valiant depth reduction, balanced optimality, and the
general conditional-label multiscale theorem. No unproved result is assumed.
-/

namespace ProofOfSpaceStatement
open ProofOfSpace.DRSample Filter

/-- DRSample: Theorem `thm:dr-conjecture2` of the current paper.
The constants are uniform in `ε`; the threshold on `n` may depend on it. -/
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
  refine ⟨1 / 200000, 2000, by norm_num, by norm_num, ?_⟩
  intro ε hε hε1
  filter_upwards [eventually_avoidance_robustness hε hε1] with n hn
  obtain ⟨hn, e, b, heLo, heHi, hbLo, hbHi, hrobust⟩ := hn
  refine ⟨e, b, heLo, heHi, hbLo, hbHi, ?_⟩
  have hn0 : 0 < n := by omega
  have h := hrobust (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp_rw [drIncomingLaw_as_map] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  simp_rw [incomingGraph_block_statement] at h
  rw [← drsampleProbability_eq hn0] at h
  exact h

/-- BucketSample: Corollary `cor:bucket-optimal` of the current paper.
The same constants work for every positive number of independent draws. -/
theorem bucketSample_block_robustness :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ, 1 ≤ r → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e b : ℕ,
          c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          c * (L / ε) ≤ b ∧ (b : ℝ) ≤ C * (L / ε) ∧
          bucketSampleProbability n r (fun parents => MultiSampleBlockDepthRobust parents
            e (c * n / (Real.logb 2 n) ^ ε) b) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  refine ⟨1 / 200000, 2000, by norm_num, by norm_num, ?_⟩
  intro ε hε hε1 r hr
  filter_upwards [eventually_avoidance_robustness hε hε1] with n hn
  obtain ⟨hn, e, b, heLo, heHi, hbLo, hbHi, hrobust⟩ := hn
  refine ⟨e, b, heLo, heHi, hbLo, hbHi, ?_⟩
  have hn0 : 0 < n := by omega
  have hr0 : 0 < r := by omega
  have h := hrobust (bucketIncomingLaw hn0 hr0)
    (fun _ hv A => bucketIncomingLaw_avoidance_sharp (by omega) hr0 hv A)
  simp only [bucketIncomingLaw] at h
  rw [parentSetLaw_block_probability] at h
  rw [← bucketSampleProbability_eq hn0 hr0] at h
  exact h

end ProofOfSpaceStatement

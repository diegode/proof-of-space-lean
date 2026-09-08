import ProofOfSpace.DRSample.Registry

namespace ProofOfSpaceStatement
open Finset Filter

/-- Conjecture 2 of Blocki et al. (CRYPTO 2019, Appendix F), with
`c₁ = 1/20000`, `c₂ = 1`, and `c₃ = 3072`. All logarithms in the parameters
have base two. The explicit failure bound tends to zero as `n → ∞`. -/
theorem drsample_conjecture2 : ∀ᶠ n : ℕ in atTop,
    drsampleProbability n (fun parents => DRSampleBlockDepthRobust parents
      (Nat.floor ((n : ℝ) * Real.logb 2 (Real.logb 2 n) / (20000 * Real.logb 2 n)))
      ((n : ℝ) * Real.logb 2 (Real.logb 2 n) / Real.logb 2 n)
      (Nat.floor (3072 * Real.logb 2 n / Real.logb 2 (Real.logb 2 n)))) ≥
    1 - Real.exp (-(((4 / 3 : ℝ) - Real.log 3) / 3300) *
      ((n : ℝ) * Real.logb 2 (Real.logb 2 n) / Real.logb 2 n)) := by
  exact ProofOfSpace.DRSample.registry_conjecture2

end ProofOfSpaceStatement

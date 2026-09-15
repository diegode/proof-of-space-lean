import ProofOfSpace.DRSample.PaperParameters
import ProofOfSpace.DRSample.MultiSamplerRegistry

/-! # The paper's concrete avoidance lemma

This is Lemma `lem:concrete-avoidance`. The exact sampler applications are
proved in `Solution.lean`.
-/
namespace ProofOfSpace.DRSample
open Finset

/-- Independent incoming-edge sets satisfying the paper's reciprocal-distance
avoidance bound give its concrete block depth-robustness parameters. -/
theorem concrete_avoidance_criterion {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      BlockDepthRobust (incomingGraph sets) (paperBudget n)
        ((37 / 25 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hp := paper_integer_parameters hn
  have hx := (log_parameters hn).1
  have hfinite := finite_avoidance_robustness (paper_block_bounds hn).1 hp.1 p
    (by positivity : 0 < 1 / (Real.logb 2 n + 1)) havoid
  have hfailure := paper_failure_parameters hn
  have hbound := (show 1 - paperFailure n ≤
      1 - ((20 * paperBlockUnit n : ℕ) : ℝ) *
        Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / (20 * paperBlockUnit n) - 2)) by
    linarith).trans hfinite
  apply hbound.trans
  apply FiniteLaw.probability_mono
  intro sets hs
  exact (hs (paperBudget n) (paperWidth n) hp.2.1 hp.2.2).mono le_rfl
    (paper_depth_parameters hn)

end ProofOfSpace.DRSample

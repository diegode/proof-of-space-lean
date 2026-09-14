import ProofOfSpace.DRSample.PaperParameters
import ProofOfSpace.DRSample.MultiSamplerRegistry

namespace ProofOfSpace.DRSample
open Finset Classical

theorem concrete_avoidance_of_depth {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta d : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u))
    (hd : d ≤ (9 / 40 : ℝ) * ((n : ℝ) - 2 * (20 * paperBlockUnit n)) *
      Real.exp (-323 / (eta * (20 * paperBlockUnit n)))) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      BlockDepthRobust (incomingGraph sets) (paperBudget n) d (paperWidth n)) ≥ 1 - paperFailure n := by
  have hp := paper_integer_parameters hn
  have hfinite := finite_avoidance_robustness (paper_block_bounds hn).1 hp.1 p heta havoid
  have hfailure := paper_failure_parameters hn
  have hbound := (show 1 - paperFailure n ≤
      1 - ((20 * paperBlockUnit n : ℕ) : ℝ) *
        Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / (20 * paperBlockUnit n) - 2)) by
    linarith).trans hfinite
  apply hbound.trans
  apply FiniteLaw.probability_mono
  intro sets hs
  exact (hs (paperBudget n) (paperWidth n) hp.2.1 hp.2.2).mono le_rfl hd

theorem concrete_avoidance_dr {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      BlockDepthRobust (incomingGraph sets) (paperBudget n)
        ((37 / 25 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hx := (log_parameters hn).1
  exact concrete_avoidance_of_depth hn p (by positivity) havoid (paper_depth_parameters hn).1

theorem concrete_avoidance_harmonic {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-(1 / Real.log n) * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      BlockDepthRobust (incomingGraph sets) (paperBudget n)
        ((2 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact concrete_avoidance_of_depth hn p (by positivity) havoid (paper_depth_parameters hn).2

/-- The common avoidance criterion, including its two depth branches. -/
theorem concrete_avoidance_criterion {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta : ℝ}
    (hbase : 1 / (Real.logb 2 n + 1) ≤ eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      BlockDepthRobust (incomingGraph sets) (paperBudget n)
        ((if 1 / Real.log n ≤ eta then (2 : ℝ) else 37 / 25) * n / paperScale n)
        (paperWidth n)) ≥ 1 - paperFailure n := by
  have hweak (c : ℝ) (hc : c ≤ eta) (v : ℕ) (hv : v < n) (U : Finset (Fin n)) :
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-c * ∑ u ∈ U, harmonicAt n v u) := by
    apply (havoid v hv U).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right (neg_le_neg hc)
    exact sum_nonneg fun u _ => by unfold harmonicAt; positivity
  by_cases hh : 1 / Real.log n ≤ eta
  · simp only [if_pos hh]
    exact concrete_avoidance_harmonic hn p (hweak _ hh)
  · simp only [if_neg hh]
    exact concrete_avoidance_dr hn p (hweak _ hbase)

theorem paper_drsample {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    ProofOfSpaceStatement.drsampleProbability n (fun parents =>
      ProofOfSpaceStatement.DRSampleBlockDepthRobust parents (paperBudget n)
        ((37 / 25 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hn0 : 0 < n := by omega
  have h := concrete_avoidance_dr hn (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp_rw [drIncomingLaw_as_map] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  simp_rw [incomingGraph_block_statement] at h
  rw [drsampleProbability_eq hn0]
  exact h

theorem paper_bucketSample {n r : ℕ} (hn : 2 ^ 120 ≤ n) (hr : 1 ≤ r) :
    ProofOfSpaceStatement.bucketSampleProbability n r (fun parents =>
      ProofOfSpaceStatement.MultiSampleBlockDepthRobust parents (paperBudget n)
        ((37 / 25 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hn0 : 0 < n := by omega
  have hr0 : 0 < r := by omega
  have h := concrete_avoidance_dr hn (bucketIncomingLaw hn0 hr0)
    (fun _ hv A => bucketIncomingLaw_avoidance_sharp (by omega) hr0 hv A)
  simp only [bucketIncomingLaw] at h
  rw [parentSetLaw_block_probability] at h
  rw [bucketSampleProbability_eq hn0 hr0]
  exact h

theorem paper_harmonicSample {n r : ℕ} (hn : 2 ^ 120 ≤ n) (hr : 1 ≤ r) :
    ProofOfSpaceStatement.harmonicSampleProbability n r (fun parents =>
      ProofOfSpaceStatement.MultiSampleBlockDepthRobust parents (paperBudget n)
        ((2 : ℝ) * n / paperScale n) (paperWidth n)) ≥ 1 - paperFailure n := by
  have hn0 : 0 < n := by omega
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h := concrete_avoidance_harmonic hn (harmonicIncomingLaw hn0 r) (by
    intro v hv A
    apply (harmonicIncomingLaw_avoidance (by omega) r hv A).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _
      (sum_nonneg fun i _ => by unfold harmonicAt; positivity)
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (by exact_mod_cast hr) hlog.le)
  simp only [harmonicIncomingLaw] at h
  rw [parentSetLaw_block_probability] at h
  rw [harmonicSampleProbability_eq hn0]
  exact h

end ProofOfSpace.DRSample

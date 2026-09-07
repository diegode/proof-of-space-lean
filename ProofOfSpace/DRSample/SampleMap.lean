import ProofOfSpace.DRSample.Multiscale
import ProofOfSpace.DRSample.LawMap

/-! # Mapping independent rows into metagraph parents -/
namespace ProofOfSpace.DRSample
open Finset Classical

def getSample {α : Type*} (fallback : α) : (n : ℕ) → SampleSpace α n → ℕ → α
  | 0, _, _ => fallback
  | n + 1, s, j => if j = n then s.2 else getSample fallback n s.1 j

def mapSamples {α β : Type*} (f : ℕ → α → β) : (n : ℕ) → SampleSpace α n → SampleSpace β n
  | 0, _ => PUnit.unit
  | n + 1, s => (mapSamples f n s.1, f n s.2)

theorem independentSamples_map_expectation {α β : Type*} [Fintype α] [Fintype β]
    (p : ℕ → FiniteLaw α) (f : ℕ → α → β) (n : ℕ) (g : SampleSpace β n → ℝ) :
    (independentSamples (fun j => (p j).map (f j)) n).expectation g =
      (independentSamples p n).expectation (fun s => g (mapSamples f n s)) := by
  induction n with
  | zero => simp [independentSamples, mapSamples, FiniteLaw.expectation, SampleSpace]
  | succ n ih =>
    rw [independentSamples, FiniteLaw.expectation_product, ih,
      independentSamples, FiniteLaw.expectation_product]
    apply congrArg (independentSamples p n).expectation
    funext s
    exact FiniteLaw.expectation_map (p n) (f n) _

theorem independentSamples_map_probability {α β : Type*} [Fintype α] [Fintype β]
    (p : ℕ → FiniteLaw α) (f : ℕ → α → β) (n : ℕ) (Q : SampleSpace β n → Prop) :
    (independentSamples (fun j => (p j).map (f j)) n).probability Q =
      (independentSamples p n).probability (fun s => Q (mapSamples f n s)) := by
  simp_rw [FiniteLaw.probability_eq_expectation]
  exact independentSamples_map_expectation p f n _

theorem choiceAt_mapSamples {α : Type*} {M n j : ℕ} (f : ℕ → α → Finset (Fin M))
    (fallback : α) (s : SampleSpace α n) (hj : j < n) :
    choiceAt n (mapSamples f n s) j = f j (getSample fallback n s j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j = n
    · subst j
      simp [choiceAt, mapSamples, getSample]
    · simp only [choiceAt, mapSamples, getSample, if_neg he]
      exact ih s.1 (by omega)

theorem multiscale_mapped {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw α) (f : ℕ → α → Finset (Fin M)) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun row => Disjoint (f j row) A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M (mapSamples f M s)) (M / 48)
        ((3 * M / 4 : ℝ) * Real.exp (-64 / (3 * lambda)))) ≥
      1 - Real.exp (-(2 - Real.log 3) * M) := by
  have h := multiscale hM (fun j => (p j).map (f j)) hlambda (by
    intro j hj A
    rw [FiniteLaw.probability_map]
    exact havoid j hj A)
  rwa [independentSamples_map_probability] at h

theorem multiscale_mapped_wide {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw α) (f : ℕ → α → Finset (Fin M)) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun row => Disjoint (f j row) A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M (mapSamples f M s)) (M / 24)
        ((M / 2 : ℝ) * Real.exp (-64 / (3 * lambda)))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have h := multiscale_wide hM (fun j => (p j).map (f j)) hlambda (by
    intro j hj A
    rw [FiniteLaw.probability_map]
    exact havoid j hj A)
  rwa [independentSamples_map_probability] at h

theorem multiscale_mapped_third {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw α) (f : ℕ → α → Finset (Fin M)) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun row => Disjoint (f j row) A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M (mapSamples f M s)) (M / 3)
        ((M / 6 : ℝ) * Real.exp (-160 / lambda))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have h := multiscale_third hM (fun j => (p j).map (f j)) hlambda (by
    intro j hj A
    rw [FiniteLaw.probability_map]
    exact havoid j hj A)
  rwa [independentSamples_map_probability] at h


end ProofOfSpace.DRSample

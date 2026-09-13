import ProofOfSpace.DRSample.OptimizedRobustness
import ProofOfSpace.DRSample.MomentSharp

/-! # The paper's sharper multiscale probability and depth bounds -/
namespace ProofOfSpace.DRSample
open Finset Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem uniform_mass_bound_sharp (p : FiniteLaw α) (M : ℕ) (lambda : ℝ)
    (hlambda : 0 < lambda) (W : Finset (Fin M) → α → ℝ)
    (hmoment : ∀ S, p.expectation (fun a => Real.exp (2 * lambda / 3 * W S a)) ≤
      3 ^ (M - S.card)) :
    p.probability (fun a => ∀ S, W S a ≤ 12 * M / (5 * lambda)) ≥
      1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
  classical
  have htail (S : Finset (Fin M)) :
      p.probability (fun a => 12 * M / (5 * lambda) < W S a) ≤
        Real.exp (-(8 * M / 5)) * 3 ^ (M - S.card) := by
    have hmono : p.probability (fun a => 12 * M / (5 * lambda) < W S a) ≤
        p.probability (fun a => Real.exp (8 * M / 5) ≤
          Real.exp (2 * lambda / 3 * W S a)) := by
      apply p.probability_mono
      intro a ha
      apply Real.exp_le_exp.mpr
      have hden : 0 < 5 * lambda := by positivity
      have := (div_lt_iff₀ hden).mp ha
      nlinarith
    have hmarkov := p.mul_probability_le_expectation
      (fun a => (Real.exp_pos (2 * lambda / 3 * W S a)).le)
      (Real.exp_pos (8 * M / 5)).le
    have hbound : Real.exp (8 * M / 5) *
        p.probability (fun a => 12 * M / (5 * lambda) < W S a) ≤ 3 ^ (M - S.card) :=
      (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans
        (hmarkov.trans (hmoment S))
    have : p.probability (fun a => 12 * M / (5 * lambda) < W S a) ≤
        3 ^ (M - S.card) / Real.exp (8 * M / 5) :=
      (le_div_iff₀ (Real.exp_pos (8 * M / 5))).mpr (by rwa [mul_comm])
    simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using this
  have hsum : ∑ S : Finset (Fin M), (3 : ℝ) ^ (M - S.card) = 4 ^ M := by
    simpa only [Fintype.card_fin, one_pow, one_mul, show (1 : ℝ) + 3 = 4 by norm_num] using
      Fintype.sum_pow_mul_eq_add_pow (Fin M) (1 : ℝ) 3
  have hfail : p.probability (fun a => ∃ S, 12 * M / (5 * lambda) < W S a) ≤
      Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
    calc p.probability (fun a => ∃ S, 12 * M / (5 * lambda) < W S a)
        ≤ ∑ S, p.probability (fun a => 12 * M / (5 * lambda) < W S a) :=
          p.probability_exists_le_sum _
      _ ≤ ∑ S, Real.exp (-(8 * M / 5)) * 3 ^ (M - S.card) :=
        sum_le_sum fun S _ => htail S
      _ = Real.exp (-(8 * M / 5)) * 4 ^ M := by rw [← mul_sum, hsum]
      _ = Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
        rw [show (4 : ℝ) ^ M = Real.exp (M * Real.log 4) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
        rw [← Real.exp_add]
        congr 1
        ring
  have heq : p.probability (fun a => ∀ S, W S a ≤ 12 * M / (5 * lambda)) =
      1 - p.probability (fun a => ∃ S, 12 * M / (5 * lambda) < W S a) := by
    rw [← p.probability_compl]
    congr 1
    funext a
    simp only [not_exists, not_lt]
  rw [heq]
  linarith

end FiniteLaw

theorem exposedIncrement_moment_sharp {M : ℕ} (p : ℕ → FiniteLaw (Finset (Fin M)))
    (S : Finset ℕ) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i))
    (n : ℕ) (past : SampleSpace (Finset (Fin M)) n) :
    (p n).expectation (fun a => Real.exp (2 * lambda / 3 * exposedIncrement S n (past, a))) ≤
      if n ∈ S ∨ M ≤ n then 1 else 3 := by
  by_cases h : n ∈ S ∨ M ≤ n
  · simp only [exposedIncrement, if_pos h, mul_zero, Real.exp_zero,
      FiniteLaw.expectation_const]
    exact le_rfl
  · simp only [exposedIncrement, if_neg h]
    have hw : ∀ i : Fin M, 0 ≤ harmonicAt M n i := by
      intro i
      unfold harmonicAt
      positivity
    apply (p n).expectation_exp_le_three_of_tail _ lambda hlambda
    · intro parents
      exact sum_nonneg fun i _ => hw i
    · intro x _
      exact newForbiddenMass_tail (p n) _ _ hlambda (havoid n (by omega)) x

theorem actualMass_moment_sharp {M : ℕ} (p : ℕ → FiniteLaw (Finset (Fin M)))
    {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) (S : Finset (Fin M)) :
    (independentSamples p M).expectation (fun s => Real.exp (2 * lambda / 3 * actualMass S s)) ≤
      3 ^ (M - S.card) := by
  have hmoment := accumulated_moment p (exposedIncrement (natDeleted S)) (2 * lambda / 3)
    (fun j => if j ∈ natDeleted S ∨ M ≤ j then 1 else 3)
    (fun j => by split_ifs <;> norm_num)
    (exposedIncrement_moment_sharp p (natDeleted S) hlambda havoid) M
  simp_rw [accumulated_eq_forbiddenMass (natDeleted S) _ le_rfl] at hmoment
  have hprod : (∏ j ∈ range M, if j ∈ natDeleted S ∨ M ≤ j then (1 : ℝ) else 3) =
      3 ^ (M - S.card) := by
    calc
      _ = ∏ j ∈ range M, if j ∉ natDeleted S then (3 : ℝ) else 1 := by
        apply prod_congr rfl
        intro j hj
        have hjM := mem_range.mp hj
        by_cases hjs : j ∈ natDeleted S <;> simp [hjs, Nat.not_le.mpr hjM]
      _ = ∏ j ∈ (range M).filter (fun j => j ∉ natDeleted S), (3 : ℝ) := by rw [prod_filter]
      _ = 3 ^ (M - S.card) := by
        have heq : (range M).filter (fun j => j ∉ natDeleted S) = range M \ natDeleted S := by ext j; simp
        rw [heq, prod_const, card_sdiff, inter_eq_left.mpr (natDeleted_subset S), card_range, natDeleted_card]
  rw [hprod] at hmoment
  exact hmoment

theorem depth_of_mass_bound_sharp {M : ℕ} (hM : 0 < M) {lambda : ℝ}
    (hlambda : 0 < lambda) (S : Finset (Fin M)) (hS : S.card ≤ M / 3)
    (s : SampleSpace (Finset (Fin M)) M)
    (hmass : actualMass S s ≤ 12 * M / (5 * lambda)) :
    HasPath (exposedGraph M s) S ((M / 2 : ℝ) * Real.exp (-48 / lambda)) := by
  have hlabels : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := shallow_labels_third_overlap (natDeleted_subset S) hM (by simpa using hS)
    (exposedLabels (natDeleted S) M s) hlabels
  apply path_of_le_labelDepth S s (by positivity)
  apply le_trans _ hshallow
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hm : actualMass S s * (5 * lambda) ≤ 12 * M :=
    (le_div_iff₀ (by positivity)).mp hmass
  change -48 / lambda ≤ -20 * actualMass S s / M
  apply (div_le_div_iff₀ hlambda hMR).mpr
  nlinarith

/-- Multiscale robustness against deletion of one third of the vertices. -/
theorem multiscale_sharp {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-48 / lambda))) ≥
      1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
  have hmass := (independentSamples p M).uniform_mass_bound_sharp M lambda hlambda actualMass
    (actualMass_moment_sharp p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  exact depth_of_mass_bound_sharp hM hlambda S hS s (hs S)


theorem multiscale_mapped_sharp {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw α) (f : ℕ → α → Finset (Fin M)) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun row => Disjoint (f j row) A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M (mapSamples f M s)) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-48 / lambda))) ≥
      1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
  have h := multiscale_sharp hM (fun j => (p j).map (f j)) hlambda (by
    intro j hj A
    rw [FiniteLaw.probability_map]
    exact havoid j hj A)
  rwa [independentSamples_map_probability] at h


end ProofOfSpace.DRSample

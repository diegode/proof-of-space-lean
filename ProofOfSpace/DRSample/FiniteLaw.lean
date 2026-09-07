import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Elementary finite probability

Real weights suffice because every DRSample choice has finite support. Events
and expectations below are finite sums; the law carries its normalization proof.
-/
namespace ProofOfSpace.DRSample
open Finset

structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def expectation (p : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a, p.weight a * f a

noncomputable def probability (p : FiniteLaw α) (Q : α → Prop) : ℝ := by
  classical
  exact ∑ a, if Q a then p.weight a else 0

theorem probability_nonneg (p : FiniteLaw α) (Q : α → Prop) :
    0 ≤ p.probability Q := by
  classical
  exact sum_nonneg fun a _ => ite_nonneg (p.nonneg a) le_rfl

theorem probability_le_one (p : FiniteLaw α) (Q : α → Prop) :
    p.probability Q ≤ 1 := by
  classical
  rw [probability, ← p.total]
  apply sum_le_sum
  intro a _
  split_ifs <;> [exact le_rfl; exact p.nonneg a]

theorem probability_mono (p : FiniteLaw α) {Q R : α → Prop}
    (h : ∀ a, Q a → R a) : p.probability Q ≤ p.probability R := by
  classical
  apply sum_le_sum
  intro a _
  by_cases hQ : Q a
  · simp [hQ, h a hQ]
  · simp only [if_neg hQ]
    split_ifs <;> [exact p.nonneg a; exact le_rfl]

theorem expectation_nonneg (p : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ p.expectation f :=
  sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf a)

theorem expectation_mono (p : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : p.expectation f ≤ p.expectation g :=
  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

theorem probability_compl (p : FiniteLaw α) (Q : α → Prop) :
    p.probability (fun a => ¬ Q a) = 1 - p.probability Q := by
  classical
  have h : p.probability Q + p.probability (fun a => ¬ Q a) = 1 := by
    rw [probability, probability, ← sum_add_distrib, ← p.total]
    apply sum_congr rfl
    intro a _
    by_cases hQ : Q a <;> simp [hQ]
  linarith

/-- The union bound does not require independence. -/
theorem probability_exists_le_sum (p : FiniteLaw α) (Q : β → α → Prop) :
    p.probability (fun a => ∃ b, Q b a) ≤ ∑ b, p.probability (Q b) := by
  classical
  unfold probability
  rw [sum_comm]
  apply sum_le_sum
  intro a _
  split_ifs with h
  · obtain ⟨b, hb⟩ := h
    calc p.weight a = (if Q b a then p.weight a else 0) := by simp [hb]
      _ ≤ ∑ b, if Q b a then p.weight a else 0 :=
        single_le_sum (f := fun b => if Q b a then p.weight a else 0)
          (fun b _ => ite_nonneg (p.nonneg a) le_rfl) (mem_univ b)
  · apply sum_nonneg
    intro b _
    exact ite_nonneg (p.nonneg a) le_rfl

/-- Markov's inequality, in a form requiring no division. -/
theorem mul_probability_le_expectation (p : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) {t : ℝ} (_ht : 0 ≤ t) :
    t * p.probability (fun a => t ≤ f a) ≤ p.expectation f := by
  classical
  rw [probability, mul_sum, expectation]
  apply sum_le_sum
  intro a _
  split_ifs with h
  · nlinarith [p.nonneg a]
  · simp only [mul_zero]
    exact mul_nonneg (p.nonneg a) (hf a)

/-- A moment bound for each fixed deletion set becomes one graph event uniform
in the deleted set. This is the weighted `3^M` union bound in the note. -/
theorem uniform_mass_bound (p : FiniteLaw α) (M : ℕ) (lambda : ℝ)
    (hlambda : 0 < lambda) (W : Finset (Fin M) → α → ℝ)
    (hmoment : ∀ S, p.expectation (fun a => Real.exp (lambda / 2 * W S a)) ≤
      2 ^ (M - S.card)) :
    p.probability (fun a => ∀ S, W S a ≤ 4 * M / lambda) ≥
      1 - Real.exp (-(2 - Real.log 3) * M) := by
  classical
  have htail (S : Finset (Fin M)) :
      p.probability (fun a => 4 * M / lambda < W S a) ≤
        Real.exp (-(2 * M)) * 2 ^ (M - S.card) := by
    have hmono : p.probability (fun a => 4 * M / lambda < W S a) ≤
        p.probability (fun a => Real.exp (2 * M) ≤
          Real.exp (lambda / 2 * W S a)) := by
      apply p.probability_mono
      intro a ha
      apply Real.exp_le_exp.mpr
      have := (div_lt_iff₀ hlambda).mp ha
      nlinarith
    have hmarkov := p.mul_probability_le_expectation
      (fun a => (Real.exp_pos (lambda / 2 * W S a)).le)
      (Real.exp_pos (2 * M)).le
    have hbound : Real.exp (2 * M) *
        p.probability (fun a => 4 * M / lambda < W S a) ≤ 2 ^ (M - S.card) :=
      (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans
        (hmarkov.trans (hmoment S))
    have : p.probability (fun a => 4 * M / lambda < W S a) ≤
        2 ^ (M - S.card) / Real.exp (2 * M) :=
      (le_div_iff₀ (Real.exp_pos (2 * M))).mpr (by rwa [mul_comm])
    simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using this
  have hsum : ∑ S : Finset (Fin M), (2 : ℝ) ^ (M - S.card) = 3 ^ M := by
    simpa only [Fintype.card_fin, one_pow, one_mul, show (1 : ℝ) + 2 = 3 by norm_num] using
      Fintype.sum_pow_mul_eq_add_pow (Fin M) (1 : ℝ) 2
  have hfail : p.probability (fun a => ∃ S, 4 * M / lambda < W S a) ≤
      Real.exp (-(2 - Real.log 3) * M) := by
    calc p.probability (fun a => ∃ S, 4 * M / lambda < W S a)
        ≤ ∑ S, p.probability (fun a => 4 * M / lambda < W S a) :=
          p.probability_exists_le_sum _
      _ ≤ ∑ S, Real.exp (-(2 * M)) * 2 ^ (M - S.card) := sum_le_sum fun S _ => htail S
      _ = Real.exp (-(2 * M)) * 3 ^ M := by rw [← mul_sum, hsum]
      _ = Real.exp (-(2 - Real.log 3) * M) := by
        rw [show (3 : ℝ) ^ M = Real.exp (M * Real.log 3) by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
        rw [← Real.exp_add]
        congr 1
        ring
  have heq : p.probability (fun a => ∀ S, W S a ≤ 4 * M / lambda) =
      1 - p.probability (fun a => ∃ S, 4 * M / lambda < W S a) := by
    rw [← p.probability_compl]
    congr 1
    funext a
    simp only [not_exists, not_lt]
  rw [heq]
  linarith

end FiniteLaw
end ProofOfSpace.DRSample

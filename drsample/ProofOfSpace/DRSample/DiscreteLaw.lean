import ProofOfSpace.DRSample.Moment
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Discrete probability with possibly infinite support. All expectations used
below are nonnegative; summability is established before comparing series. -/
namespace ProofOfSpace.DRSample
open Finset Classical

structure DiscreteLaw (α : Type*) where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  summable : Summable weight
  total : ∑' a, weight a = 1

namespace DiscreteLaw
variable {α β : Type*}

noncomputable def ofPMF (p : PMF α) : DiscreteLaw α where
  weight a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  summable := ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  total := by rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]; simp

noncomputable def expectation (p : DiscreteLaw α) (f : α → ℝ) : ℝ :=
  ∑' a, p.weight a * f a

noncomputable def probability (p : DiscreteLaw α) (Q : α → Prop) : ℝ := by
  classical
  exact ∑' a, if Q a then p.weight a else 0

theorem summable_event (p : DiscreteLaw α) (Q : α → Prop) :
    Summable (fun a => if Q a then p.weight a else 0) := by
  classical
  exact p.summable.indicator {a | Q a}

theorem probability_ofPMF (p : PMF α) (Q : α → Prop) :
    (ofPMF p).probability Q = (p.toOuterMeasure {a | Q a}).toReal := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases ha : Q a <;> simp [probability, ofPMF, Set.indicator, ha]
  · intro a
    by_cases ha : Q a <;> simp [Set.indicator, ha, p.apply_ne_top]

theorem probability_nonneg (p : DiscreteLaw α) (Q : α → Prop) :
    0 ≤ p.probability Q := by
  classical
  exact tsum_nonneg fun a => ite_nonneg (p.nonneg a) le_rfl

theorem probability_le_one (p : DiscreteLaw α) (Q : α → Prop) :
    p.probability Q ≤ 1 := by
  classical
  rw [← p.total]
  exact (p.summable_event Q).tsum_le_tsum (fun a => by split_ifs <;> simp [p.nonneg])
    p.summable

theorem probability_mono (p : DiscreteLaw α) {Q R : α → Prop}
    (h : ∀ a, Q a → R a) : p.probability Q ≤ p.probability R := by
  classical
  apply Summable.tsum_le_tsum _ (p.summable_event Q) (p.summable_event R)
  intro a
  by_cases hQ : Q a
  · simp [hQ, h a hQ]
  · simp only [if_neg hQ]
    split_ifs <;> simp [p.nonneg]

theorem probability_mono_on_weight (p : DiscreteLaw α) {Q R : α → Prop}
    (h : ∀ a, p.weight a ≠ 0 → Q a → R a) : p.probability Q ≤ p.probability R := by
  apply Summable.tsum_le_tsum _ (p.summable_event Q) (p.summable_event R)
  intro a
  by_cases hw : p.weight a = 0
  · simp [hw]
  by_cases hQ : Q a
  · simp [hQ, h a hw hQ]
  · simp only [if_neg hQ]
    split_ifs <;> simp [p.nonneg]

theorem probability_compl (p : DiscreteLaw α) (Q : α → Prop) :
    p.probability (fun a => ¬ Q a) = 1 - p.probability Q := by
  classical
  have h : p.probability Q + p.probability (fun a => ¬ Q a) = 1 := by
    rw [probability, probability, ← (p.summable_event Q).tsum_add (p.summable_event _),
      ← p.total]
    apply tsum_congr
    intro a
    by_cases hQ : Q a <;> simp [hQ]
  linarith

theorem probability_exists_le_sum [Fintype β] (p : DiscreteLaw α) (Q : β → α → Prop) :
    p.probability (fun a => ∃ b, Q b a) ≤ ∑ b, p.probability (Q b) := by
  classical
  unfold probability
  rw [← Summable.tsum_finsetSum (fun b _ => p.summable_event (Q b))]
  apply Summable.tsum_le_tsum _ (p.summable_event _) (summable_sum (fun b _ => p.summable_event _))
  intro a
  split_ifs with h
  · obtain ⟨b, hb⟩ := h
    calc p.weight a = (if Q b a then p.weight a else 0) := by simp [hb]
      _ ≤ ∑ b, if Q b a then p.weight a else 0 :=
        single_le_sum (f := fun b => if Q b a then p.weight a else 0) (fun b _ => ite_nonneg (p.nonneg a) le_rfl) (mem_univ b)
  · exact sum_nonneg fun b _ => ite_nonneg (p.nonneg a) le_rfl

theorem summable_bounded (p : DiscreteLaw α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ a, 0 ≤ f a) (hC : ∀ a, f a ≤ C) : Summable (fun a => p.weight a * f a) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (p.nonneg a) (hf a))
    (fun a => mul_le_mul_of_nonneg_left (hC a) (p.nonneg a)) (p.summable.mul_right C)

theorem mul_probability_le_expectation (p : DiscreteLaw α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) (hsum : Summable (fun a => p.weight a * f a)) {t : ℝ} :
    t * p.probability (fun a => t ≤ f a) ≤ p.expectation f := by
  classical
  rw [probability, ← tsum_mul_left, expectation]
  apply Summable.tsum_le_tsum _ ((p.summable_event _).mul_left t) hsum
  intro a
  split_ifs with h
  · nlinarith [p.nonneg a]
  · simp only [mul_zero]
    exact mul_nonneg (p.nonneg a) (hf a)

/-- Tail control implies a moment bound without a bounded-support assumption. -/
theorem expectation_exp_le_two_of_tail (p : DiscreteLaw α) (X : α → ℝ)
    (lambda : ℝ) (hlambda : 0 < lambda) (hX : ∀ a, 0 ≤ X a)
    (htail : ∀ x, 0 < x → p.probability (fun a => x ≤ X a) ≤ Real.exp (-lambda * x)) :
    p.expectation (fun a => Real.exp (lambda / 2 * X a)) ≤ 2 := by
  classical
  apply Real.tsum_le_of_sum_le (fun a => mul_nonneg (p.nonneg a) (Real.exp_pos _).le)
  intro s
  have h := sum_exp_le_two_sqrt s p.weight (fun a => lambda / 2 * X a)
    (fun a _ => p.nonneg a) (by
      intro a _
      have hsub : ∑ b ∈ s.filter (fun b => lambda / 2 * X a ≤ lambda / 2 * X b),
          p.weight b ≤ p.probability (fun b => X a ≤ X b) := by
        rw [sum_filter]
        have heq : (fun b => if lambda / 2 * X a ≤ lambda / 2 * X b then p.weight b else 0) =
            (fun b => if X a ≤ X b then p.weight b else 0) := by
          funext b
          simp only [mul_le_mul_iff_right₀ (by positivity : 0 < lambda / 2)]
        rw [heq]
        exact Summable.sum_le_tsum s (fun b _ => ite_nonneg (p.nonneg b) le_rfl)
          (p.summable_event _)
      have ht : p.probability (fun b => X a ≤ X b) ≤ Real.exp (-lambda * X a) := by
        rcases eq_or_lt_of_le (hX a) with ha | ha
        · simpa [← ha] using p.probability_le_one (fun b => X a ≤ X b)
        · exact htail (X a) ha
      convert hsub.trans ht using 1 <;> congr 1 <;> ring)
  have hm : ∑ a ∈ s, p.weight a ≤ 1 :=
    p.total ▸ Summable.sum_le_tsum s (fun a _ => p.nonneg a) p.summable
  exact h.trans (by nlinarith [Real.sqrt_le_sqrt hm, Real.sqrt_one])

/-- Conditioning on an atom of positive probability. -/
noncomputable def condition (p : DiscreteLaw α) (Q : α → Prop)
    (hQ : 0 < p.probability Q) : DiscreteLaw α where
  weight a := (if Q a then p.weight a else 0) / p.probability Q
  nonneg a := div_nonneg (ite_nonneg (p.nonneg a) le_rfl) hQ.le
  summable := (p.summable_event Q).div_const _
  total := by rw [tsum_div_const]; exact div_self hQ.ne'

theorem probability_condition (p : DiscreteLaw α) (Q R : α → Prop)
    (hQ : 0 < p.probability Q) :
    (p.condition Q hQ).probability R = p.probability (fun a => Q a ∧ R a) / p.probability Q := by
  rw [probability, probability, ← tsum_div_const]
  apply tsum_congr
  intro a
  by_cases hq : Q a <;> by_cases hr : R a <;> simp [condition, hq, hr]

theorem atom_expectation (p : DiscreteLaw α) (Q : α → Prop) (f : α → ℝ)
    (hQ : 0 < p.probability Q) :
    (∑' a, if Q a then p.weight a * f a else 0) =
      p.probability Q * (p.condition Q hQ).expectation f := by
  rw [expectation, ← tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : Q a <;> simp [condition, ha]; field_simp

theorem weight_eq_zero_of_probability_eq_zero (p : DiscreteLaw α) (Q : α → Prop)
    (hQ : p.probability Q = 0) {a : α} (ha : Q a) : p.weight a = 0 := by
  have h := Summable.sum_le_tsum {a} (fun b _ => ite_nonneg (p.nonneg b) le_rfl)
    (p.summable_event Q)
  simp only [sum_singleton, if_pos ha] at h
  exact le_antisymm (h.trans_eq hQ) (p.nonneg a)

/-- Regroup an absolutely summable expectation by the observed history. -/
theorem expectation_by_fibers (p : DiscreteLaw α) (key : α → β) (f : α → ℝ)
    (hsum : Summable (fun a => p.weight a * f a)) :
    HasSum (fun b => ∑' a, if key a = b then p.weight a * f a else 0) (p.expectation f) := by
  apply (hsum.hasSum.tsum_fiberwise key).congr_fun
  intro b
  exact (_root_.tsum_subtype (key ⁻¹' {b}) (fun a => p.weight a * f a)).symm

/-- Conditional moment bounds multiply when the preceding factor is fixed by
history. No independence assumption is needed. -/
theorem expectation_mul_le (p : DiscreteLaw α) (key : α → β) (F : β → ℝ)
    (g : α → ℝ) (C : ℝ) (hF : ∀ b, 0 ≤ F b)
    (hsum : Summable (fun a => p.weight a * (F (key a) * g a)))
    (hprev : Summable (fun a => p.weight a * F (key a)))
    (hlocal : ∀ b, (∑' a, if key a = b then p.weight a * g a else 0) ≤
      C * p.probability (fun a => key a = b)) :
    p.expectation (fun a => F (key a) * g a) ≤ C * p.expectation (fun a => F (key a)) := by
  have h₁ := p.expectation_by_fibers key (fun a => F (key a) * g a) hsum
  have h₂ := (p.expectation_by_fibers key (fun a => F (key a)) hprev).mul_left C
  rw [← h₁.tsum_eq, ← h₂.tsum_eq]
  apply Summable.tsum_le_tsum _ h₁.summable h₂.summable
  intro b
  have heq : (∑' a, if key a = b then p.weight a * (F (key a) * g a) else 0) =
      F b * ∑' a, if key a = b then p.weight a * g a else 0 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases ha : key a = b <;> simp [ha] <;> ring
  have heq₂ : (∑' a, if key a = b then p.weight a * F (key a) else 0) =
      F b * p.probability (fun a => key a = b) := by
    rw [probability, ← tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases ha : key a = b <;> simp [ha, mul_comm]
  rw [heq, heq₂]
  nlinarith [mul_le_mul_of_nonneg_left (hlocal b) (hF b)]

/-- A moment bound for each fixed deletion set becomes one graph event uniform
in the deleted set. This is the weighted `3^M` union bound in the note. -/
theorem uniform_mass_bound (p : DiscreteLaw α) (M : ℕ) (lambda : ℝ)
    (hlambda : 0 < lambda) (W : Finset (Fin M) → α → ℝ)
    (hsum : ∀ S, Summable (fun a => p.weight a * Real.exp (lambda / 2 * W S a)))
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
    have hmarkov := p.mul_probability_le_expectation (t := Real.exp (2 * M))
      (fun a => (Real.exp_pos (lambda / 2 * W S a)).le)
      (hsum S)
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

end DiscreteLaw
end ProofOfSpace.DRSample

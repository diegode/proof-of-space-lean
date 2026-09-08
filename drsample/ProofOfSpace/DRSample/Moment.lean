import ProofOfSpace.DRSample.FiniteLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exponential moments from finite tail bounds

A finite-sum proof avoids measure-theoretic conditional expectation. Removing a
minimum-valued outcome and telescoping square roots proves the sharp factor two.
-/
namespace ProofOfSpace.DRSample
open Finset

/-- Finite layer-cake bound: tail domination by `exp (-2 X)` gives a square-root
bound on the exponential moment, even for a subprobability law. -/
theorem sum_exp_le_two_sqrt {α : Type*} [DecidableEq α] (s : Finset α)
    (w X : α → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (htail : ∀ a ∈ s, ∑ b ∈ s.filter (fun b => X a ≤ X b), w b ≤ Real.exp (-2 * X a)) :
    ∑ a ∈ s, w a * Real.exp (X a) ≤ 2 * Real.sqrt (∑ a ∈ s, w a) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨a, ha, hmin⟩ := s.exists_min_image X hne
    have hrest : ∑ b ∈ s.erase a, w b * Real.exp (X b) ≤
        2 * Real.sqrt (∑ b ∈ s.erase a, w b) := by
      apply ih (s.erase a) (s.erase_ssubset ha) (fun b hb => hw b (mem_of_mem_erase hb))
      intro b hb
      apply le_trans _ (htail b (mem_of_mem_erase hb))
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset_filter _ (erase_subset _ _)
      · intro c hc _
        exact hw c (mem_filter.mp hc).1
    have hmass : ∑ b ∈ s, w b ≤ Real.exp (-2 * X a) := by
      convert htail a ha using 1
      congr 1
      exact (filter_eq_self.mpr fun b hb => hmin b hb).symm
    have hnonneg : 0 ≤ ∑ b ∈ s, w b := sum_nonneg hw
    have hrestnonneg : 0 ≤ ∑ b ∈ s.erase a, w b :=
      sum_nonneg fun b hb => hw b (mem_of_mem_erase hb)
    have hsplit : (∑ b ∈ s.erase a, w b) + w a = ∑ b ∈ s, w b :=
      sum_erase_add _ _ ha
    have hsquare := Real.sq_sqrt hnonneg
    have hrestsquare := Real.sq_sqrt hrestnonneg
    have hsqrt := Real.sqrt_nonneg (∑ b ∈ s, w b)
    have hrestsqrt := Real.sqrt_nonneg (∑ b ∈ s.erase a, w b)
    have hweight := hw a ha
    have hexp := Real.exp_pos (X a)
    have hexpsquare : Real.exp (X a) ^ 2 = Real.exp (2 * X a) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hprod : (∑ b ∈ s, w b) * Real.exp (X a) ^ 2 ≤ 1 := by
      rw [hexpsquare]
      calc (∑ b ∈ s, w b) * Real.exp (2 * X a)
          ≤ Real.exp (-2 * X a) * Real.exp (2 * X a) :=
            mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hrootprod : Real.sqrt (∑ b ∈ s, w b) * Real.exp (X a) ≤ 1 := by
      nlinarith [sq_nonneg (Real.sqrt (∑ b ∈ s, w b) * Real.exp (X a) - 1)]
    have hlocal : w a * Real.exp (X a) +
        2 * Real.sqrt (∑ b ∈ s.erase a, w b) ≤ 2 * Real.sqrt (∑ b ∈ s, w b) := by
      by_cases hz : Real.sqrt (∑ b ∈ s, w b) = 0
      · have hp : w a = 0 := by nlinarith
        have hq : Real.sqrt (∑ b ∈ s.erase a, w b) = 0 := by nlinarith
        simp [hp, hq, hz]
      · have hpos : 0 < Real.sqrt (∑ b ∈ s, w b) := lt_of_le_of_ne hsqrt (Ne.symm hz)
        apply (mul_le_mul_iff_right₀ hpos).mp
        have hweighted := mul_le_mul_of_nonneg_left hrootprod hweight
        nlinarith [sq_nonneg (Real.sqrt (∑ b ∈ s, w b) -
          Real.sqrt (∑ b ∈ s.erase a, w b))]
    rw [← sum_erase_add _ _ ha]
    linarith

namespace FiniteLaw
variable {α : Type*} [Fintype α]

/-- The factor-two conditional moment estimate used at each destination. -/
theorem expectation_exp_le_two_of_tail (p : FiniteLaw α) (X : α → ℝ)
    (lambda : ℝ) (hlambda : 0 < lambda) (hX : ∀ a, 0 ≤ X a)
    (htail : ∀ x, 0 < x → p.probability (fun a => x ≤ X a) ≤ Real.exp (-lambda * x)) :
    p.expectation (fun a => Real.exp (lambda / 2 * X a)) ≤ 2 := by
  classical
  have h := sum_exp_le_two_sqrt univ p.weight (fun a => lambda / 2 * X a)
    (fun a _ => p.nonneg a) (by
      intro a _
      have heq : (univ.filter fun b => lambda / 2 * X a ≤ lambda / 2 * X b) =
          (univ.filter fun b => X a ≤ X b) := by
        ext b
        simp only [mem_filter, mem_univ, true_and]
        exact mul_le_mul_iff_right₀ (by positivity : 0 < lambda / 2)
      rw [heq]
      have htaila : p.probability (fun b => X a ≤ X b) ≤ Real.exp (-lambda * X a) := by
        rcases eq_or_lt_of_le (hX a) with ha | ha
        · rw [← ha]
          simpa using p.probability_le_one (fun b => 0 ≤ X b)
        · exact htail (X a) ha
      simpa [probability, sum_filter, show -2 * (lambda / 2 * X a) = -lambda * X a by ring]
        using htaila)
  simpa [expectation, p.total] using h

end FiniteLaw
end ProofOfSpace.DRSample

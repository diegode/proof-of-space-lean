import ProofOfSpace.DRSample.Moment

/-! # The two-thirds exponential moment used by the paper

Finite layer cake, with cube roots, gives the conditional factor three without
introducing measure-theoretic assumptions on the finite sampling space.
-/
namespace ProofOfSpace.DRSample
open Finset

theorem sum_exp_le_three_cuberoot {α : Type*} [DecidableEq α] (s : Finset α)
    (w X : α → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (htail : ∀ a ∈ s, ∑ b ∈ s.filter (fun b => X a ≤ X b), w b ≤
      Real.exp (-3 * X a)) :
    ∑ a ∈ s, w a * Real.exp (2 * X a) ≤
      3 * (∑ a ∈ s, w a) ^ (1 / 3 : ℝ) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · norm_num
    obtain ⟨a, ha, hmin⟩ := s.exists_min_image X hne
    have hrest := ih (s.erase a) (s.erase_ssubset ha)
      (fun b hb => hw b (mem_of_mem_erase hb)) (by
        intro b hb
        apply le_trans _ (htail b (mem_of_mem_erase hb))
        apply sum_le_sum_of_subset_of_nonneg
        · exact filter_subset_filter _ (erase_subset _ _)
        · intro c hc _
          exact hw c (mem_filter.mp hc).1)
    have hmass : ∑ b ∈ s, w b ≤ Real.exp (-3 * X a) := by
      convert htail a ha using 1
      congr 1
      exact (filter_eq_self.mpr fun b hb => hmin b hb).symm
    let p := (∑ b ∈ s, w b) ^ (1 / 3 : ℝ)
    let q := (∑ b ∈ s.erase a, w b) ^ (1 / 3 : ℝ)
    have hp0 : 0 ≤ p := Real.rpow_nonneg (sum_nonneg hw) _
    have hq0 : 0 ≤ q := Real.rpow_nonneg
      (sum_nonneg fun b hb => hw b (mem_of_mem_erase hb)) _
    have hp3 : p ^ 3 = ∑ b ∈ s, w b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (sum_nonneg hw)]
      norm_num
    have hq3 : q ^ 3 = ∑ b ∈ s.erase a, w b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (sum_nonneg fun b hb => hw b (mem_of_mem_erase hb))]
      norm_num
    have hsplit := sum_erase_add s w ha
    have hwa := hw a ha
    have hqp : q ≤ p := Real.rpow_le_rpow
      (sum_nonneg fun b hb => hw b (mem_of_mem_erase hb))
      (by linarith) (by norm_num)
    have hroot : p ≤ Real.exp (-X a) := by
      have h := Real.rpow_le_rpow (sum_nonneg hw) hmass (by norm_num : (0 : ℝ) ≤ 1 / 3)
      simpa only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        show -3 * X a * (1 / 3) = -X a by ring] using h
    have hprod : p ^ 2 * Real.exp (2 * X a) ≤ 1 := by
      calc p ^ 2 * Real.exp (2 * X a)
          ≤ (Real.exp (-X a)) ^ 2 * Real.exp (2 * X a) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp0 hroot 2) (Real.exp_pos _).le
        _ = 1 := by
          rw [pow_two, ← Real.exp_add, ← Real.exp_add]
          ring_nf
          exact Real.exp_zero
    have hlocal : w a * Real.exp (2 * X a) + 3 * q ≤ 3 * p := by
      by_cases hp : p = 0
      · have hq : q = 0 := le_antisymm (by simpa [hp] using hqp) hq0
        have hwz : w a = 0 := by simp [hp, hq] at hp3 hq3; linarith
        simp [hp, hq, hwz]
      · have hp2 : 0 < p ^ 2 := sq_pos_of_pos (lt_of_le_of_ne hp0 (Ne.symm hp))
        apply (mul_le_mul_iff_right₀ hp2).mp
        have hweighted := mul_le_mul_of_nonneg_left hprod hwa
        have hfactor := mul_nonneg (sq_nonneg (p - q)) (show 0 ≤ 2 * p + q by positivity)
        nlinarith
    rw [← sum_erase_add s (fun b => w b * Real.exp (2 * X b)) ha]
    change _ ≤ 3 * p
    change _ ≤ 3 * q at hrest
    linarith

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem expectation_exp_le_three_of_tail (p : FiniteLaw α) (X : α → ℝ)
    (lambda : ℝ) (hlambda : 0 < lambda) (hX : ∀ a, 0 ≤ X a)
    (htail : ∀ x, 0 < x → p.probability (fun a => x ≤ X a) ≤ Real.exp (-lambda * x)) :
    p.expectation (fun a => Real.exp (2 * lambda / 3 * X a)) ≤ 3 := by
  classical
  have h := sum_exp_le_three_cuberoot univ p.weight (fun a => lambda / 3 * X a)
    (fun a _ => p.nonneg a) (by
      intro a _
      have heq : (univ.filter fun b => lambda / 3 * X a ≤ lambda / 3 * X b) =
          (univ.filter fun b => X a ≤ X b) := by
        ext b
        simp only [mem_filter, mem_univ, true_and]
        exact mul_le_mul_iff_right₀ (by positivity : 0 < lambda / 3)
      rw [heq]
      have htaila : p.probability (fun b => X a ≤ X b) ≤ Real.exp (-lambda * X a) := by
        rcases eq_or_lt_of_le (hX a) with ha | ha
        · rw [← ha]
          simpa using p.probability_le_one (fun b => 0 ≤ X b)
        · exact htail (X a) ha
      simpa [probability, sum_filter,
        show -3 * (lambda / 3 * X a) = -lambda * X a by ring] using htaila)
  simpa [expectation, p.total,
    show ∀ a, 2 * (lambda / 3 * X a) = 2 * lambda / 3 * X a by intro a; ring] using h

end FiniteLaw
end ProofOfSpace.DRSample

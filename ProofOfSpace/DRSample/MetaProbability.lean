import ProofOfSpace.DRSample.PortGeometry
import ProofOfSpace.DRSample.SampleMap
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Harmonic avoidance in the restricted metagraph -/
namespace ProofOfSpace.DRSample
open Finset Classical

def metaParents {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (j : ℕ) (row : Fin m → Finset (Fin n)) : Finset (Fin M) :=
  univ.filter fun i => i.val < j ∧
    (i.val + 1 = j ∨ ∃ k : Fin m, k.val < m / 3 ∧
      ∃ a : Fin (m / 3), outgoingVertex hm hn i a ∈ row k)

noncomputable def rowLaw {n : ℕ} (m : ℕ) (p : ℕ → FiniteLaw (Finset (Fin n)))
    (j : ℕ) : FiniteLaw (Fin m → Finset (Fin n)) :=
  FiniteLaw.pi fun k => p (j * m + k.val)

theorem prod_fin_nat (M : ℕ) (f : ℕ → ℝ) :
    (∏ i : Fin M, f i.val) = ∏ i ∈ range M, f i := by
  apply prod_bij (fun i _ => i.val)
  · intro i _; exact mem_range.mpr i.isLt
  · intro i _ j _ he; exact Fin.ext he
  · intro i hi; exact ⟨⟨i, mem_range.mp hi⟩, mem_univ _, rfl⟩
  · intros; rfl

theorem prod_if_fin_lt {m t : ℕ} (ht : t ≤ m) (z : ℝ) :
    (∏ k : Fin m, if k.val < t then z else 1) = z ^ t := by
  rw [prod_fin_nat m (fun k => if k < t then z else 1), ← prod_filter]
  have heq : (range m).filter (· < t) = range t := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  rw [heq, prod_const, card_range]

theorem meta_disjoint_implies_row_disjoint {n m M j : ℕ}
    (hm : 3 ≤ m) (hn : M * m ≤ n) (A : Finset (Fin M))
    (row : Fin m → Finset (Fin n)) (h : Disjoint (metaParents hm hn j row) A)
    (k : Fin m) (hk : k.val < m / 3) :
    Disjoint (row k) (outgoingPorts hm hn (A.filter fun i => i.val < j)) := by
  apply disjoint_left.mpr
  intro u hu hport
  obtain ⟨⟨i, a⟩, hia, heq⟩ := mem_image.mp hport
  have hi := mem_filter.mp (mem_product.mp hia).1
  apply (disjoint_left.mp h) _ hi.1
  apply mem_filter.mpr
  refine ⟨mem_univ _, hi.2, Or.inr ⟨k, hk, a, ?_⟩⟩
  simpa only [heq] using hu

theorem harmonicAt_filter_earlier {M j : ℕ} (A : Finset (Fin M)) :
    (∑ i ∈ A.filter (fun i => i.val < j), harmonicAt M j i) =
      ∑ i ∈ A, harmonicAt M j i := by
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  unfold harmonicAt
  split_ifs <;> rfl

/-- Grouping independent destinations multiplies the harmonic coefficient by
the square of the port width, divided by twice the block width. -/
theorem metaParents_avoidance {n m M j : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (hj : j < M) (p : ℕ → FiniteLaw (Finset (Fin n))) {c : ℝ} (hc : 0 ≤ c)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-c * ∑ u ∈ U, harmonicAt n v u)) (A : Finset (Fin M)) :
    (rowLaw m p j).probability (fun row => Disjoint (metaParents hm hn j row) A) ≤
      Real.exp (-(c * (m / 3 : ℕ) ^ 2 / (2 * m)) * ∑ i ∈ A, harmonicAt M j i) := by
  by_cases hpred : ∃ i ∈ A, i.val + 1 = j
  · obtain ⟨i, hi, hij⟩ := hpred
    have hnone : ∀ row, ¬ Disjoint (metaParents hm hn j row) A := by
      intro row h
      apply (disjoint_left.mp h) _ hi
      exact mem_filter.mpr ⟨mem_univ _, by omega, Or.inl hij⟩
    have heq : (rowLaw m p j).probability (fun row => Disjoint (metaParents hm hn j row) A) = 0 := by
      simp [FiniteLaw.probability, hnone]
    rw [heq]
    exact (Real.exp_pos _).le
  · have hA : ∀ i ∈ A.filter (fun i => i.val < j), i.val + 2 ≤ j := by
      intro i hi
      have hh := mem_filter.mp hi
      have hne : i.val + 1 ≠ j := fun he => hpred ⟨i, hh.1, he⟩
      omega
    have hstep (k : Fin m) :
        (p (j * m + k.val)).probability (fun parents =>
          k.val < m / 3 → Disjoint parents (outgoingPorts hm hn (A.filter fun i => i.val < j))) ≤
          if k.val < m / 3 then
            Real.exp (-(c * ((m / 3 : ℕ) : ℝ) / (2 * m)) * ∑ i ∈ A, harmonicAt M j i) else 1 := by
      by_cases hk : k.val < m / 3
      · simp only [hk, true_implies, if_true]
        have hvn : j * m + k.val < n := by
          have hmul := Nat.mul_le_mul_right m (show j + 1 ≤ M by omega)
          have := k.isLt
          nlinarith
        apply (havoid _ hvn _).trans
        apply Real.exp_le_exp.mpr
        have hgeo := outgoingPorts_harmonic_ge hm hn _ hA k
        rw [harmonicAt_filter_earlier] at hgeo
        have h := mul_le_mul_of_nonpos_left hgeo (neg_nonpos.mpr hc)
        convert h using 1 <;> first | ring | rfl
      · simp [hk]
    have hmono : (rowLaw m p j).probability (fun row => Disjoint (metaParents hm hn j row) A) ≤
        (rowLaw m p j).probability (fun row => ∀ k : Fin m, k.val < m / 3 →
          Disjoint (row k) (outgoingPorts hm hn (A.filter fun i => i.val < j))) := by
      apply FiniteLaw.probability_mono
      intro row h k hk
      exact meta_disjoint_implies_row_disjoint hm hn A row h k hk
    apply hmono.trans
    rw [rowLaw, FiniteLaw.probability_pi (fun k : Fin m => p (j * m + k.val))
      (fun k parents => k.val < m / 3 → Disjoint parents (outgoingPorts hm hn (A.filter fun i => i.val < j)))]
    calc _ ≤ ∏ k : Fin m, if k.val < m / 3 then
          Real.exp (-(c * ((m / 3 : ℕ) : ℝ) / (2 * m)) * ∑ i ∈ A, harmonicAt M j i) else 1 := by
            apply prod_le_prod
            · intro k _; exact FiniteLaw.probability_nonneg _ _
            · intro k _; exact hstep k
      _ = Real.exp (-(c * (m / 3 : ℕ) ^ 2 / (2 * m)) * ∑ i ∈ A, harmonicAt M j i) := by
        rw [prod_if_fin_lt (Nat.div_le_self _ _), ← Real.exp_nat_mul]
        congr 1
        ring

theorem metaParents_avoidance_explicit {n m M j : ℕ} (hm : 12 ≤ m) (hn : M * m ≤ n)
    (hj : j < M) (hlog : 0 < Real.logb 2 n) (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-(1 / (4 * Real.logb 2 n)) * ∑ u ∈ U, harmonicAt n v u)) (A : Finset (Fin M)) :
    (rowLaw m p j).probability (fun row => Disjoint (metaParents (by omega) hn j row) A) ≤
      Real.exp (-(m / (128 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt M j i) := by
  apply (metaParents_avoidance (by omega) hn hj p (by positivity) havoid A).trans
  apply Real.exp_le_exp.mpr
  have ht : m ≤ 4 * (m / 3) := by omega
  have htR : (m : ℝ) ≤ 4 * (m / 3 : ℕ) := by exact_mod_cast ht
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcoef : (m : ℝ) / (128 * Real.logb 2 n) ≤
      (1 / (4 * Real.logb 2 n)) * (m / 3 : ℕ) ^ 2 / (2 * m) := by
    field_simp
    nlinarith [sq_nonneg ((4 : ℝ) * (m / 3 : ℕ) - m)]
  have hw : 0 ≤ ∑ i ∈ A, harmonicAt M j i := by
    apply sum_nonneg
    intro i _
    unfold harmonicAt
    positivity
  exact mul_le_mul_of_nonneg_right (neg_le_neg hcoef) hw

end ProofOfSpace.DRSample

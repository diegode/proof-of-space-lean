import ProofOfSpace.DRSample.LawMap
import ProofOfSpace.DRSample.Sequential

/-! # Avoidance from independent parent draws -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem FiniteLaw.avoidance_of_weights {α : Type*} [Fintype α] (p : FiniteLaw α)
    (A : Finset α) (w : α → ℝ) (hw : ∀ a ∈ A, w a ≤ p.weight a) :
    p.probability (fun a => a ∉ A) ≤ Real.exp (-(∑ a ∈ A, w a)) := by
  have hhit : p.probability (fun a => a ∈ A) = ∑ a ∈ A, p.weight a := by
    unfold probability
    have hsub : (∑ a ∈ A, if a ∈ A then p.weight a else 0) =
        ∑ a, if a ∈ A then p.weight a else 0 :=
      sum_subset (subset_univ A) (fun a _ ha => if_neg ha)
    convert hsub.symm.trans (sum_congr rfl (fun a ha => if_pos ha)) using 1
    apply sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [probability_compl, hhit]
  have hsum := sum_le_sum hw
  have hexp := Real.add_one_le_exp (-(∑ a ∈ A, w a))
  linarith

def sampledParents {n d : ℕ} (v : ℕ) (draws : Fin d → Fin n) : Finset (Fin n) :=
  (univ.image draws) ∪ (univ.filter fun u => u.val + 1 = v)

theorem sampledParents_card {n d : ℕ} (v : ℕ) (draws : Fin d → Fin n) :
    (sampledParents v draws).card ≤ d + 1 := by
  have hline : (univ.filter (fun u : Fin n => u.val + 1 = v)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Fin.ext
    omega
  exact (card_union_le _ _).trans (Nat.add_le_add
    (by simpa using (card_image_le : (univ.image draws).card ≤ (univ : Finset (Fin d)).card)) hline)

theorem mem_sampledParents_line {n d : ℕ} {v : ℕ} (draws : Fin d → Fin n)
    (u : Fin n) (hu : u.val + 1 = v) : u ∈ sampledParents v draws :=
  mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hu⟩)

noncomputable def parentSetLaw {n : ℕ} (d v : ℕ) (p : FiniteLaw (Fin n)) :
    FiniteLaw (Finset (Fin n)) :=
  (FiniteLaw.pi (fun _ : Fin d => p)).map (sampledParents v)

theorem parentSetLaw_avoidance {n d v : ℕ} (p : FiniteLaw (Fin n))
    (A : Finset (Fin n)) (w : Fin n → ℝ) (hw : ∀ i ∈ A, w i ≤ p.weight i) :
    (parentSetLaw d v p).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(d : ℝ) * ∑ i ∈ A, w i) := by
  rw [parentSetLaw, FiniteLaw.probability_map]
  have hmono : (FiniteLaw.pi (fun _ : Fin d => p)).probability
      (fun draws => Disjoint (sampledParents v draws) A) ≤
      (FiniteLaw.pi (fun _ : Fin d => p)).probability (fun draws => ∀ k, draws k ∉ A) := by
    apply FiniteLaw.probability_mono
    intro draws h k hk
    apply (disjoint_left.mp h) _ hk
    exact mem_union_left _ (mem_image.mpr ⟨k, mem_univ _, rfl⟩)
  apply hmono.trans
  rw [FiniteLaw.probability_pi (fun _ : Fin d => p) (fun _ i => i ∉ A)]
  calc (∏ _ : Fin d, p.probability (fun i => i ∉ A))
      ≤ ∏ _ : Fin d, Real.exp (-(∑ i ∈ A, w i)) := by
        apply prod_le_prod
        · intro k _; exact p.probability_nonneg _
        · intro k _; exact p.avoidance_of_weights A w hw
    _ = Real.exp (-(d : ℝ) * ∑ i ∈ A, w i) := by
      simp only [prod_const, card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem parentSetLaw_avoidance_harmonic {n d v : ℕ} (p : FiniteLaw (Fin n))
    {c : ℝ} (hc : 0 ≤ c)
    (hkernel : ∀ i : Fin n, i.val + 2 ≤ v → c / (v - i.val : ℕ) ≤ p.weight i)
    (A : Finset (Fin n)) :
    (parentSetLaw d v p).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(d * c) * ∑ i ∈ A, harmonicAt n v i) := by
  by_cases hpred : ∃ i ∈ A, i.val + 1 = v
  · obtain ⟨i, hiA, hi⟩ := hpred
    rw [parentSetLaw, FiniteLaw.probability_map]
    have hnone : ∀ draws : Fin d → Fin n, ¬ Disjoint (sampledParents v draws) A := by
      intro draws h
      exact (disjoint_left.mp h) (mem_sampledParents_line draws i hi) hiA
    have heq : (FiniteLaw.pi (fun _ : Fin d => p)).probability
        (fun draws => Disjoint (sampledParents v draws) A) = 0 := by
      simp [FiniteLaw.probability, hnone]
    rw [heq]
    exact (Real.exp_pos _).le
  · have hw : ∀ i ∈ A, c * harmonicAt n v i ≤ p.weight i := by
      intro i hi
      unfold harmonicAt
      by_cases hiv : i.val < v
      · rw [if_pos hiv, ← mul_div_assoc, mul_one]
        apply hkernel i
        have hne : i.val + 1 ≠ v := fun he => hpred ⟨i, hi, he⟩
        omega
      · rw [if_neg hiv, mul_zero]
        exact p.nonneg i
    have h := parentSetLaw_avoidance (d := d) (v := v) p A (fun i => c * harmonicAt n v i) hw
    rw [← mul_sum] at h
    convert h using 1 <;> ring

end ProofOfSpace.DRSample

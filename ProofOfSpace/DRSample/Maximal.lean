import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # A discrete one-sided maximal inequality for deleted vertices -/
namespace ProofOfSpace.DRSample
open Finset Classical

/-- Endpoints of left intervals whose deletion density exceeds `1/c`. -/
noncomputable def leftDense (c : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (range n).filter fun j => ∃ i ≤ j, j + 1 - i < c * (S ∩ Ico i (j + 1)).card

/-- The one-sided maximal estimate is a disjoint-interval counting argument. -/
theorem card_leftDense_le (c : ℕ) (S : Finset ℕ) (n : ℕ) :
    (leftDense c S n).card ≤ c * S.card := by
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    rcases (leftDense c S n).eq_empty_or_nonempty with he | hne
    · simp [he]
    obtain ⟨j, hj, hmax⟩ := (leftDense c S n).exists_max_image id hne
    have hjn : j < n := mem_range.mp (mem_filter.mp hj).1
    obtain ⟨i, hij, hdense⟩ := (mem_filter.mp hj).2
    have hiN : i < n := hij.trans_lt hjn
    let pastDeleted := S ∩ range i
    have hcover : leftDense c S n ⊆ leftDense c pastDeleted i ∪ Ico i (j + 1) := by
      intro k hk
      have hkj : k ≤ j := hmax k hk
      by_cases hki : k < i
      · apply mem_union_left
        obtain ⟨l, hlk, hldense⟩ := (mem_filter.mp hk).2
        have hinter : pastDeleted ∩ Ico l (k + 1) = S ∩ Ico l (k + 1) := by
          ext x
          simp only [pastDeleted, mem_inter, mem_range, mem_Ico]
          constructor
          · rintro ⟨⟨hxS, _⟩, hxlo, hxhi⟩
            exact ⟨hxS, hxlo, hxhi⟩
          · rintro ⟨hxS, hxlo, hxhi⟩
            exact ⟨⟨hxS, by omega⟩, hxlo, hxhi⟩
        apply mem_filter.mpr
        refine ⟨mem_range.mpr hki, l, hlk, ?_⟩
        rwa [hinter]
      · apply mem_union_right
        exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hdisj : Disjoint pastDeleted (S ∩ Ico i (j + 1)) := by
      apply disjoint_left.mpr
      intro x hx hy
      have hxi : x < i := mem_range.mp (mem_inter.mp hx).2
      have hix : i ≤ x := (mem_Ico.mp (mem_inter.mp hy).2).1
      omega
    have hsub : pastDeleted ∪ (S ∩ Ico i (j + 1)) ⊆ S := by
      apply union_subset
      · exact inter_subset_left
      · exact inter_subset_left
    have hcards : pastDeleted.card + (S ∩ Ico i (j + 1)).card ≤ S.card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card hsub
    have hrec := ih i hiN pastDeleted
    calc (leftDense c S n).card ≤ (leftDense c pastDeleted i ∪ Ico i (j + 1)).card := card_le_card hcover
      _ ≤ (leftDense c pastDeleted i).card + (Ico i (j + 1)).card := card_union_le _ _
      _ ≤ c * pastDeleted.card + c * (S ∩ Ico i (j + 1)).card := by
        simpa only [Nat.card_Ico] using Nat.add_le_add hrec hdense.le
      _ ≤ c * S.card := by nlinarith

end ProofOfSpace.DRSample

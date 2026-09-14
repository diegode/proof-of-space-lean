import ProofOfSpace.DRSample.Registry

/-! # Sharper finite bounds by accounting for the overlap of exceptional sets

Every deleted vertex belongs to both one-sided dense sets. Subtracting that
intersection improves the good-vertex count from `n - 5|S|/2` to `n - 3|S|/2`.
This is the deterministic shallow-label estimate used in the revised appendix.
-/
namespace ProofOfSpace.DRSample
open Finset

theorem card_goodVerticesFourFifths_overlap {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) :
    2 * n ≤ 2 * (goodVerticesFourFifths S n).card + 3 * S.card := by
  have hleft := card_leftDenseFourFifths_le S n
  have hright := card_rightDenseFourFifths_le hS
  have hdeleted : S ⊆ leftDenseFourFifths S n ∩ rightDenseFourFifths S n := by
    intro j hj
    have hjn := mem_range.mp (hS hj)
    have hpos : 0 < (S ∩ Ico j (j + 1)).card := card_pos.mpr
      ⟨j, mem_inter.mpr ⟨hj, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
    apply mem_inter.mpr
    constructor
    · exact mem_filter.mpr ⟨hS hj, j, le_rfl, by omega⟩
    · exact mem_rightDenseFourFifths_of_interval (hi := j + 1) hS
        (by omega) (by omega) (by omega)
  have hi := card_le_card hdeleted
  have hu := card_union_add_card_inter (leftDenseFourFifths S n) (rightDenseFourFifths S n)
  have hs := card_sdiff_add_card_inter (range n)
    (leftDenseFourFifths S n ∪ rightDenseFourFifths S n)
  have hinter := card_le_card (inter_subset_right :
    range n ∩ (leftDenseFourFifths S n ∪ rightDenseFourFifths S n) ⊆
      leftDenseFourFifths S n ∪ rightDenseFourFifths S n)
  simp only [card_range] at hs
  change 2 * n ≤
    2 * (range n \ (leftDenseFourFifths S n ∪ rightDenseFourFifths S n)).card + 3 * S.card
  omega


/-- Sharper shallow-label bound at the same one-third deletion budget. -/
theorem shallow_labels_third_overlap {n d : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hn : 0 < n) (hsmall : S.card ≤ n / 3) (h : ℕ → ℕ)
    (hh : ∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) :
    (n : ℝ) / 2 * Real.exp (-20 * forbiddenMass (range n \ S) h / n) ≤ d := by
  have hsub : goodVerticesFourFifths S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨goodVerticesFourFifths_subset_range S n hj, goodVerticesFourFifths_survive hj⟩
  have hbound := depth_bound_of_inconsistent_mass
    (compressedHeight (range n \ S) h) 0 (range n \ S).card
    ((goodVerticesFourFifths S n).image (survivorRank (range n \ S)))
    (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      exact mem_Ico.mpr ⟨Nat.zero_le _, survivorRank_lt_card (hsub hj)⟩)
    d (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      rw [compressedHeight_rank (hsub hj)]
      exact hh j (hsub hj))
    ((n : ℝ) / 2) ((5 / 2 : ℝ) * forbiddenMass (range n \ S) h)
    (by positivity) (mul_nonneg (by norm_num) (forbiddenMass_nonneg _ _))
    (by
      rw [card_image_of_injOn ((survivorRank_injOn (range n \ S)).mono hsub)]
      have hc := card_goodVerticesFourFifths_overlap hS
      have hs : 3 * S.card ≤ n := by omega
      have hncard : n ≤ 2 * (goodVerticesFourFifths S n).card := by omega
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      simpa [mul_comm] using
        (show (n : ℝ) ≤ 2 * (goodVerticesFourFifths S n).card by exact_mod_cast hncard))
    (by nlinarith [goodFourFifths_compressed_mass_le hS h])
  convert hbound using 2
  congr 1
  ring

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.Compression
import ProofOfSpace.DRSample.LabelBound

/-! # Inconsistent mass before and after rank compression -/
namespace ProofOfSpace.DRSample
open Finset Classical

noncomputable def compressedHeight (U : Finset ℕ) (h : ℕ → ℕ) (r : ℕ) : ℕ :=
  (U.filter (fun i => survivorRank U i = r)).sup h

theorem compressedHeight_rank {U : Finset ℕ} {h : ℕ → ℕ} {i : ℕ} (hi : i ∈ U) :
    compressedHeight U h (survivorRank U i) = h i := by
  have heq : U.filter (fun j => survivorRank U j = survivorRank U i) = {i} := by
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · exact fun hh => survivorRank_injOn U hh.1 hi hh.2
    · intro he
      subst j
      exact ⟨hi, rfl⟩
  simp [compressedHeight, heq]

noncomputable def pairMass (h : ℕ → ℕ) (i j : ℕ) : ℝ :=
  if i < j ∧ h j ≤ h i then 1 / (j - i : ℕ) else 0

noncomputable def forbiddenMass (U : Finset ℕ) (h : ℕ → ℕ) : ℝ :=
  ∑ j ∈ U, ∑ i ∈ U, pairMass h i j

theorem pairMass_nonneg (h : ℕ → ℕ) (i j : ℕ) : 0 ≤ pairMass h i j := by
  unfold pairMass
  positivity

theorem forbiddenMass_nonneg (U : Finset ℕ) (h : ℕ → ℕ) : 0 ≤ forbiddenMass U h :=
  sum_nonneg fun j _ => sum_nonneg fun i _ => pairMass_nonneg h i j

theorem inconsistentCost_full (a : ℕ → ℝ) {N j : ℕ} (hj : j < N) :
    inconsistentCost a 0 N j =
      (∑ i ∈ range N, if i < j ∧ a j ≤ a i then (1 : ℝ) / (j - i : ℕ) else 0) +
      (∑ i ∈ range N, if j < i ∧ a i ≤ a j then (1 : ℝ) / (i - j : ℕ) else 0) := by
  have hl : (range N).filter (· < j) = Ico 0 j := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  have hr : (range N).filter (j < ·) = Ico (j + 1) N := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  unfold inconsistentCost
  rw [← hl, ← hr, sum_filter, sum_filter]
  congr 1 <;> apply sum_congr rfl <;> intro i hi <;> split_ifs <;> simp_all

/-- Reindex a cost on compressed ranks by the original surviving vertices. -/
theorem compressed_cost {U : Finset ℕ} (h : ℕ → ℕ) {j : ℕ} (hj : j ∈ U) :
    inconsistentCost (fun r => (compressedHeight U h r : ℝ)) 0 U.card (survivorRank U j) =
      (∑ i ∈ U, if i < j ∧ h j ≤ h i then
        (1 : ℝ) / (survivorRank U j - survivorRank U i : ℕ) else 0) +
      (∑ i ∈ U, if j < i ∧ h i ≤ h j then
        (1 : ℝ) / (survivorRank U i - survivorRank U j : ℕ) else 0) := by
  rw [inconsistentCost_full _ (survivorRank_lt_card hj), ← survivorRank_image U]
  rw [sum_image (survivorRank_injOn U), sum_image (survivorRank_injOn U)]
  congr 1 <;> apply sum_congr rfl <;> intro i hi
  · simp only [survivorRank_lt_iff hi hj, compressedHeight_rank hi,
      compressedHeight_rank hj, Nat.cast_le]
  · simp only [survivorRank_lt_iff hj hi, compressedHeight_rank hi,
      compressedHeight_rank hj, Nat.cast_le]

theorem good_compressed_cost_le {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (h : ℕ → ℕ) {j : ℕ} (hj : j ∈ goodVertices S n) :
    inconsistentCost (fun r => (compressedHeight (range n \ S) h r : ℝ)) 0
        (range n \ S).card (survivorRank (range n \ S) j) ≤
      2 * ((∑ i ∈ range n \ S, pairMass h i j) +
        ∑ i ∈ range n \ S, pairMass h j i) := by
  have hjU : j ∈ range n \ S := mem_sdiff.mpr
    ⟨goodVertices_subset_range S n hj, goodVertices_survive hj⟩
  rw [compressed_cost h hjU, mul_add, mul_sum, mul_sum]
  apply add_le_add
  · apply sum_le_sum
    intro i hi
    unfold pairMass
    split_ifs with hcond
    · simpa only [← mul_div_assoc, mul_one] using
        good_survivor_reciprocal hS hi hjU hcond.1 (Or.inr hj)
    · simp
  · apply sum_le_sum
    intro i hi
    unfold pairMass
    split_ifs with hcond
    · simpa only [← mul_div_assoc, mul_one] using
        good_survivor_reciprocal hS hjU hi hcond.1 (Or.inl hj)
    · simp

/-- Each forbidden pair can contribute at most once at either good endpoint. -/
theorem good_compressed_mass_le {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (h : ℕ → ℕ) :
    ∑ r ∈ (goodVertices S n).image (survivorRank (range n \ S)),
      inconsistentCost (fun r => (compressedHeight (range n \ S) h r : ℝ)) 0
        (range n \ S).card r ≤ 4 * forbiddenMass (range n \ S) h := by
  have hsub : goodVertices S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨goodVertices_subset_range S n hj, goodVertices_survive hj⟩
  rw [sum_image ((survivorRank_injOn (range n \ S)).mono hsub)]
  calc _ ≤ ∑ j ∈ goodVertices S n,
        2 * ((∑ i ∈ range n \ S, pairMass h i j) + ∑ i ∈ range n \ S, pairMass h j i) :=
      sum_le_sum fun j hj => good_compressed_cost_le hS h hj
    _ ≤ ∑ j ∈ range n \ S,
        2 * ((∑ i ∈ range n \ S, pairMass h i j) + ∑ i ∈ range n \ S, pairMass h j i) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      exact mul_nonneg (by norm_num) (add_nonneg
        (sum_nonneg fun i _ => pairMass_nonneg h i j)
        (sum_nonneg fun i _ => pairMass_nonneg h j i))
    _ = 4 * forbiddenMass (range n \ S) h := by
      rw [← mul_sum, sum_add_distrib]
      conv_lhs => arg 2; arg 2; rw [sum_comm]
      unfold forbiddenMass
      ring

/-- The shallow-label lemma with the deletion loss and all constants explicit. -/
theorem shallow_labels {n d : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hsmall : 12 * S.card < n) (h : ℕ → ℕ)
    (hh : ∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) :
    ((n - 12 * S.card : ℕ) : ℝ) *
      Real.exp (-4 * forbiddenMass (range n \ S) h / (n - 12 * S.card : ℕ)) ≤ d := by
  have hsub : goodVertices S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨goodVertices_subset_range S n hj, goodVertices_survive hj⟩
  apply depth_bound_of_inconsistent_mass (compressedHeight (range n \ S) h) 0
    (range n \ S).card ((goodVertices S n).image (survivorRank (range n \ S)))
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    exact mem_Ico.mpr ⟨Nat.zero_le _, survivorRank_lt_card (hsub hj)⟩
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    rw [compressedHeight_rank (hsub hj)]
    exact hh j (hsub hj)
  · exact_mod_cast Nat.sub_pos_of_lt hsmall
  · exact forbiddenMass_nonneg _ _
  · rw [card_image_of_injOn ((survivorRank_injOn (range n \ S)).mono hsub)]
    exact_mod_cast card_goodVertices_ge hS
  · exact good_compressed_mass_le hS h

end ProofOfSpace.DRSample

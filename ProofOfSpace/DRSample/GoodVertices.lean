import ProofOfSpace.DRSample.Maximal

/-! # Many vertices have low deletion density in every interval containing them -/
namespace ProofOfSpace.DRSample
open Finset Classical

def reflected (n : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun i => n - 1 - i)

theorem reflected_card {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    (reflected n S).card = S.card := by
  apply card_image_of_injOn
  intro i hi j hj heq
  have := mem_range.mp (hS hi)
  have := mem_range.mp (hS hj)
  dsimp only at heq
  omega

theorem reflected_inter_Ico {n lo hi : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) (hlohi : lo ≤ hi) (hhi : hi ≤ n) :
    reflected n (S ∩ Ico lo hi) = reflected n S ∩ Ico (n - hi) (n - lo) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hiS, rfl⟩ := mem_image.mp hj
    have his := (mem_inter.mp hiS).1
    have hii := mem_Ico.mp (mem_inter.mp hiS).2
    refine mem_inter.mpr ⟨mem_image.mpr ⟨i, his, rfl⟩, mem_Ico.mpr ?_⟩
    constructor <;> omega
  · intro hj
    obtain ⟨i, hiS, heq⟩ := mem_image.mp (mem_inter.mp hj).1
    have hin := mem_range.mp (hS hiS)
    have hji := mem_Ico.mp (mem_inter.mp hj).2
    refine mem_image.mpr ⟨i, mem_inter.mpr ⟨hiS, mem_Ico.mpr ?_⟩, heq⟩
    constructor <;> omega

/-- The right-directed maximal set, obtained by reflecting the left-directed one. -/
noncomputable def rightDense (c : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  reflected n (leftDense c (reflected n S) n)

theorem card_rightDense_le (c : ℕ) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    (rightDense c S n).card ≤ c * S.card := by
  have hsub : leftDense c (reflected n S) n ⊆ range n := filter_subset _ _
  rw [rightDense, reflected_card hsub]
  simpa [reflected_card hS] using card_leftDense_le c (reflected n S) n

theorem mem_rightDense_of_interval {c n j hi : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) (hj : j < hi) (hhi : hi ≤ n)
    (hdense : hi - j < c * (S ∩ Ico j hi).card) : j ∈ rightDense c S n := by
  have hjn : j < n := hj.trans_le hhi
  have hcard : (reflected n S ∩ Ico (n - hi) (n - j)).card = (S ∩ Ico j hi).card := by
    rw [← reflected_inter_Ico hS hj.le hhi]
    exact reflected_card (inter_subset_left.trans hS)
  apply mem_image.mpr
  refine ⟨n - 1 - j, ?_, by omega⟩
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (by omega), n - hi, by omega, ?_⟩
  have heq : n - 1 - j + 1 = n - j := by omega
  rw [heq, hcard]
  have hlen : n - j - (n - hi) = hi - j := by omega
  rwa [hlen]

/-- Vertices outside both one-sided exceptional sets. -/
noncomputable def goodVertices (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  range n \ (leftDense 6 S n ∪ rightDense 6 S n)

theorem goodVertices_subset_range (S : Finset ℕ) (n : ℕ) :
    goodVertices S n ⊆ range n := sdiff_subset

theorem card_goodVertices_ge {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    n - 12 * S.card ≤ (goodVertices S n).card := by
  have hleft := card_leftDense_le 6 S n
  have hright := card_rightDense_le 6 hS
  have hbad : (leftDense 6 S n ∪ rightDense 6 S n).card ≤ 12 * S.card := by
    have := card_union_le (leftDense 6 S n) (rightDense 6 S n)
    omega
  have hsplit := card_sdiff_add_card_inter (range n) (leftDense 6 S n ∪ rightDense 6 S n)
  have hinter := card_le_card (inter_subset_right :
    range n ∩ (leftDense 6 S n ∪ rightDense 6 S n) ⊆ leftDense 6 S n ∪ rightDense 6 S n)
  simp only [card_range] at hsplit
  change n - 12 * S.card ≤ (range n \ (leftDense 6 S n ∪ rightDense 6 S n)).card
  omega

theorem goodVertices_survive {n j : ℕ} {S : Finset ℕ} (hj : j ∈ goodVertices S n) : j ∉ S := by
  intro hjS
  have hjn : j < n := mem_range.mp (mem_sdiff.mp hj).1
  have hnot : j ∉ leftDense 6 S n := fun h => (mem_sdiff.mp hj).2 (mem_union_left _ h)
  apply hnot
  apply mem_filter.mpr
  refine ⟨mem_range.mpr hjn, j, le_rfl, ?_⟩
  have hpos : 0 < (S ∩ Ico j (j + 1)).card := card_pos.mpr
    ⟨j, mem_inter.mpr ⟨hjS, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
  omega

/-- Every interval containing a good vertex has deletion density at most one quarter. -/
theorem goodVertices_interval {n lo hi j : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hj : j ∈ goodVertices S n) (hlo : lo ≤ j) (hjhi : j < hi) (hhi : hi ≤ n) :
    4 * (S ∩ Ico lo hi).card ≤ hi - lo := by
  have hjn : j < n := mem_range.mp (mem_sdiff.mp hj).1
  have hnleft : j ∉ leftDense 6 S n := fun h => (mem_sdiff.mp hj).2 (mem_union_left _ h)
  have hnright : j ∉ rightDense 6 S n := fun h => (mem_sdiff.mp hj).2 (mem_union_right _ h)
  have hleft : 6 * (S ∩ Ico lo (j + 1)).card ≤ j + 1 - lo := by
    by_contra! h
    exact hnleft (mem_filter.mpr ⟨mem_range.mpr hjn, lo, hlo, h⟩)
  have hright : 6 * (S ∩ Ico j hi).card ≤ hi - j := by
    by_contra! h
    exact hnright (mem_rightDense_of_interval hS hjhi hhi h)
  have hcover : S ∩ Ico lo hi ⊆ (S ∩ Ico lo (j + 1)) ∪ (S ∩ Ico j hi) := by
    intro k hk
    have hkS := (mem_inter.mp hk).1
    have hki := mem_Ico.mp (mem_inter.mp hk).2
    by_cases hkj : k ≤ j
    · exact mem_union_left _ (mem_inter.mpr ⟨hkS, mem_Ico.mpr ⟨hki.1, by omega⟩⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hkS, mem_Ico.mpr ⟨by omega, hki.2⟩⟩)
  have hc : (S ∩ Ico lo hi).card ≤
      (S ∩ Ico lo (j + 1)).card + (S ∩ Ico j hi).card :=
    (card_le_card hcover).trans (card_union_le _ _)
  omega

end ProofOfSpace.DRSample

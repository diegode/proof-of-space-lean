import ProofOfSpace.DRSample.GoodVertices

/-! # Distances after removing holes -/
namespace ProofOfSpace.DRSample
open Finset Classical

def survivorRank (U : Finset ℕ) (v : ℕ) : ℕ := (U.filter (· < v)).card

theorem survivorRank_lt_card {U : Finset ℕ} {v : ℕ} (hv : v ∈ U) :
    survivorRank U v < U.card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨filter_subset _ _, ?_⟩
  intro heq
  have : v ∈ U.filter (· < v) := heq.symm ▸ hv
  exact (lt_irrefl v) (mem_filter.mp this).2

theorem survivorRank_sub {U : Finset ℕ} {i j : ℕ} (hij : i ≤ j) :
    survivorRank U j - survivorRank U i = (U ∩ Ico i j).card := by
  have heq : U.filter (· < j) = U.filter (· < i) ∪ (U ∩ Ico i j) := by
    ext x
    simp only [mem_filter, mem_union, mem_inter, mem_Ico]
    by_cases hx : x ∈ U <;> simp [hx] <;> omega
  have hdisj : Disjoint (U.filter (· < i)) (U ∩ Ico i j) := by
    apply disjoint_left.mpr
    intro x hx hy
    have := (mem_filter.mp hx).2
    have := (mem_Ico.mp (mem_inter.mp hy).2).1
    omega
  unfold survivorRank
  rw [heq, card_union_of_disjoint hdisj]
  omega

theorem survivorRank_strictMono {U : Finset ℕ} {i j : ℕ} (hi : i ∈ U) (hij : i < j) :
    survivorRank U i < survivorRank U j := by
  have hd := survivorRank_sub (U := U) hij.le
  have hp : 0 < (U ∩ Ico i j).card := card_pos.mpr
    ⟨i, mem_inter.mpr ⟨hi, mem_Ico.mpr ⟨le_rfl, hij⟩⟩⟩
  omega

theorem survivorRank_injOn (U : Finset ℕ) : Set.InjOn (survivorRank U) U := by
  intro i hi j hj heq
  rcases lt_trichotomy i j with hij | hij | hij
  · have := survivorRank_strictMono hi hij
    omega
  · exact hij
  · have := survivorRank_strictMono hj hij
    omega

theorem survivorRank_image (U : Finset ℕ) : U.image (survivorRank U) = range U.card := by
  apply eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (survivorRank_lt_card hi)
  · rw [card_range, card_image_of_injOn (survivorRank_injOn U)]

theorem survivorRank_lt_iff {U : Finset ℕ} {i j : ℕ} (hi : i ∈ U) (hj : j ∈ U) :
    survivorRank U i < survivorRank U j ↔ i < j := by
  refine ⟨fun h => ?_, survivorRank_strictMono hi⟩
  by_contra! hji
  rcases hji.eq_or_lt with he | hlt
  · subst j; omega
  · have := survivorRank_strictMono hj hlt
    omega

/-- Surviving and deleted vertices partition any interval inside the graph. -/
theorem survivor_interval_partition {n i j : ℕ} {S : Finset ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    ((range n \ S) ∩ Ico i j).card + (S ∩ Ico i j).card = j - i := by
  have heq : ((range n \ S) ∩ Ico i j) ∪ (S ∩ Ico i j) = Ico i j := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff, mem_range, mem_Ico]
    by_cases hx : x ∈ S <;> simp [hx] <;> omega
  have hdisj : Disjoint ((range n \ S) ∩ Ico i j) (S ∩ Ico i j) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp (mem_inter.mp hx).1).2 (mem_inter.mp hy).1
  rw [← card_union_of_disjoint hdisj, heq, Nat.card_Ico]

/-- At a good endpoint, erasing holes shrinks every distance by at most two. -/
theorem good_survivor_distance {n i j : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hi : i ∈ range n \ S) (hj : j ∈ range n \ S) (hij : i < j)
    (hgood : i ∈ goodVertices S n ∨ j ∈ goodVertices S n) :
    j - i ≤ 2 * (survivorRank (range n \ S) j - survivorRank (range n \ S) i) := by
  have hjn := mem_range.mp (mem_sdiff.mp hj).1
  have hdense : 4 * (S ∩ Ico i (j + 1)).card ≤ j + 1 - i := by
    rcases hgood with hg | hg
    · exact goodVertices_interval hS hg le_rfl (by omega) (by omega)
    · exact goodVertices_interval hS hg hij.le (by omega) (by omega)
  have hsub : S ∩ Ico i j ⊆ S ∩ Ico i (j + 1) := by
    intro x hx
    have hh := mem_Ico.mp (mem_inter.mp hx).2
    exact mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_Ico.mpr ⟨hh.1, by omega⟩⟩
  have hc := card_le_card hsub
  have hp := survivor_interval_partition (S := S) hij.le hjn.le
  rw [survivorRank_sub hij.le]
  omega

theorem good_survivor_reciprocal {n i j : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hi : i ∈ range n \ S) (hj : j ∈ range n \ S) (hij : i < j)
    (hgood : i ∈ goodVertices S n ∨ j ∈ goodVertices S n) :
    (1 : ℝ) / (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ)
      ≤ 2 / (j - i : ℕ) := by
  have hdist := good_survivor_distance hS hi hj hij hgood
  have hrank := survivorRank_strictMono hi hij
  have hp : (0 : ℝ) < (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hrank
  have hq : (0 : ℝ) < (j - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hij
  apply (div_le_div_iff₀ hp hq).mpr
  simpa using (show ((j - i : ℕ) : ℝ) ≤ 2 * (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ) by exact_mod_cast hdist)

end ProofOfSpace.DRSample

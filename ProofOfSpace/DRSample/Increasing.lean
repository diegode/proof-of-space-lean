import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # Increasing subsequences as finite sets of indices -/
namespace ProofOfSpace.DRSample
open Finset

/-- Indices, in their natural order, carry strictly increasing values. -/
def Increasing (a : ℕ → ℝ) (s : Finset ℕ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i < j → a i < a j

noncomputable def increasingCapacity (a : ℕ → ℝ) (s : Finset ℕ) : ℕ := by
  classical
  exact (s.powerset.filter (Increasing a)).sup Finset.card

theorem increasingCapacity_witness (a : ℕ → ℝ) (s : Finset ℕ) :
    ∃ t ⊆ s, Increasing a t ∧ t.card = increasingCapacity a s := by
  classical
  have he : (s.powerset.filter (Increasing a)).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨by simp, ?_⟩⟩
    simp [Increasing]
  obtain ⟨t, ht, hcard⟩ := exists_mem_eq_sup _ he Finset.card
  exact ⟨t, mem_powerset.mp (mem_filter.mp ht).1, (mem_filter.mp ht).2, hcard.symm⟩

theorem Increasing.card_le_capacity {a : ℕ → ℝ} {s t : Finset ℕ}
    (ht : Increasing a t) (hst : t ⊆ s) : t.card ≤ increasingCapacity a s := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hst, ht⟩)

theorem Increasing.ordered_union {a : ℕ → ℝ} {s t : Finset ℕ}
    (hs : Increasing a s) (ht : Increasing a t)
    (hst : ∀ i ∈ s, ∀ j ∈ t, i < j ∧ a i < a j) : Increasing a (s ∪ t) := by
  intro i hi j hj hij
  rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
  · exact hs i hi j hj hij
  · exact (hst i hi j hj).2
  · have := (hst j hj i hi).1
    omega
  · exact ht i hi j hj hij

theorem Increasing.injectiveOn {a : ℕ → ℝ} {s : Finset ℕ} (hs : Increasing a s) :
    Set.InjOn a s := by
  intro i hi j hj heq
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact False.elim ((hs i hi j hj hij).ne heq)
  · rfl
  · exact False.elim ((hs j hj i hi hji).ne heq.symm)

/-- Integer depth labels between one and `d` admit at most `d` increasing indices. -/
theorem increasingCapacity_nat_le (h : ℕ → ℕ) (s : Finset ℕ) (d : ℕ)
    (hh : ∀ i ∈ s, 1 ≤ h i ∧ h i ≤ d) :
    increasingCapacity (fun i => (h i : ℝ)) s ≤ d := by
  classical
  obtain ⟨t, hts, ht, hcard⟩ := increasingCapacity_witness (fun i => (h i : ℝ)) s
  have hinj : Set.InjOn h t := by
    intro i hi j hj heq
    apply ht.injectiveOn hi hj
    dsimp only
    exact_mod_cast heq
  have hsub : t.image h ⊆ Icc 1 d := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    exact mem_Icc.mpr (hh i (hts hi))
  calc increasingCapacity (fun i => (h i : ℝ)) s = t.card := hcard.symm
    _ = (t.image h).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc 1 d).card := card_le_card hsub
    _ = d := by simp

/-- Splitting at a pivot yields compatible increasing subsequences on the two
sides. The pivot itself is included exactly when it belongs to the target set. -/
theorem increasingCapacity_pivot (a : ℕ → ℝ) (s : Finset ℕ) (i : ℕ) :
    increasingCapacity a (s.filter fun j => j < i ∧ a j < a i) +
      increasingCapacity a (s.filter fun j => i < j ∧ a i < a j) +
      (if i ∈ s then 1 else 0) ≤ increasingCapacity a s := by
  classical
  obtain ⟨l, hl, hil, hcl⟩ := increasingCapacity_witness a
    (s.filter fun j => j < i ∧ a j < a i)
  obtain ⟨r, hr, hir, hcr⟩ := increasingCapacity_witness a
    (s.filter fun j => i < j ∧ a i < a j)
  have hlprop : ∀ j ∈ l, j ∈ s ∧ j < i ∧ a j < a i :=
    fun j hj => mem_filter.mp (hl hj)
  have hrprop : ∀ j ∈ r, j ∈ s ∧ i < j ∧ a i < a j :=
    fun j hj => mem_filter.mp (hr hj)
  have hlr : ∀ j ∈ l, ∀ k ∈ r, j < k ∧ a j < a k := by
    intro j hj k hk
    exact ⟨(hlprop j hj).2.1.trans (hrprop k hk).2.1,
      (hlprop j hj).2.2.trans (hrprop k hk).2.2⟩
  have hdisj : Disjoint l r := by
    apply disjoint_left.mpr
    intro j hj hk
    have := (hlr j hj j hk).1
    omega
  have hls : l ∪ r ⊆ s := union_subset
    (fun j hj => (hlprop j hj).1) (fun j hj => (hrprop j hj).1)
  have hiout : i ∉ l ∪ r := by
    intro hi
    rcases mem_union.mp hi with hi | hi
    · have := (hlprop i hi).2.1; omega
    · have := (hrprop i hi).2.1; omega
  rw [← hcl, ← hcr]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    have hic : Increasing a (insert i (l ∪ r)) := by
      intro j hj k hk hjk
      rcases mem_insert.mp hj with hjEq | hj
      · subst j
        rcases mem_insert.mp hk with rfl | hk
        · omega
        · rcases mem_union.mp hk with hk | hk
          · have := (hlprop k hk).2.1; omega
          · exact (hrprop k hk).2.2
      · rcases mem_insert.mp hk with hkEq | hk
        · subst k
          rcases mem_union.mp hj with hj | hj
          · exact (hlprop j hj).2.2
          · have := (hrprop j hj).2.1; omega
        · exact (hil.ordered_union hir hlr) j hj k hk hjk
    have := hic.card_le_capacity (insert_subset hi hls)
    simpa [card_insert_of_notMem hiout, card_union_of_disjoint hdisj] using this
  · rw [if_neg hi, add_zero]
    have := (hil.ordered_union hir hlr).card_le_capacity hls
    simpa [card_union_of_disjoint hdisj] using this

end ProofOfSpace.DRSample

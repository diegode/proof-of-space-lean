import ProofOfSpace.DRSample.Basic
import Mathlib.Tactic

/-! # Counting partition blocks touched by interval deletions -/
namespace ProofOfSpace.DRSample
open Finset
variable {n : ℕ}

/-- Indices of partition blocks meeting a deleted set, including the final
incomplete block when it is present. -/
def touched (m : ℕ) (S : Finset (Fin n)) : Finset ℕ :=
  S.image fun v => v.val / m

/-- An interval of at most `m` vertices meets only its endpoint's partition
block and possibly the immediately preceding block. -/
theorem block_index_alternatives {m b : ℕ} (hm : 0 < m) (hb : b ≤ m)
    {u v : Fin n} (huv : u ≤ v) (hvu : v.val < u.val + b) :
    u.val / m = v.val / m ∨ u.val / m = v.val / m - 1 := by
  have hlo : u.val / m ≤ v.val / m := Nat.div_le_div_right huv
  have hhi : v.val / m ≤ u.val / m + 1 := by
    calc v.val / m ≤ (u.val + m) / m := Nat.div_le_div_right (by omega)
      _ = u.val / m + 1 := Nat.add_div_right _ hm
  rcases eq_or_lt_of_le hlo with h | h
  · exact Or.inl h
  · right
    have heq := Nat.le_antisymm hhi (Nat.succ_le_iff.mpr h)
    rw [heq, Nat.add_sub_cancel]

/-- This bound is uniform over endpoint sets chosen after seeing the graph. -/
theorem card_touched_blockDeleted_le {m b : ℕ} (hm : 0 < m) (hb : b ≤ m)
    (S : Finset (Fin n)) : (touched m (blockDeleted b S)).card ≤ 2 * S.card := by
  classical
  have hsub : touched m (blockDeleted b S) ⊆
      S.image (fun v => v.val / m) ∪ S.image (fun v => v.val / m - 1) := by
    intro i hi
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
    obtain ⟨v, hv, huv, hvu⟩ := mem_blockDeleted.mp hu
    rcases block_index_alternatives hm hb huv hvu with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨v, hv, h.symm⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨v, hv, h.symm⟩)
  calc (touched m (blockDeleted b S)).card
      ≤ (S.image (fun v => v.val / m) ∪ S.image (fun v => v.val / m - 1)).card :=
        card_le_card hsub
    _ ≤ (S.image (fun v => v.val / m)).card +
        (S.image (fun v => v.val / m - 1)).card := card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add (card_image_le) (card_image_le)
    _ = 2 * S.card := by omega

/-- Restrict touched indices to the complete partition blocks. -/
def discardedBlocks (m M : ℕ) (S : Finset (Fin n)) : Finset (Fin M) :=
  univ.filter fun i => i.val ∈ touched m S

theorem card_discardedBlocks_le (m M : ℕ) (S : Finset (Fin n)) :
    (discardedBlocks m M S).card ≤ (touched m S).card := by
  classical
  calc (discardedBlocks m M S).card
      = ((discardedBlocks m M S).image Fin.val).card :=
        (card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (touched m S).card := by
      apply card_le_card
      intro i hi
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hi
      exact (mem_filter.mp hv).2

theorem card_discardedBlocks_blockDeleted_le {m b : ℕ} (hm : 0 < m) (hb : b ≤ m)
    (M : ℕ) (S : Finset (Fin n)) :
    (discardedBlocks m M (blockDeleted b S)).card ≤ 2 * S.card :=
  (card_discardedBlocks_le _ _ _).trans (card_touched_blockDeleted_le hm hb S)

end ProofOfSpace.DRSample

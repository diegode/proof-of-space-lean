import ProofOfSpace.DRSample.Height
import ProofOfSpace.DRSample.Blocks
import Mathlib.Tactic

/-! # Line edges inside intact blocks -/
namespace ProofOfSpace.DRSample
open Finset Classical

def HasLine {n : ℕ} (G : OrderedGraph n) : Prop :=
  ∀ u v : Fin n, u.val + 1 = v.val → G.edge u v

theorem height_along_line {n : ℕ} (G : OrderedGraph n) (hline : HasLine G)
    (D : Finset (Fin n)) (u v : Fin n) (huv : u ≤ v)
    (hclean : ∀ w : Fin n, u ≤ w → w ≤ v → w ∉ D) :
    height G D u + (v.val - u.val) ≤ height G D v := by
  have hstep : ∀ k, u.val ≤ k → k ≤ v.val → ∀ hk : k < n,
      height G D u + (k - u.val) ≤ height G D ⟨k, hk⟩ := by
    intro k huk
    induction k, huk using Nat.le_induction with
    | base =>
      intro _ hk
      have heq : (⟨u.val, hk⟩ : Fin n) = u := Fin.ext rfl
      simp [heq]
    | succ k huk ih =>
      intro hkv hk
      have hkn : k < n := by omega
      have hprev := ih (by omega) hkn
      have hedge : G.edge ⟨k, hkn⟩ ⟨k + 1, hk⟩ := hline _ _ rfl
      have hpos := height_lt_of_edge (hclean ⟨k + 1, hk⟩ (by change u.val ≤ k + 1; omega)
        (by exact hkv)) hedge
      omega
  exact hstep v.val huv le_rfl v.isLt

theorem intact_block_vertex {n m M : ℕ} (hm : 0 < m)
    (D : Finset (Fin n)) (i : Fin M) (hi : i ∉ discardedBlocks m M D)
    (v : Fin n) (hlo : i.val * m ≤ v.val) (hhi : v.val < (i.val + 1) * m) : v ∉ D := by
  intro hv
  apply hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, mem_image.mpr ⟨v, hv, ?_⟩⟩
  exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

/-- Positive increments along a chain imply a lower bound on its last height. -/
theorem chain_weight_bound {α : Type*} {R : α → α → Prop} (h : α → ℕ) (a : ℕ)
    (x : α) (xs : List α) (hc : (x :: xs).IsChain R)
    (hedge : ∀ u ∈ x :: xs, ∀ v ∈ x :: xs, R u v → h u + a ≤ h v) :
    ∃ v ∈ x :: xs, h x + a * xs.length ≤ h v := by
  induction xs generalizing x with
  | nil => exact ⟨x, by simp, by simp⟩
  | cons y ys ih =>
    have hxy : R x y := (List.isChain_cons_cons.mp hc).1
    have ht : (y :: ys).IsChain R := (List.isChain_cons_cons.mp hc).2
    have hsub : ∀ u ∈ y :: ys, u ∈ x :: y :: ys := fun u hu => List.mem_cons_of_mem x hu
    obtain ⟨v, hv, hvbound⟩ := ih y ht (fun u hu v hv => hedge u (hsub u hu) v (hsub v hv))
    refine ⟨v, hsub v hv, ?_⟩
    have hstep := hedge x (by simp) y (by simp) hxy
    simp only [List.length_cons]
    nlinarith

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.HeightLine

/-! # Lifting paths through intact partition blocks -/
namespace ProofOfSpace.DRSample
open Finset Classical

/-- An interblock edge leaves the last third and enters the first third. -/
def PortEdge {n M : ℕ} (G : OrderedGraph n) (m : ℕ) (i j : Fin M) : Prop :=
  ∃ u v : Fin n, G.edge u v ∧
    i.val * m + (m - m / 3) ≤ u.val ∧ u.val < (i.val + 1) * m ∧
    j.val * m ≤ v.val ∧ v.val < j.val * m + m / 3

def restrictedGraph {n : ℕ} (G : OrderedGraph n) (m M : ℕ) : OrderedGraph M where
  edge i j := i < j ∧ PortEdge G m i j
  increasing h := h.1

def blockMiddle {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n) (i : Fin M) : Fin n :=
  ⟨i.val * m + (m - m / 3), by
    have ht : 0 < m / 3 := by omega
    have hi := i.isLt
    have hmul : (i.val + 1) * m ≤ M * m := Nat.mul_le_mul_right m (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega⟩

theorem blockMiddle_clean {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (D : Finset (Fin n)) (i : Fin M) (hi : i ∉ discardedBlocks m M D) :
    blockMiddle hm hn i ∉ D := by
  apply intact_block_vertex (by omega) D i hi
  · dsimp [blockMiddle]; omega
  · dsimp [blockMiddle]
    have ht : 0 < m / 3 := by omega
    have hd : m - m / 3 < m := by omega
    nlinarith

theorem blockMiddle_height {n m M : ℕ} (G : OrderedGraph n) (hline : HasLine G)
    (hm : 3 ≤ m) (hn : M * m ≤ n) (D : Finset (Fin n))
    (i : Fin M) (hi : i ∉ discardedBlocks m M D) :
    m - 2 * (m / 3) ≤ height G D (blockMiddle hm hn i) := by
  have hstartn : i.val * m < n := by
    have := (blockMiddle hm hn i).isLt
    dsimp [blockMiddle] at this
    omega
  let u : Fin n := ⟨i.val * m, hstartn⟩
  have hu : u ∉ D := by
    apply intact_block_vertex (by omega) D i hi
    · exact le_rfl
    · dsimp [u]; nlinarith
  have hlinebound := height_along_line G hline D u (blockMiddle hm hn i)
    (by change i.val * m ≤ i.val * m + (m - m / 3); omega) (by
      intro w hwlo hwhi
      apply intact_block_vertex (by omega) D i hi
      · exact hwlo
      · have ht : 0 < m / 3 := by omega
        have hd : m - m / 3 < m := by omega
        change w.val ≤ i.val * m + (m - m / 3) at hwhi
        nlinarith)
  have hpos := height_pos (G := G) hu
  dsimp [u, blockMiddle] at hlinebound hpos ⊢
  omega

theorem blockMiddle_height_step {n m M : ℕ} (G : OrderedGraph n) (hline : HasLine G)
    (hm : 3 ≤ m) (hn : M * m ≤ n) (D : Finset (Fin n))
    (i j : Fin M) (hi : i ∉ discardedBlocks m M D) (hj : j ∉ discardedBlocks m M D)
    (hedge : PortEdge G m i j) :
    height G D (blockMiddle hm hn i) + (m - 2 * (m / 3)) ≤
      height G D (blockMiddle hm hn j) := by
  obtain ⟨u, v, huv, hu0, hu1, hv0, hv1⟩ := hedge
  have hfirst := height_along_line G hline D (blockMiddle hm hn i) u hu0 (by
    intro w hw0 hw1
    apply intact_block_vertex (by omega) D i hi
    · change i.val * m + (m - m / 3) ≤ w.val at hw0
      omega
    · exact lt_of_le_of_lt hw1 hu1)
  have hvD : v ∉ D := by
    apply intact_block_vertex (by omega) D j hj v hv0
    have ht : m / 3 ≤ m := Nat.div_le_self _ _
    nlinarith
  have hcross := height_lt_of_edge hvD huv
  have hlast := height_along_line G hline D v (blockMiddle hm hn j)
    (by change v.val ≤ j.val * m + (m - m / 3); omega) (by
      intro w hw0 hw1
      apply intact_block_vertex (by omega) D j hj
      · exact hv0.trans hw0
      · have ht : 0 < m / 3 := by omega
        have hd : m - m / 3 < m := by omega
        change w.val ≤ j.val * m + (m - m / 3) at hw1
        nlinarith)
  dsimp [blockMiddle] at hfirst hlast ⊢
  omega

/-- Every metagraph path gives at least one third of a block per visited vertex. -/
theorem lift_meta_path {n m M : ℕ} (G : OrderedGraph n) (H : OrderedGraph M)
    (hline : HasLine G) (hm : 3 ≤ m) (hn : M * m ≤ n)
    (hedges : ∀ i j, H.edge i j → PortEdge G m i j)
    (D : Finset (Fin n)) {d : ℝ} (hd : 0 < d)
    (hpath : HasPath H (discardedBlocks m M D) d) :
    HasPath G D ((m : ℝ) / 3 * d) := by
  obtain ⟨P, hne, hc, havoid, hlen⟩ := hpath
  cases P with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    obtain ⟨v, hv, hvbound⟩ := chain_weight_bound
      (fun i => height G D (blockMiddle hm hn i)) (m - 2 * (m / 3)) x xs hc (by
        intro i hi j hj hij
        exact blockMiddle_height_step G hline hm hn D i j
          (havoid i hi) (havoid j hj) (hedges i j hij))
    have hx := blockMiddle_height G hline hm hn D x (havoid x (by simp))
    have hpathnat : (m - 2 * (m / 3)) * (x :: xs).length ≤
        height G D (blockMiddle hm hn v) := by
      simp only [List.length_cons]
      nlinarith
    have hthird : (m : ℝ) / 3 ≤ ((m - 2 * (m / 3) : ℕ) : ℝ) := by
      have ht : 3 * (m / 3) ≤ m := by omega
      rw [Nat.cast_sub (by omega : 2 * (m / 3) ≤ m), Nat.cast_mul, Nat.cast_ofNat]
      have htR : (3 : ℝ) * (m / 3 : ℕ) ≤ m := by exact_mod_cast ht
      linarith
    apply hasPath_of_le_depth (by positivity : 0 < (m : ℝ) / 3 * d)
    calc (m : ℝ) / 3 * d ≤ ((m - 2 * (m / 3) : ℕ) : ℝ) * (x :: xs).length :=
        mul_le_mul hthird hlen hd.le (by positivity)
      _ ≤ height G D (blockMiddle hm hn v) := by exact_mod_cast hpathnat
      _ ≤ depth G D := by exact_mod_cast height_le_depth G D _

theorem blockDepthRobust_of_meta {n m M e b : ℕ} {d : ℝ}
    (G : OrderedGraph n) (H : OrderedGraph M) (hline : HasLine G)
    (hm : 3 ≤ m) (hn : M * m ≤ n) (hb : b ≤ m) (hd : 0 < d)
    (hedges : ∀ i j, H.edge i j → PortEdge G m i j)
    (he : 2 * e ≤ M / 48) (hH : DepthRobust H (M / 48) d) :
    BlockDepthRobust G e ((m : ℝ) / 3 * d) b := by
  intro S hS
  apply lift_meta_path G H hline hm hn hedges _ hd
  apply hH
  exact (card_discardedBlocks_blockDeleted_le (by omega) hb M S).trans (by omega)

end ProofOfSpace.DRSample

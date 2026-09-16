import ProofOfSpace.DRSample.PaperDefinitions
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Rev

/-! # From block depth robustness to fractional depth robustness

Theorem 4 of Blocki--Zhou (TCC 2017), with integer deletion budgets and
vertex-counting paths. A residue-class cover makes the final truncated block
explicit. Reversal gives both directional guarantees on the same graph.
-/
namespace ProofOfSpaceStatement
open Finset

theorem EndsLongPath.line_step {n : ℕ} {edge : Fin n → Fin n → Prop}
    (hline : ContainsLine edge) {D : Finset (Fin n)} {d : ℝ} {u v : Fin n}
    (hu : EndsLongPath edge D d u) (huv : u.val + 1 = v.val) (hv : v ∉ D) :
    EndsLongPath edge D d v := by
  obtain ⟨path, ⟨hchain, hclean⟩, hlast, hlen⟩ := hu
  refine ⟨path ++ [v], ⟨hchain.append (.singleton _) ?_, ?_⟩, by simp, ?_⟩
  · simpa [hlast] using hline u v huv
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hclean w hw
    · simpa using List.mem_singleton.mp hw ▸ hv
  · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    linarith

theorem EndsLongPath.line_interval {n : ℕ} {edge : Fin n → Fin n → Prop}
    (hline : ContainsLine edge) {D : Finset (Fin n)} {d : ℝ} {u v : Fin n}
    (hu : EndsLongPath edge D d u) (huv : u ≤ v)
    (hclean : ∀ w : Fin n, u ≤ w → w ≤ v → w ∉ D) :
    EndsLongPath edge D d v := by
  have hstep : ∀ k, u.val ≤ k → k ≤ v.val → ∀ hk : k < n,
      EndsLongPath edge D d ⟨k, hk⟩ := by
    intro k huk
    induction k, huk using Nat.le_induction with
    | base => intro _ hk; exact hu
    | succ k huk ih =>
      intro hkv hk
      exact (ih (by omega) (by omega)).line_step hline rfl
        (hclean ⟨k + 1, hk⟩ (by exact Nat.le_trans huk (Nat.le_succ k)) hkv)
  exact hstep v.val huv le_rfl v.isLt

/-- Every residue occurs within the next `b` positions, including the current one. -/
private theorem next_residue {b a : ℕ} (hb : 0 < b) (ha : a < b) (u : ℕ) :
    ∃ v, u ≤ v ∧ v < u + b ∧ v % b = a := by
  have hm := Nat.mod_lt u hb
  have hs := Nat.mod_add_div u b
  by_cases h : u % b ≤ a
  · refine ⟨a + b * (u / b), by omega, by omega, ?_⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
  · refine ⟨a + b * (u / b) + b, by omega, by omega, ?_⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt ha]

open Classical in
/-- The terminal vertices of long paths are covered by the deleted vertices,
one residue class of terminal vertices, and the last (possibly partial) block. -/
private theorem cover_long_ends {n b : ℕ} (hn : 0 < n) (hb : 0 < b)
    {edge : Fin n → Fin n → Prop} (hline : ContainsLine edge)
    (D : Finset (Fin n)) (d : ℝ) {a : ℕ} (ha : a < b) :
    let R := univ.filter (EndsLongPath edge D d)
    let T := D ∪ R.filter (fun v => v.val % b = a) ∪ {⟨n - 1, by omega⟩}
    ∀ u, u ∈ D ∨ EndsLongPath edge D d u →
      ∃ v ∈ T, u ≤ v ∧ v.val < u.val + b := by
  classical
  dsimp only
  intro u hu
  rcases hu with hu | hu
  · exact ⟨u, mem_union_left _ (mem_union_left _ hu), le_rfl, by omega⟩
  obtain ⟨v, huv, hvb, hva⟩ := next_residue hb ha u.val
  let w : Fin n := ⟨min v (n - 1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
  have huw : u ≤ w := by change u.val ≤ min v (n - 1); omega
  have hwb : w.val < u.val + b := (min_le_left _ _).trans_lt hvb
  by_cases hD : ∃ z : Fin n, u ≤ z ∧ z ≤ w ∧ z ∈ D
  · obtain ⟨z, huz, hzw, hzD⟩ := hD
    exact ⟨z, mem_union_left _ (mem_union_left _ hzD), huz,
      lt_of_le_of_lt hzw hwb⟩
  · have hw := hu.line_interval hline huw (by
      intro z huz hzw hzD
      exact hD ⟨z, huz, hzw, hzD⟩)
    refine ⟨w, ?_, huw, hwb⟩
    by_cases hvn : v < n
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hw⟩,
        by change (min v (n - 1)) % b = a; rwa [min_eq_left (by omega)]⟩
    · apply mem_union_right
      simp only [mem_singleton, Fin.ext_iff]
      exact min_eq_right (by omega)

open Classical in
/-- The number of vertices ending long paths after at most `⌊e/2⌋` deletions. -/
theorem block_to_fractional_ends {n e b : ℕ} {edge : Fin n → Fin n → Prop}
    (hline : ContainsLine edge) (hb : 1 ≤ b) (hbn : b ≤ n) {d : ℝ}
    (hrobust : GraphBlockDepthRobust edge e d b)
    (D : Finset (Fin n)) (hD : D.card ≤ e / 2) :
    (e : ℝ) * b / 2 ≤ ((univ.filter (EndsLongPath edge D d)).card : ℝ) := by
  classical
  let R := univ.filter (EndsLongPath edge D d)
  by_contra! hsmall
  have havg : (R.card : ℝ) < (range b).card • ((e : ℝ) / 2) := by
    calc
      _ < (e : ℝ) * b / 2 := hsmall
      _ = _ := by simp only [card_range, nsmul_eq_mul]; ring
  obtain ⟨a, ha, hcount⟩ := exists_card_fiber_lt_of_card_lt_nsmul
    (f := fun v : Fin n => v.val % b) havg
  have ha : a < b := mem_range.mp ha
  let Q := R.filter (fun v => v.val % b = a)
  have hcountNat : 2 * Q.card < e := by
    have : (2 : ℝ) * Q.card < e := by change (Q.card : ℝ) < (e : ℝ) / 2 at hcount; linarith
    exact_mod_cast this
  let last : Fin n := ⟨n - 1, by omega⟩
  let T := D ∪ Q ∪ {last}
  have hcard : T.card ≤ e := by
    have hc : T.card ≤ D.card + Q.card + 1 :=
      (card_union_le _ _).trans (by simpa using Nat.add_le_add_right (card_union_le D Q) 1)
    omega
  obtain ⟨path, hne, hchain, havoid, hlen⟩ := hrobust T hcard
  have hcover := cover_long_ends (by omega : 0 < n) (by omega : 0 < b) hline D d ha
  have hclean : ∀ u ∈ path, u ∉ D := by
    intro u hu huD
    obtain ⟨v, hv, huv⟩ := hcover u (Or.inl huD)
    exact havoid u hu v hv huv
  let u := path.getLast hne
  have hu : u ∈ path := List.getLast_mem hne
  have hlong : EndsLongPath edge D d u :=
    ⟨path, ⟨hchain, hclean⟩, List.getLast?_eq_some_getLast hne, hlen⟩
  obtain ⟨v, hv, huv⟩ := hcover u (Or.inr hlong)
  exact havoid u hu v hv huv

/-- Paper result `thm:block-to-fractional` (Blocki--Zhou, Theorem 4). -/
theorem block_to_fractional {n e b : ℕ} {edge : Fin n → Fin n → Prop}
    (_hordered : IsOrdered edge) (hline : ContainsLine edge)
    (hb : 1 ≤ b) (hbn : b ≤ n) {d : ℝ} (_hd : 0 < d)
    (hrobust : GraphBlockDepthRobust edge e d b) :
    FractionalDepthRobust edge (e / 2) d 0 ((e : ℝ) * b / (2 * n)) := by
  classical
  intro D hD
  refine ⟨by simp, ?_⟩
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have heq : (e : ℝ) * b / (2 * n) * n = (e : ℝ) * b / 2 := by field_simp
  rw [heq]
  exact block_to_fractional_ends hline hb hbn hrobust D hD

/-- Reverse the edges and the topological order. -/
def reverseEdge {n : ℕ} (edge : Fin n → Fin n → Prop) (u v : Fin n) : Prop :=
  edge v.rev u.rev

theorem IsOrdered.reverse {n : ℕ} {edge : Fin n → Fin n → Prop}
    (h : IsOrdered edge) : IsOrdered (reverseEdge edge) := by
  intro u v huv
  exact Fin.rev_lt_rev.mp (h _ _ huv)

theorem ContainsLine.reverse {n : ℕ} {edge : Fin n → Fin n → Prop}
    (h : ContainsLine edge) : ContainsLine (reverseEdge edge) := by
  intro u v huv
  apply h
  simp only [Fin.val_rev]
  omega

/-- A backward block in the reversed order is contained in a backward block
of the same width in the original order, including at the two boundaries. -/
theorem GraphBlockDepthRobust.reverse {n e b : ℕ} {edge : Fin n → Fin n → Prop}
    {d : ℝ} (h : GraphBlockDepthRobust edge e d b) (hb : 1 ≤ b) :
    GraphBlockDepthRobust (reverseEdge edge) e d b := by
  classical
  intro T hT
  let endpoint (v : Fin n) : Fin n :=
    ⟨min (n - 1) (v.rev.val + b - 1),
      lt_of_le_of_lt (min_le_left _ _) (by have := v.isLt; omega)⟩
  obtain ⟨path, hne, hchain, hclean, hlen⟩ := h (T.image endpoint) (card_image_le.trans hT)
  refine ⟨path.reverse.map Fin.rev, by simpa, ?_, ?_, by simpa⟩
  · simpa only [List.isChain_map, reverseEdge, Fin.rev_rev, List.isChain_reverse] using hchain
  · intro u hu v hv huv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    have hwpath := List.mem_reverse.mp hw
    apply hclean w hwpath (endpoint v) (mem_image.mpr ⟨v, hv, rfl⟩)
    have hvn := v.isLt
    have hwn := w.isLt
    change w.val ≤ min (n - 1) (v.rev.val + b - 1) ∧
      min (n - 1) (v.rev.val + b - 1) < w.val + b
    simp only [Fin.le_def, Fin.val_rev] at huv ⊢
    omega

theorem EndsLongPath.reverse {n : ℕ} {edge : Fin n → Fin n → Prop}
    {D : Finset (Fin n)} {d : ℝ} {v : Fin n}
    (h : EndsLongPath (reverseEdge edge) (D.image Fin.rev) d v) :
    StartsLongPath edge D d v.rev := by
  obtain ⟨path, ⟨hchain, hclean⟩, hlast, hlen⟩ := h
  refine ⟨path.reverse.map Fin.rev, ⟨?_, ?_⟩, ?_, by simpa⟩
  · rw [List.isChain_map, List.isChain_reverse]
    exact hchain
  · intro u hu huD
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact hclean w (List.mem_reverse.mp hw)
      (mem_image.mpr ⟨w.rev, huD, by simp⟩)
  · simp [List.head?_reverse, hlast]

/-- Both directional guarantees follow deterministically from one block
robustness guarantee; no union bound over two random events is needed. -/
theorem GraphBlockDepthRobust.fractional {n e b : ℕ} {edge : Fin n → Fin n → Prop}
    {d : ℝ}
    (h : GraphBlockDepthRobust edge e d b) (hline : ContainsLine edge)
    (hb : 1 ≤ b) (hbn : b ≤ n) :
    FractionalDepthRobust edge (e / 2) d
      ((e : ℝ) * b / (2 * n)) ((e : ℝ) * b / (2 * n)) := by
  classical
  intro D hD
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have heq : (e : ℝ) * b / (2 * n) * n = (e : ℝ) * b / 2 := by field_simp
  rw [heq]
  refine ⟨?_, block_to_fractional_ends hline hb hbn h D hD⟩
  have hDrev : (D.image Fin.rev).card ≤ e / 2 := card_image_le.trans hD
  have hends := block_to_fractional_ends hline.reverse hb hbn (h.reverse hb)
    (D.image Fin.rev) hDrev
  apply hends.trans
  apply Nat.cast_le.mpr
  rw [← card_image_of_injective _ Fin.rev_injective]
  apply card_le_card
  intro u hu
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2.reverse⟩

theorem FractionalDepthRobust.mono {n e e' : ℕ} {edge : Fin n → Fin n → Prop}
    {d d' fPlus fMinus fPlus' fMinus' : ℝ}
    (h : FractionalDepthRobust edge e d fPlus fMinus)
    (he : e' ≤ e) (hd : d' ≤ d) (hp : fPlus' ≤ fPlus) (hm : fMinus' ≤ fMinus) :
    FractionalDepthRobust edge e' d' fPlus' fMinus' := by
  classical
  intro D hD
  obtain ⟨hplus, hminus⟩ := h D (hD.trans he)
  constructor
  · apply (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n)).trans (hplus.trans _)
    apply Nat.cast_le.mpr (card_le_card _)
    intro v hv
    obtain ⟨path, hpath, hhead, hlen⟩ := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, path, hpath, hhead, hd.trans hlen⟩
  · apply (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg n)).trans (hminus.trans _)
    apply Nat.cast_le.mpr (card_le_card _)
    intro v hv
    obtain ⟨path, hpath, hlast, hlen⟩ := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, path, hpath, hlast, hd.trans hlen⟩

end ProofOfSpaceStatement

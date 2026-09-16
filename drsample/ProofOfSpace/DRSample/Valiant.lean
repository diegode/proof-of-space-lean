import ProofOfSpace.DRSample.PaperDefinitions
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Powerset

/-! # Valiant's depth reduction

Split ordered edges according to their highest differing binary digit. After
deleting the destinations of edges in `k` classes, the remaining binary digits
strictly increase along a path, leaving at most `2^(h-k)` vertices on it.
Choosing the `k` least expensive classes gives the exact deletion budget.
-/
namespace ProofOfSpace.DRSample.Valiant
open Finset

/-- Lexicographic order with the larger index taking precedence. -/
def BitsLT {α : Type*} [LinearOrder α] (f g : α → Bool) : Prop :=
  ∃ i, f i = false ∧ g i = true ∧ ∀ j, i < j → f j = g j

instance {α : Type*} [LinearOrder α] : Trans (@BitsLT α _) BitsLT BitsLT where
  trans := by
    intro f g h ⟨i, hfi, hgi, hfg⟩ ⟨j, hgj, hhj, hgh⟩
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ⟨j, (hfg j hij).trans hgj, hhj,
        fun l hjl => (hfg l (hij.trans hjl)).trans (hgh l hjl)⟩
    · subst j
      simp [hgi] at hgj
    · exact ⟨i, hfi, (hgh i hij).symm.trans hgi,
        fun l hil => (hfg l hil).trans (hgh l (hij.trans hil))⟩

instance {α : Type*} [LinearOrder α] : Std.Irrefl (@BitsLT α _) where
  irrefl := by
    rintro f ⟨i, hfalse, htrue, _⟩
    simp [hfalse] at htrue

theorem highest_difference {u v h : ℕ} (huv : u < v) (hv : v < 2 ^ h) :
    ∃ i : Fin h, u.testBit i.val = false ∧ v.testBit i.val = true ∧
      ∀ j, i.val < j → u.testBit j = v.testBit j := by
  obtain ⟨i, hi, hhigh⟩ := Nat.exists_most_significant_bit
    (Nat.xor_ne_zero_iff.mpr (Nat.ne_of_lt huv))
  have heq (j : ℕ) (hij : i < j) : u.testBit j = v.testBit j := by
    have hh := hhigh j hij
    rw [Nat.testBit_xor] at hh
    cases huj : u.testBit j <;> cases hvj : v.testBit j <;> simp_all
  have hbits : u.testBit i = false ∧ v.testBit i = true := by
    rw [Nat.testBit_xor] at hi
    cases hui : u.testBit i <;> cases hvi : v.testBit i <;> simp_all
    exact (Nat.lt_asymm huv (Nat.lt_of_testBit i hvi hui (fun j hj => (heq j hj).symm))).elim
  have hih : i < h := by
    by_contra! hle
    have hv' : v < 2 ^ i := hv.trans_le (Nat.pow_le_pow_right (by omega) hle)
    have hh := Nat.testBit_eq_false_of_lt hv'
    simp [hh] at hbits
  exact ⟨⟨i, hih⟩, hbits.1, hbits.2, heq⟩

/-- A subset of prescribed size containing the smallest weights. -/
theorem smallest_subset {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℕ)
    (k : ℕ) (hk : k ≤ s.card) :
    ∃ T ⊆ s, T.card = k ∧ ∀ i ∈ T, ∀ j ∈ s, j ∉ T → w i ≤ w j := by
  induction k generalizing s with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha, hmin⟩ := s.exists_min_image w (card_pos.mp (by omega))
    obtain ⟨T, hTs, hTk, hTmin⟩ := ih (s.erase a) (by rw [card_erase_of_mem ha]; omega)
    have haT : a ∉ T := fun h => (mem_erase.mp (hTs h)).1 rfl
    refine ⟨insert a T, insert_subset ha (hTs.trans (erase_subset _ _)), by simp [haT, hTk], ?_⟩
    intro i hi j hj hjT
    rcases mem_insert.mp hi with rfl | hi
    · exact hmin j hj
    · exact hTmin i hi j (mem_erase.mpr ⟨by aesop, hj⟩) (by aesop)

/-- The `k` smallest classes have at most `k/h` of the total weight. -/
theorem small_classes {h k : ℕ} (hk : k ≤ h) (w : Fin h → ℕ) :
    ∃ T : Finset (Fin h), T.card = k ∧ h * (∑ i ∈ T, w i) ≤ k * ∑ i, w i := by
  classical
  obtain ⟨T, _, hTk, hTmin⟩ := smallest_subset univ w k (by simpa)
  refine ⟨T, hTk, ?_⟩
  have hcross : ∑ i ∈ T, ∑ j ∈ Tᶜ, w i ≤ ∑ i ∈ T, ∑ j ∈ Tᶜ, w j := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    exact hTmin i hi j (mem_univ _) (mem_compl.mp hj)
  simp only [sum_const, nsmul_eq_mul, ← mul_sum, card_compl, Fintype.card_fin, hTk] at hcross
  norm_cast at hcross
  have htotal := sum_add_sum_compl T w
  calc
    h * (∑ i ∈ T, w i) = (h - k) * (∑ i ∈ T, w i) + k * (∑ i ∈ T, w i) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hk]
    _ ≤ k * (∑ i ∈ Tᶜ, w i) + k * (∑ i ∈ T, w i) := Nat.add_le_add_right hcross _
    _ = k * ∑ i, w i := by rw [← Nat.mul_add, add_comm, htotal]

/-- A chosen binary level for each ordered edge. -/
noncomputable def edgeLevel {n h : ℕ} (hn : n ≤ 2 ^ h) (hh : 0 < h)
    (u v : Fin n) : Fin h :=
  if huv : u < v then (highest_difference huv (v.isLt.trans_le hn)).choose else ⟨0, hh⟩

theorem edgeLevel_spec {n h : ℕ} (hn : n ≤ 2 ^ h) (hh : 0 < h)
    {u v : Fin n} (huv : u < v) :
    u.val.testBit (edgeLevel hn hh u v).val = false ∧
    v.val.testBit (edgeLevel hn hh u v).val = true ∧
    ∀ j, (edgeLevel hn hh u v).val < j → u.val.testBit j = v.val.testBit j := by
  simpa only [edgeLevel, dif_pos huv] using
    (highest_difference huv (v.isLt.trans_le hn)).choose_spec

theorem path_length {n h : ℕ} (hn : n ≤ 2 ^ h) (hh : 0 < h)
    (T : Finset (Fin h)) {edge : Fin n → Fin n → Prop}
    (hordered : ProofOfSpaceStatement.IsOrdered edge) (path : List (Fin n))
    (hpath : path.IsChain edge)
    (havoid : ∀ u ∈ path, ∀ v ∈ path, edge u v → edgeLevel hn hh u v ∉ T) :
    path.length ≤ 2 ^ (h - T.card) := by
  classical
  let code (v : Fin n) : ↥(Tᶜ : Finset (Fin h)) → Bool := fun i => v.val.testBit i.val.val
  have hchain : (path.map code).IsChain BitsLT := by
    rw [List.isChain_map]
    apply hpath.imp_of_mem_imp
    intro u v hu hv huv
    obtain ⟨hui, hvi, hhigh⟩ := edgeLevel_spec hn hh (hordered u v huv)
    let i : ↥(Tᶜ : Finset (Fin h)) :=
      ⟨edgeLevel hn hh u v, mem_compl.mpr (havoid u hu v hv huv)⟩
    exact ⟨i, hui, hvi, fun j hij => hhigh j.val.val hij⟩
  have hlen := hchain.pairwise.nodup.length_le_card
  simpa only [List.length_map, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, Fintype.card_fin] using hlen

end ProofOfSpace.DRSample.Valiant

namespace ProofOfSpaceStatement
open Finset ProofOfSpace.DRSample.Valiant

/-- Paper result `thm:valiant-depth-reduction`. The natural division is the
floor of `Δ n k / h`, with `h = ⌈log₂ n⌉`. Vertices are in topological order. -/
theorem valiant_depth_reduction {n Δ : ℕ} (hn : 2 ≤ n) (_hΔ : 2 ≤ Δ)
    {edge : Fin n → Fin n → Prop} (hordered : IsOrdered edge)
    (hdegree : IndegreeAtMost edge Δ) {k : ℕ} (hk : k < Nat.clog 2 n) :
    ∃ S : Finset (Fin n), S.card ≤ Δ * n * k / Nat.clog 2 n ∧
      DepthAtMost edge S (2 ^ (Nat.clog 2 n - k)) := by
  classical
  let h := Nat.clog 2 n
  have hh : 0 < h := Nat.clog_pos (by norm_num) (by omega)
  have hpow : n ≤ 2 ^ h := Nat.le_pow_clog (by norm_num) n
  let E := (univ : Finset (Fin n × Fin n)).filter (fun uv => edge uv.1 uv.2)
  let level (uv : Fin n × Fin n) := edgeLevel hpow hh uv.1 uv.2
  let w (i : Fin h) := (E.filter (fun uv => level uv = i)).card
  have hsum : ∑ i, w i = E.card :=
    (card_eq_sum_card_fiberwise (s := E) (t := univ) (f := level)
      (fun _ _ => mem_univ _)).symm
  have hE : E.card ≤ Δ * n := by
    calc
      E.card = ∑ v : Fin n, (univ.filter (fun u => edge u v)).card := by
        simp only [E, card_filter, Fintype.sum_prod_type]
        rw [sum_comm]
      _ ≤ ∑ _v : Fin n, Δ := sum_le_sum (fun v _ => hdegree v)
      _ = Δ * n := by simp [mul_comm]
  obtain ⟨T, hTk, hTcost⟩ := small_classes hk.le w
  let selected := E.filter (fun uv => level uv ∈ T)
  let S := selected.image Prod.snd
  have hselected : selected.card = ∑ i ∈ T, w i := by
    rw [card_eq_sum_card_fiberwise (s := selected) (t := T) (f := level)
      (fun _ huv => (mem_filter.mp huv).2)]
    apply sum_congr rfl
    intro i hi
    congr 1
    ext uv
    simp only [selected, mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2 ▸ hi⟩, h.2⟩
  refine ⟨S, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le hh).mpr
    have hS : S.card ≤ ∑ i ∈ T, w i := card_image_le.trans_eq hselected
    rw [hsum] at hTcost
    nlinarith [Nat.mul_le_mul_left h hS, Nat.mul_le_mul_left k hE]
  · intro path ⟨hpath, hclean⟩
    rw [← hTk]
    apply path_length hpow hh T hordered path hpath
    intro u _ v hv huv hlevel
    exact hclean v hv (mem_image.mpr ⟨(u, v),
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, huv⟩, hlevel⟩, rfl⟩)

end ProofOfSpaceStatement

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop

/-! # Layered DAGs, static pebblings, and unpebbled paths

The graph model is independent of any expansion calculus or search certificate.
-/
namespace ProofOfSpace
namespace Concrete
open Finset Set
universe u
variable {V : Type u}

/-- S nonempty directed path whose nodes are all unpebbled.  `List.IsChain` checks
adjacency of consecutive nodes. -/
structure Path (E : V → V → Prop) (unpebbled : V → Prop) where
  nodes : List V
  nonempty : nodes ≠ []
  chain : nodes.IsChain E
  unpebbled' : ∀ v ∈ nodes, unpebbled v

namespace Path

variable {E : V → V → Prop} {unpebbled : V → Prop}

def first (P : Path E unpebbled) : V := P.nodes.head P.nonempty

def last (P : Path E unpebbled) : V := P.nodes.getLast P.nonempty

def length (P : Path E unpebbled) : ℕ := P.nodes.length

theorem length_pos (P : Path E unpebbled) : 0 < P.length :=
  Nat.pos_of_ne_zero fun h => P.nonempty (List.eq_nil_of_length_eq_zero h)

theorem first_mem (P : Path E unpebbled) : P.first ∈ P.nodes :=
  List.head_mem P.nonempty

theorem last_mem (P : Path E unpebbled) : P.last ∈ P.nodes :=
  List.getLast_mem P.nonempty

/-- The one-node path. -/
def singleton (v : V) (hv : unpebbled v) : Path E unpebbled where
  nodes := [v]
  nonempty := by simp
  chain := .singleton v
  unpebbled' := by simpa

/-- Concatenate paths sharing an endpoint, retaining the common endpoint once. -/
noncomputable def append (P Q : Path E unpebbled) (h : P.last = Q.first) : Path E unpebbled where
  nodes := P.nodes.dropLast ++ Q.nodes
  nonempty := by
    intro hempty
    exact Q.nonempty (List.eq_nil_of_append_eq_nil hempty).2
  chain := by
    have hP : P.nodes.dropLast ++ [P.last] = P.nodes :=
      List.dropLast_append_getLast P.nonempty
    have hQ : Q.first :: Q.nodes.tail = Q.nodes :=
      List.cons_head_tail Q.nonempty
    have hc1 : (P.nodes.dropLast ++ [P.last]).IsChain E := by
      rw [hP]
      exact P.chain
    have hc2 : ([P.last] ++ Q.nodes.tail).IsChain E := by
      rw [h]
      change (Q.first :: Q.nodes.tail).IsChain E
      rw [hQ]
      exact Q.chain
    have := hc1.append_overlap hc2 (by simp)
    change (P.nodes.dropLast ++ Q.nodes).IsChain E
    rw [← hQ, ← h]
    simpa only [List.singleton_append, List.append_assoc] using this
  unpebbled' := by
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with hv | hv
    · exact P.unpebbled' v (List.mem_of_mem_dropLast hv)
    · exact Q.unpebbled' v hv

@[simp] theorem append_length (P Q : Path E unpebbled) (h : P.last = Q.first) :
    (P.append Q h).length = P.length + Q.length - 1 := by
  simp only [append, length, List.length_append]
  rw [List.length_dropLast]
  have := P.length_pos
  simp only [length] at this
  omega


@[simp] theorem append_first (P Q : Path E unpebbled) (h : P.last = Q.first) :
    (P.append Q h).first = P.first := by
  have hopen : (P.append Q h).nodes.head? = P.nodes.head? := by
    change (P.nodes.dropLast ++ Q.nodes).head? = P.nodes.head?
    rcases hP : P.nodes with _ | ⟨a, l⟩
    · exact absurd hP P.nonempty
    · cases l with
      | nil =>
          change Q.nodes.head? = some a
          rw [List.head?_eq_some_head Q.nonempty]
          simpa [Path.last, Path.first, hP] using h.symm
      | cons b l => simp
  have hleft := List.head?_eq_some_head (P.append Q h).nonempty
  have hright := List.head?_eq_some_head P.nonempty
  exact Option.some.inj (hleft.symm.trans (hopen.trans hright))

@[simp] theorem append_last (P Q : Path E unpebbled) (h : P.last = Q.first) :
    (P.append Q h).last = Q.last := by
  have hopen : (P.append Q h).nodes.getLast? = Q.nodes.getLast? := by
    change (P.nodes.dropLast ++ Q.nodes).getLast? = Q.nodes.getLast?
    exact List.getLast?_append_of_ne_nil P.nodes.dropLast Q.nonempty
  have hleft := List.getLast?_eq_some_getLast (P.append Q h).nonempty
  have hright := List.getLast?_eq_some_getLast Q.nonempty
  exact Option.some.inj (hleft.symm.trans (hopen.trans hright))

/-- S suffix beginning at the `i`th node. -/
noncomputable def drop (P : Path E unpebbled) (i : ℕ) (hi : i < P.length) : Path E unpebbled where
  nodes := P.nodes.drop i
  nonempty := by simpa [length, List.drop_eq_nil_iff] using hi
  chain := P.chain.drop i
  unpebbled' := fun v hv => P.unpebbled' v (List.mem_of_mem_drop hv)


@[simp] theorem drop_length (P : Path E unpebbled) (i : ℕ) (hi : i < P.length) :
    (P.drop i hi).length = P.length - i := by simp [drop, length]

@[simp] theorem drop_first (P : Path E unpebbled) (i : ℕ) (hi : i < P.length) :
    (P.drop i hi).first = P.nodes[i]'(by simpa [length] using hi) := by
  have hopen : (P.drop i hi).nodes.head? = some P.nodes[i] := by
    change (P.nodes.drop i).head? = some P.nodes[i]
    rw [List.head?_eq_some_head (by simpa [List.drop_eq_nil_iff, length] using hi)]
    simp
    rfl
  have hleft := List.head?_eq_some_head (P.drop i hi).nonempty
  exact Option.some.inj (hleft.symm.trans hopen)

@[simp] theorem drop_last (P : Path E unpebbled) (i : ℕ) (hi : i < P.length) :
    (P.drop i hi).last = P.last := by
  have hopen : (P.drop i hi).nodes.getLast? = P.nodes.getLast? := by
    change (P.nodes.drop i).getLast? = P.nodes.getLast?
    rw [List.getLast?_drop]
    have hi' : i < P.nodes.length := by simpa [length] using hi
    rw [if_neg (Nat.not_le_of_lt hi')]
  have hleft := List.getLast?_eq_some_getLast (P.drop i hi).nonempty
  have hright := List.getLast?_eq_some_getLast P.nonempty
  exact Option.some.inj (hleft.symm.trans (hopen.trans hright))

end Path

structure LayeredGraph (V : Type u) (ℓ n : ℕ) where
  layer : ℕ → Finset V
  depth : V → ℕ
  rank : V → ℕ
  intra : ℕ → V → V → Prop
  inter : ℕ → V → V → Prop
  pred : ℕ → Finset V → Finset V
  layer_mem : ∀ {d v}, v ∈ layer d ↔ depth v = d ∧ d < ℓ
  layer_card : ∀ {d}, d < ℓ → (layer d).card = n
  intra_mem : ∀ {d u v}, intra d u v → u ∈ layer d ∧ v ∈ layer d
  inter_mem : ∀ {d u v}, inter d u v → u ∈ layer (d + 1) ∧ v ∈ layer d
  intra_rank : ∀ {d u v}, intra d u v → rank u < rank v
  inter_rank : ∀ {d u v}, inter d u v → rank u < rank v
  pred_subset : ∀ {d T}, pred d T ⊆ layer (d + 1)
  pred_edge : ∀ {d T u}, u ∈ pred d T → ∃ v ∈ T, inter d u v

namespace LayeredGraph
variable {ℓ n : ℕ} (G : LayeredGraph V ℓ n)

def DepthRobustAt (d t d₀ : ℕ) : Prop :=
  ∀ F : Finset V, F ⊆ G.layer d → t ≤ F.card →
    ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
      (∀ v ∈ p, v ∈ F) ∧ d₀ ≤ p.length

def DepthRobust (t d₀ : ℕ) : Prop :=
  ∀ d, d < ℓ → G.DepthRobustAt d t d₀

def Expands (β : ℝ → ℝ) (a p : ℝ) : Prop :=
  ∀ {d X x}, d + 1 < ℓ → X ⊆ G.layer d → x ∈ Icc a p →
    x ≤ (X.card : ℝ) / n → β x * n ≤ (G.pred d X).card

/-- All horizontal and vertical dependency edges. -/
def edge (u v : V) : Prop :=
  (∃ d, G.intra d u v) ∨ (∃ d, G.inter d u v)

theorem edge_rank {u v : V} (h : G.edge u v) : G.rank u < G.rank v := by
  rcases h with ⟨d, h⟩ | ⟨d, h⟩
  · exact G.intra_rank h
  · exact G.inter_rank h

/-- S dependency edge stays in one layer or descends by exactly one layer. -/
theorem edge_depth_le_succ {u v : V} (h : G.edge u v) :
    G.depth u ≤ G.depth v + 1 := by
  rcases h with ⟨d, h⟩ | ⟨d, h⟩
  · have hu := (G.layer_mem.mp (G.intra_mem h).1).1
    have hv := (G.layer_mem.mp (G.intra_mem h).2).1
    omega
  · have hu := (G.layer_mem.mp (G.inter_mem h).1).1
    have hv := (G.layer_mem.mp (G.inter_mem h).2).1
    omega

/-- S path from depth `d` to depth zero contains at least `d + 1` nodes. -/
theorem depth_add_one_le_path_length {unpebbled : V → Prop} (P : Path G.edge unpebbled)
    (hlast : G.depth P.last = 0) : G.depth P.first + 1 ≤ P.length := by
  have aux : ∀ (l : List V) (hne : l ≠ []), l.IsChain G.edge →
      G.depth (l.head hne) + 1 ≤ G.depth (l.getLast hne) + l.length := by
    intro l
    induction l using List.twoStepInduction with
    | nil =>
        intro hne
        exact absurd rfl hne
    | singleton x =>
        intro _ _
        simp
    | cons_cons x y xs _ ih =>
        intro _ hchain
        have hxy := G.edge_depth_le_succ hchain.rel
        have htail := ih y (by simp) hchain.of_cons
        simp only [List.head_cons, List.getLast_cons_cons, List.length_cons] at htail ⊢
        omega
  have h := aux P.nodes P.nonempty P.chain
  simp only [Path.first, Path.last, Path.length] at hlast h ⊢
  omega

theorem path_nodup {unpebbled : V → Prop} (P : Path G.edge unpebbled) :
    P.nodes.Nodup := by
  have hc : P.nodes.IsChain (fun u v => G.rank u < G.rank v) :=
    P.chain.imp fun _ _ h => G.edge_rank h
  have hp : P.nodes.Pairwise (fun u v => G.rank u < G.rank v) := by
    rwa [← List.isChain_iff_pairwise]
  apply hp.imp
  intro a b h hab
  subst b
  exact Nat.lt_irrefl _ h

theorem layer_weight_le_one (hn : 0 < n) {d : ℕ} (hd : d < ℓ) {T : Finset V}
    (hT : T ⊆ G.layer d) : (T.card : ℝ) / n ≤ 1 := by
  have hc : T.card ≤ n := by rw [← G.layer_card hd]; exact Finset.card_le_card hT
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_one hnr]
  exact_mod_cast hc

end LayeredGraph

structure Pebbling {ℓ n : ℕ} (G : LayeredGraph V ℓ n) (δ ρ : ℝ) where
  black : ℕ → Finset V
  red : ℕ → Finset V
  black_subset : ∀ d, black d ⊆ G.layer d
  red_subset : ∀ d, red d ⊆ G.layer d
  black_total : ∀ m, ∑ d ∈ Finset.range m, ((black d).card : ℝ) / n ≤ ρ
  red_bound : ∀ d, ((red d).card : ℝ) ≤ δ * n

namespace Pebbling
variable {ℓ n : ℕ} {G : LayeredGraph V ℓ n} {δ ρ : ℝ}

def unpebbled (P : Pebbling G δ ρ) (v : V) : Prop :=
  v ∉ P.black (G.depth v) ∧ v ∉ P.red (G.depth v)

noncomputable def spend (P : Pebbling G δ ρ) (d : ℕ) : ℝ :=
  ((P.black d).card : ℝ) / n

variable {P : Pebbling G δ ρ}

/-- Unpebbled reachability in the actual stacked DAG. -/
def Reaches (P : Pebbling G δ ρ) (u v : V) : Prop :=
  ∃ Q : Path G.edge P.unpebbled, Q.first = u ∧ Q.last = v

theorem reaches_refl (P : Pebbling G δ ρ) {v : V} (hv : P.unpebbled v) : P.Reaches v v := by
  exact ⟨Path.singleton v hv, rfl, rfl⟩


/-- The actual footprint of a finite target set. -/
def footprint (P : Pebbling G δ ρ) (S : Finset V) : Set V :=
  {u | ∃ v ∈ S, P.Reaches u v}

noncomputable def layerFootprint (P : Pebbling G δ ρ) (S : Finset V) (d : ℕ) : Finset V :=
  by
    classical
    exact (G.layer d).filter fun u => u ∈ P.footprint S

@[simp] theorem mem_layerFootprint (P : Pebbling G δ ρ) (S : Finset V) {d : ℕ} {u : V} :
    u ∈ P.layerFootprint S d ↔ u ∈ G.layer d ∧ u ∈ P.footprint S := by
  classical
  simp [layerFootprint]

theorem footprint_available (P : Pebbling G δ ρ) (S : Finset V) {u : V}
    (hu : u ∈ P.footprint S) : P.unpebbled u := by
  rcases hu with ⟨v, _, Q, hfirst, _⟩
  rw [← hfirst]
  exact Q.unpebbled' Q.first Q.first_mem


/-- Prepending a genuine inter-layer edge preserves unpebbled reachability. -/
theorem pred_survivor_mem (P : Pebbling G δ ρ) (S : Finset V) {d : ℕ} {u : V}
    (huPred : u ∈ G.pred d (P.layerFootprint S d))
    (huBlack : u ∉ P.black (d + 1)) (huRed : u ∉ P.red (d + 1)) :
    u ∈ P.layerFootprint S (d + 1) := by
  classical
  have huLayer := G.pred_subset huPred
  have hdepth : G.depth u = d + 1 := (G.layer_mem.mp huLayer).1
  have huAvail : P.unpebbled u := by
    simpa [Pebbling.unpebbled, hdepth] using And.intro huBlack huRed
  obtain ⟨v, hvFoot, huv⟩ := G.pred_edge huPred
  have hv := (P.mem_layerFootprint S).mp hvFoot
  rcases hv.2 with ⟨a, haA, Q, hQv, hQa⟩
  have hedge : G.edge u v := Or.inr ⟨d, huv⟩
  have hcons : (u :: Q.nodes).IsChain G.edge := by
    apply Q.chain.cons
    intro y hy
    rw [List.head?_eq_some_head Q.nonempty] at hy
    simp only [Option.mem_some_iff] at hy
    subst y
    change Q.nodes.head Q.nonempty = v at hQv
    simpa only [hQv] using hedge
  let R : Path G.edge P.unpebbled := {
    nodes := u :: Q.nodes
    nonempty := by simp
    chain := hcons
    unpebbled' := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact huAvail
      · exact Q.unpebbled' x hx
  }
  refine (P.mem_layerFootprint S).mpr ⟨huLayer, a, haA, R, ?_, ?_⟩
  · simp [R, Path.first]
  · simpa [R, Path.last, List.getLast_cons Q.nonempty] using hQa

/-! ### Actual footprints dominate the scalar recurrence -/

/-- Normalized cardinality. -/
noncomputable def weight (n : ℕ) (S : Finset V) : ℝ := (S.card : ℝ) / n

theorem layerFootprint_subset (P : Pebbling G δ ρ) (S : Finset V) (d : ℕ) :
    P.layerFootprint S d ⊆ G.layer d := by
  intro u hu
  exact (P.mem_layerFootprint S).mp hu |>.1

/-- One genuine expansion step: after deleting the red and black pebbles in the
predecessor layer, the actual footprint is at least the scalar recurrence. -/
theorem layerFootprint_step (P : Pebbling G δ ρ) (hn : 0 < n) {β : ℝ → ℝ} {a p : ℝ}
    (hexp : G.Expands β a p) {S : Finset V} {d : ℕ}
    (hd : d + 1 < ℓ) {x : ℝ} (hxactive : x ∈ Set.Icc a p)
    (hx : x ≤ weight n (P.layerFootprint S d)) :
    max 0 ((β x - δ) - P.spend (d + 1)) ≤
      weight n (P.layerFootprint S (d + 1)) := by
  classical
  let T := P.layerFootprint S d
  let U := G.pred d T \ (P.black (d + 1) ∪ P.red (d + 1))
  have hT : T ⊆ G.layer d := P.layerFootprint_subset S d
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hexpand : β x * n ≤ (G.pred d T).card := by
    exact hexp hd hT hxactive (by simpa [weight, T] using hx)
  have hUsub : U ⊆ P.layerFootprint S (d + 1) := by
    intro u hu
    have hu' := Finset.mem_sdiff.mp hu
    have hunion : u ∉ P.black (d + 1) ∪ P.red (d + 1) := hu'.2
    exact P.pred_survivor_mem S hu'.1
      (fun hub => hunion (Finset.mem_union_left _ hub))
      (fun hur => hunion (Finset.mem_union_right _ hur))
  have hcover : G.pred d T ⊆ U ∪ (P.black (d + 1) ∪ P.red (d + 1)) := by
    intro u hu
    by_cases hub : u ∈ P.black (d + 1) ∪ P.red (d + 1)
    · exact Finset.mem_union_right _ hub
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, hub⟩)
  have hcardNat : (G.pred d T).card ≤
      U.card + (P.black (d + 1)).card + (P.red (d + 1)).card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le U (P.black (d + 1) ∪ P.red (d + 1))
    have h3 := Finset.card_union_le (P.black (d + 1)) (P.red (d + 1))
    omega
  have hcard : ((G.pred d T).card : ℝ) ≤
      U.card + (P.black (d + 1)).card + (P.red (d + 1)).card := by
    exact_mod_cast hcardNat
  have hred := P.red_bound (d + 1)
  have hUcard : (U.card : ℝ) ≤ (P.layerFootprint S (d + 1)).card := by
    exact_mod_cast Finset.card_le_card hUsub
  have hraw : ((β x - δ) - P.spend (d + 1)) * n ≤
      (P.layerFootprint S (d + 1)).card := by
    have hblack : P.spend (d + 1) * n = ((P.black (d + 1)).card : ℝ) := by
      simp only [spend]
      field_simp
    nlinarith [hexpand, hcard, hred, hUcard]
  have hmain : (β x - δ) - P.spend (d + 1) ≤
      weight n (P.layerFootprint S (d + 1)) := by
    unfold weight
    rw [le_div_iff₀ hnreal]
    exact hraw
  have hzero : 0 ≤ weight n (P.layerFootprint S (d + 1)) :=
    div_nonneg (Nat.cast_nonneg _) hnreal.le
  exact max_le hzero hmain

theorem source_le_layerFootprint (P : Pebbling G δ ρ) {S : Finset V} {d : ℕ}
    (hA : S ⊆ G.layer d) (havail : ∀ v ∈ S, P.unpebbled v) {c : ℝ}
    (hc : c ≤ weight n S) : c ≤ weight n (P.layerFootprint S d) := by
  classical
  have hsub : S ⊆ P.layerFootprint S d := by
    intro v hv
    apply (P.mem_layerFootprint S).mpr
    exact ⟨hA hv, v, hv, P.reaches_refl (havail v hv)⟩
  exact hc.trans (by
    unfold weight
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg n))

theorem challenge_start_le (P : Pebbling G δ ρ) (hn : 0 < n) {w : ℝ} {S : Finset V}
    (hA : S ⊆ G.layer 0) (hred : ∀ v ∈ S, v ∉ P.red 0)
    (hweight : w ≤ weight n S) :
    max 0 (w - P.spend 0) ≤ weight n (P.layerFootprint S 0) := by
  classical
  let U := S \ P.black 0
  have hUsub : U ⊆ P.layerFootprint S 0 := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    have hvLayer := hA hv'.1
    have hdepth : G.depth v = 0 := (G.layer_mem.mp hvLayer).1
    have havail : P.unpebbled v := by
      simpa [Pebbling.unpebbled, hdepth] using And.intro hv'.2 (hred v hv'.1)
    exact (P.mem_layerFootprint S).mpr ⟨hvLayer, v, hv'.1, P.reaches_refl havail⟩
  have hcover : S ⊆ U ∪ P.black 0 := by
    intro v hv
    by_cases hb : v ∈ P.black 0
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hb⟩)
  have hcardNat : S.card ≤ U.card + (P.black 0).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hcard : (S.card : ℝ) ≤ U.card + (P.black 0).card := by exact_mod_cast hcardNat
  have hUcard : (U.card : ℝ) ≤ (P.layerFootprint S 0).card := by
    exact_mod_cast Finset.card_le_card hUsub
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hraw : w - P.spend 0 ≤ weight n (P.layerFootprint S 0) := by
    have hblack : P.spend 0 * n = ((P.black 0).card : ℝ) := by
      simp only [spend]
      field_simp
    unfold weight
    rw [le_div_iff₀ hnreal]
    unfold weight at hweight
    rw [le_div_iff₀ hnreal] at hweight
    nlinarith
  exact max_le (div_nonneg (Nat.cast_nonneg _) hnreal.le) hraw

/-- An actual unpebbled path beginning at `u` and ending in the challenge set `S`. -/
def PathTo (P : Pebbling G δ ρ) (S : Finset V) (u : V) (L : ℝ) : Prop :=
  ∃ a ∈ S, ∃ Q : Path G.edge P.unpebbled,
    Q.first = u ∧ Q.last = a ∧ L ≤ (Q.length : ℝ)

/-- The concrete meaning of “the footprint of `S` contains an unpebbled path of length
`L`”. -/
def HasUnpebbledPathInFootprint (P : Pebbling G δ ρ) (S : Finset V) (L : ℝ) : Prop :=
  ∃ u, P.PathTo S u L

theorem pathTo_mono (P : Pebbling G δ ρ) (S : Finset V) {u : V} {L L' : ℝ}
    (hLL' : L' ≤ L) (h : P.PathTo S u L) : P.PathTo S u L' := by
  rcases h with ⟨a, ha, Q, hfirst, hlast, hlen⟩
  exact ⟨a, ha, Q, hfirst, hlast, hLL'.trans hlen⟩

theorem hasPath_mono (P : Pebbling G δ ρ) (S : Finset V) {L L' : ℝ}
    (hLL' : L' ≤ L) (h : P.HasUnpebbledPathInFootprint S L) :
    P.HasUnpebbledPathInFootprint S L' := by
  rcases h with ⟨u, hu⟩
  exact ⟨u, P.pathTo_mono S hLL' hu⟩

/-- Every node of a `PathTo` witness really lies in the footprint. -/
theorem pathTo_nodes_mem_footprint (P : Pebbling G δ ρ) (S : Finset V) {u : V} {L : ℝ}
    (h : P.PathTo S u L) :
    ∃ Q : Path G.edge P.unpebbled, Q.first = u ∧ L ≤ (Q.length : ℝ) ∧
      ∀ v ∈ Q.nodes, v ∈ P.footprint S := by
  rcases h with ⟨a, ha, Q, hfirst, hlast, hlen⟩
  refine ⟨Q, hfirst, hlen, ?_⟩
  intro v hv
  obtain ⟨l₁, l₂, hsplit⟩ := List.mem_iff_append.mp hv
  have hsuffix_ne : v :: l₂ ≠ [] := by simp
  let R : Path G.edge P.unpebbled := {
    nodes := v :: l₂
    nonempty := hsuffix_ne
    chain := by
      have hchain := Q.chain
      rw [hsplit] at hchain
      exact hchain.right_of_append
    unpebbled' := by
      intro w hw
      apply Q.unpebbled' w
      rw [hsplit]
      exact List.mem_append_right _ hw
  }
  refine ⟨a, ha, R, by simp [R, Path.first], ?_⟩
  have hlast' : R.last = Q.last := by
    apply Option.some.inj
    have hR := List.getLast?_eq_some_getLast R.nonempty
    have hQ := List.getLast?_eq_some_getLast Q.nonempty
    have hs : R.nodes.getLast? = Q.nodes.getLast? := by
      rw [hsplit]
      change (v :: l₂).getLast? = (l₁ ++ v :: l₂).getLast?
      symm
      exact List.getLast?_append_of_ne_nil l₁ hsuffix_ne
    exact hR.symm.trans (hs.trans hQ)
  exact hlast'.trans hlast

/-- Eliminate the compact chain certificate into a genuine unpebbled directed path all
of whose nodes lie in the footprint. -/
theorem hasPath_witness (P : Pebbling G δ ρ) (S : Finset V) {L : ℝ}
    (h : P.HasUnpebbledPathInFootprint S L) :
    ∃ Q : Path G.edge P.unpebbled,
      L ≤ (Q.length : ℝ) ∧ ∀ v ∈ Q.nodes, v ∈ P.footprint S := by
  rcases h with ⟨u, hu⟩
  obtain ⟨Q, _, hlen, hfoot⟩ := P.pathTo_nodes_mem_footprint S hu
  exact ⟨Q, hlen, hfoot⟩

/-- S reachability path between distinct layers contains at least its two endpoints. -/
theorem reaches_path_length_two {u v : V} (Q : Path G.edge P.unpebbled)
    (hfirst : Q.first = u) (hlast : Q.last = v) (hdepth : G.depth u ≠ G.depth v) :
    2 ≤ Q.length := by
  by_contra h
  have hpos := Q.length_pos
  have hlen : Q.length = 1 := by omega
  have hsingle : ∃ a, Q.nodes = [a] := by
    rw [Path.length] at hlen
    exact List.length_eq_one_iff.mp hlen
  rcases hsingle with ⟨a, ha⟩
  have huv : u = v := by
    rw [← hfirst, ← hlast]
    simp [Path.first, Path.last, ha]
  exact hdepth (congrArg G.depth huv)

/-- S path inside the footprint of the challenge set already reaches the challenge set. -/
theorem splice_challenge (P : Pebbling G δ ρ) {S : Finset V} {b : ℕ}
    {Q : Path G.edge P.unpebbled} (hQ : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint S b) :
    P.PathTo S Q.first (Q.length : ℝ) := by
  classical
  have hlastF : Q.last ∈ P.layerFootprint S b := hQ Q.last Q.last_mem
  obtain ⟨a, haA, R, hRfirst, hRlast⟩ := ((P.mem_layerFootprint S).mp hlastF).2
  let QR := Q.append R hRfirst.symm
  refine ⟨a, haA, QR, by simp [QR], by simpa [QR] using hRlast, ?_⟩
  have hlen : Q.length ≤ QR.length := by
    simp only [QR, Path.append_length]
    have := R.length_pos
    omega
  exact_mod_cast hlen

/-- S path inside the footprint of a source set `D` sitting at a *different* depth
reaches `D`, and there picks up everything `D` already carries. -/
theorem splice_source (P : Pebbling G δ ρ) {S D : Finset V} {b c : ℕ} (hbc : b ≠ c)
    (hD : D ⊆ G.layer c) {m : ℝ} (hcarry : ∀ w ∈ D, P.PathTo S w m)
    {Q : Path G.edge P.unpebbled} (hQ : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b) :
    P.PathTo S Q.first ((Q.length : ℝ) + m) := by
  classical
  have hlastF : Q.last ∈ P.layerFootprint D b := hQ Q.last Q.last_mem
  have hmem := (P.mem_layerFootprint D).mp hlastF
  obtain ⟨w, hwD, R, hRfirst, hRlast⟩ := hmem.2
  have hQdepth : G.depth Q.last = b := (G.layer_mem.mp hmem.1).1
  have hwDepth : G.depth w = c := (G.layer_mem.mp (hD hwD)).1
  have hdepthNe : G.depth Q.last ≠ G.depth w := by rw [hQdepth, hwDepth]; exact hbc
  have hRlen : 2 ≤ R.length := reaches_path_length_two R hRfirst hRlast hdepthNe
  obtain ⟨a, haA, O, hOfirst, hOlast, hOlen⟩ := hcarry w hwD
  let QR := Q.append R hRfirst.symm
  have hROjoin : QR.last = O.first := by simpa [QR] using hRlast.trans hOfirst.symm
  let QRO := QR.append O hROjoin
  refine ⟨a, haA, QRO, by simp [QRO, QR], by simpa [QRO] using hOlast, ?_⟩
  have hlen : Q.length + O.length ≤ QRO.length := by
    simp only [QRO, QR, Path.append_length]
    have := Q.length_pos
    have := O.length_pos
    omega
  have hlen' : (Q.length : ℝ) + (O.length : ℝ) ≤ (QRO.length : ℝ) := by exact_mod_cast hlen
  linarith


end Pebbling
end Concrete
end ProofOfSpace

/-
# Concrete layered graphs and footprints

This module connects the scalar footprint analysis to actual nodes and directed
paths.  The graph interface records the development's standing inter-layer expansion
property and retains `depthRobust` as the requested intra-layer construction
assumption.  The footprint recurrence, chain construction, and path-splicing arguments
are proved below.
-/
import ProofOfSpace.Chain
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop

namespace ProofOfSpace

open Finset Set

universe u

namespace Concrete

variable {V : Type u}

/-- A nonempty directed path whose nodes are all unpebbled.  `List.IsChain` checks
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

/-- A suffix beginning at the `i`th node. -/
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

/-- A stacked DAG indexed by depth (see `Footprint.lean` for how this relates to
Reyzin's published level numbering): `layer 0` is the bottom layer `V_ℓ`, which carries
the challenge, and inter-layer edges run from `layer (d+1)` to `layer d`.  `expands` is
`expansion condition`, the standing property of the constructed vertical edges.  Intra-layer
robustness (`depth-robustness condition`) is stated separately so that different layer ranges may
use different graph constructions. -/
structure LayeredGraph (V : Type u) (S : Setting) (ℓ n : ℕ) where
  /-- The normalized path length promised by intra-layer depth robustness. -/
  αpi : ℝ
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
  /-- Operational expansion on the active gain interval.  It is stated at any scalar
  lower bound `x` for the source-set weight because the sampled construction may pass to
  a subset whose cardinality is the next grid point above `x`. -/
  expands : ∀ {d T x}, d + 1 < ℓ → T ⊆ layer d →
    x ∈ Set.Icc S.αmin S.αmax → x ≤ (T.card : ℝ) / n →
    S.β x * n ≤ (pred d T).card

namespace LayeredGraph

variable {S : Setting} {ℓ n : ℕ} (G : LayeredGraph V S ℓ n)

/-- The usual depth-robust path property at one specified layer. -/
def DepthRobustAt (d : ℕ) (α : ℝ) : Prop :=
  ∀ F : Finset V, F ⊆ G.layer d → S.pi * n ≤ (F.card : ℝ) →
    ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
      (∀ v ∈ p, v ∈ F) ∧ α * n ≤ (p.length : ℝ)

/-- Uniform depth robustness over all layers. -/
def DepthRobust (α : ℝ) : Prop :=
  ∀ {d : ℕ}, d < ℓ → G.DepthRobustAt d α

/-! ### Ordinary depth robustness, in deletion-set form -/

/-- `(e, dep)` node depth robustness at one layer: deleting at most `e` nodes of the
layer leaves an intra-layer path on at least `dep` surviving nodes.

`DepthRobustAt` above is the special case `e = (1 - π) n`, stated in
survivor form; `depthRobustAt_of_nodeDepthRobustAt` below converts one to the other.
The deletion form is what the standalone-graph transfers of `Constructions.lean`
speak, since a standalone certificate is stated as a deletion budget. -/
def NodeDepthRobustAt [DecidableEq V] (G : LayeredGraph V S ℓ n) (d : ℕ) (e dep : ℝ) : Prop :=
  ∀ X : Finset V, X ⊆ G.layer d → ((X.card : ℝ) ≤ e) →
    ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
      (∀ v ∈ p, v ∈ G.layer d \ X) ∧ dep ≤ (p.length : ℝ)

/-- The survivor form used by `Concrete.LayeredGraph.DepthRobustAt` is the deletion form
at budget `(1 - π) n`. -/
theorem depthRobustAt_of_nodeDepthRobustAt [DecidableEq V] (G : LayeredGraph V S ℓ n)
    {d : ℕ} {α : ℝ} (hd : d < ℓ)
    (h : G.NodeDepthRobustAt d ((1 - S.pi) * n) (α * n)) :
    G.DepthRobustAt d α := by
  intro F hF hFcard
  have hXcard : (((G.layer d \ F).card : ℝ)) ≤ (1 - S.pi) * n := by
    rw [Finset.card_sdiff_of_subset hF, Nat.cast_sub (Finset.card_le_card hF),
      G.layer_card hd]
    linarith
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h (G.layer d \ F) Finset.sdiff_subset hXcard
  refine ⟨p, hp, hchain, ?_, hlen⟩
  intro v hv
  have := hmem v hv
  rwa [Finset.sdiff_sdiff_eq_self hF] at this

/-- Conversely, survivor-form depth robustness is exactly deletion-form robustness at
budget `(1 - π) n`.  This direction uses `F = layer d \ X`; keeping it explicit avoids
silently strengthening the graph hypothesis when moving between the two APIs. -/
theorem nodeDepthRobustAt_of_depthRobustAt [DecidableEq V] (G : LayeredGraph V S ℓ n)
    {d : ℕ} {α : ℝ} (hd : d < ℓ) (h : G.DepthRobustAt d α) :
    G.NodeDepthRobustAt d ((1 - S.pi) * n) (α * n) := by
  intro X hX hXcard
  set F := G.layer d \ X with hF
  have hFcard : S.pi * n ≤ (F.card : ℝ) := by
    have hcard : F.card = n - X.card := by
      rw [hF, Finset.card_sdiff_of_subset hX, G.layer_card hd]
    have hXcardNat : X.card ≤ n := by
      rw [← G.layer_card hd]
      exact Finset.card_le_card hX
    rw [hcard, Nat.cast_sub hXcardNat]
    linarith
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h F Finset.sdiff_subset hFcard
  exact ⟨p, hp, hchain, hmem, hlen⟩

/-- The two layer-level formulations are equivalent, including their exact real-valued
rounding convention. -/
theorem depthRobustAt_iff_nodeDepthRobustAt [DecidableEq V] (G : LayeredGraph V S ℓ n)
    {d : ℕ} {α : ℝ} (hd : d < ℓ) :
    G.DepthRobustAt d α ↔ G.NodeDepthRobustAt d ((1 - S.pi) * n) (α * n) :=
  ⟨G.nodeDepthRobustAt_of_depthRobustAt hd,
    G.depthRobustAt_of_nodeDepthRobustAt hd⟩

/-- All horizontal and vertical dependency edges. -/
def edge (u v : V) : Prop :=
  (∃ d, G.intra d u v) ∨ (∃ d, G.inter d u v)

theorem edge_rank {u v : V} (h : G.edge u v) : G.rank u < G.rank v := by
  rcases h with ⟨d, h⟩ | ⟨d, h⟩
  · exact G.intra_rank h
  · exact G.inter_rank h

/-- A dependency edge stays in one layer or descends by exactly one layer. -/
theorem edge_depth_le_succ {u v : V} (h : G.edge u v) :
    G.depth u ≤ G.depth v + 1 := by
  rcases h with ⟨d, h⟩ | ⟨d, h⟩
  · have hu := (G.layer_mem.mp (G.intra_mem h).1).1
    have hv := (G.layer_mem.mp (G.intra_mem h).2).1
    omega
  · have hu := (G.layer_mem.mp (G.inter_mem h).1).1
    have hv := (G.layer_mem.mp (G.inter_mem h).2).1
    omega

/-- A path from depth `d` to depth zero contains at least `d + 1` nodes. -/
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

/--
A concrete red/black pebble placement.  The budget fields are precisely the adversarial
bounds of the development, expressed per layer: `black_total` caps the *total* stored weight
across all layers at `ρ`, and `red_bound` caps each layer's red set at `δ n`.

**Scope of the model.**  This is a *static space snapshot*, not a time-indexed pebbling
game: `black` is one fixed assignment, the adversary's stored state at challenge time,
and there is no move sequence.  Consequently the theorems in `Latency.lean` do not bound
a running time directly — they exhibit an unpebbled directed path of a given length that
ends at a challenge and lies inside the challenge footprint.  The bridge to latency is
`LayeredGraph.depth_add_one_le_path_length` together with the development's argument that such
a path must be recomputed sequentially; that last step is prose, here as in the development.

Note also what the challenge set is required to be: the latency theorems take
`A ⊆ layer 0` with `weight n A ≥ ζ_δ` and `A` disjoint from `red 0`.  At the Filecoin
parameters `ζ_δ = 0.8622`, so `A` is essentially the whole final layer, not a small
sampled challenge.  This is consistent — `red_bound` caps red at `δ n = 0.0378 n`, and
`0.8622 ≤ 1 - 0.0378` — but it is a modelling choice inherited from the development. -/
structure Pebbling {S : Setting} {ℓ n : ℕ} (G : LayeredGraph V S ℓ n) where
  black : ℕ → Finset V
  red : ℕ → Finset V
  black_subset : ∀ d, black d ⊆ G.layer d
  red_subset : ∀ d, red d ⊆ G.layer d
  black_total : ∀ m,
    ∑ d ∈ Finset.range m, ((black d).card : ℝ) / n ≤ S.ρ
  red_bound : ∀ d, ((red d).card : ℝ) ≤ S.δ * n

namespace Pebbling

variable {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n}

def unpebbled (P : Pebbling G) (v : V) : Prop :=
  v ∉ P.black (G.depth v) ∧ v ∉ P.red (G.depth v)

noncomputable def budget (P : Pebbling G) : Budget S where
  spend d := ((P.black d).card : ℝ) / n
  spend_nonneg _d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := P.black_total

@[simp] theorem budget_spend (P : Pebbling G) (d : ℕ) :
    P.budget.spend d = ((P.black d).card : ℝ) / n := rfl

end Pebbling

variable {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n}

namespace Pebbling

variable {P : Pebbling G}

/-- Unpebbled reachability in the actual stacked DAG. -/
def Reaches (P : Pebbling G) (u v : V) : Prop :=
  ∃ Q : Path G.edge P.unpebbled, Q.first = u ∧ Q.last = v

theorem reaches_refl (P : Pebbling G) {v : V} (hv : P.unpebbled v) : P.Reaches v v := by
  exact ⟨Path.singleton v hv, rfl, rfl⟩


/-- The actual footprint of a finite target set. -/
def footprint (P : Pebbling G) (A : Finset V) : Set V :=
  {u | ∃ v ∈ A, P.Reaches u v}

noncomputable def layerFootprint (P : Pebbling G) (A : Finset V) (d : ℕ) : Finset V :=
  by
    classical
    exact (G.layer d).filter fun u => u ∈ P.footprint A

@[simp] theorem mem_layerFootprint (P : Pebbling G) (A : Finset V) {d : ℕ} {u : V} :
    u ∈ P.layerFootprint A d ↔ u ∈ G.layer d ∧ u ∈ P.footprint A := by
  classical
  simp [layerFootprint]

theorem footprint_available (P : Pebbling G) (A : Finset V) {u : V}
    (hu : u ∈ P.footprint A) : P.unpebbled u := by
  rcases hu with ⟨v, _, Q, hfirst, _⟩
  rw [← hfirst]
  exact Q.unpebbled' Q.first Q.first_mem


/-- Prepending a genuine inter-layer edge preserves unpebbled reachability. -/
theorem pred_survivor_mem (P : Pebbling G) (A : Finset V) {d : ℕ} {u : V}
    (huPred : u ∈ G.pred d (P.layerFootprint A d))
    (huBlack : u ∉ P.black (d + 1)) (huRed : u ∉ P.red (d + 1)) :
    u ∈ P.layerFootprint A (d + 1) := by
  classical
  have huLayer := G.pred_subset huPred
  have hdepth : G.depth u = d + 1 := (G.layer_mem.mp huLayer).1
  have huAvail : P.unpebbled u := by
    simpa [Pebbling.unpebbled, hdepth] using And.intro huBlack huRed
  obtain ⟨v, hvFoot, huv⟩ := G.pred_edge huPred
  have hv := (P.mem_layerFootprint A).mp hvFoot
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
  refine (P.mem_layerFootprint A).mpr ⟨huLayer, a, haA, R, ?_, ?_⟩
  · simp [R, Path.first]
  · simpa [R, Path.last, List.getLast_cons Q.nonempty] using hQa

/-! ### Actual footprints dominate the scalar recurrence -/

/-- Normalized cardinality. -/
noncomputable def weight (n : ℕ) (A : Finset V) : ℝ := (A.card : ℝ) / n

theorem layerFootprint_subset (P : Pebbling G) (A : Finset V) (d : ℕ) :
    P.layerFootprint A d ⊆ G.layer d := by
  intro u hu
  exact (P.mem_layerFootprint A).mp hu |>.1

/-- One genuine expansion step: after deleting the red and black pebbles in the
predecessor layer, the actual footprint is at least the scalar recurrence. -/
theorem layerFootprint_step (P : Pebbling G) (hn : 0 < n) {A : Finset V} {d : ℕ}
    (hd : d + 1 < ℓ) {x : ℝ} (hxactive : x ∈ Set.Icc S.αmin S.αmax)
    (hx : x ≤ weight n (P.layerFootprint A d)) :
    max 0 (S.betaD x - P.budget.spend (d + 1)) ≤
      weight n (P.layerFootprint A (d + 1)) := by
  classical
  let T := P.layerFootprint A d
  let U := G.pred d T \ (P.black (d + 1) ∪ P.red (d + 1))
  have hT : T ⊆ G.layer d := P.layerFootprint_subset A d
  have hTle : weight n T ≤ 1 := G.layer_weight_le_one hn (by omega) hT
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hexpand : S.β x * n ≤ (G.pred d T).card := by
    exact G.expands hd hT hxactive (by simpa [weight, T] using hx)
  have hUsub : U ⊆ P.layerFootprint A (d + 1) := by
    intro u hu
    have hu' := Finset.mem_sdiff.mp hu
    have hunion : u ∉ P.black (d + 1) ∪ P.red (d + 1) := hu'.2
    exact P.pred_survivor_mem A hu'.1
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
  have hUcard : (U.card : ℝ) ≤ (P.layerFootprint A (d + 1)).card := by
    exact_mod_cast Finset.card_le_card hUsub
  have hraw : (S.betaD x - P.budget.spend (d + 1)) * n ≤
      (P.layerFootprint A (d + 1)).card := by
    have hblack : P.budget.spend (d + 1) * n = ((P.black (d + 1)).card : ℝ) := by
      simp only [Pebbling.budget_spend]
      field_simp
    simp only [Setting.betaD] at *
    nlinarith [hexpand, hcard, hred, hUcard]
  have hmain : S.betaD x - P.budget.spend (d + 1) ≤
      weight n (P.layerFootprint A (d + 1)) := by
    unfold weight
    rw [le_div_iff₀ hnreal]
    exact hraw
  have hzero : 0 ≤ weight n (P.layerFootprint A (d + 1)) :=
    div_nonneg (Nat.cast_nonneg _) hnreal.le
  exact max_le hzero hmain

/-- The footprint bound beginning with weight `c` at depth `start`. -/
noncomputable def footprintBound (P : Pebbling G) (start : ℕ) (c : ℝ) (d : ℕ) : ℝ :=
  if start ≤ d then
    Nat.rec c
      (fun k value => max 0 (S.betaD value - P.budget.spend (start + k + 1))) (d - start)
  else c

@[simp] theorem footprintBound_start (P : Pebbling G) (start : ℕ) (c : ℝ) :
    P.footprintBound start c start = c := by simp [footprintBound]

theorem footprintBound_isBound (P : Pebbling G) (start : ℕ) (c : ℝ) :
    IsFootprintBound S P.budget start (P.footprintBound start c) := by
  intro d hd
  rw [footprintBound, if_pos (by omega), footprintBound, if_pos hd]
  have hsub : d + 1 - start = (d - start) + 1 := by omega
  rw [hsub]
  simp only
  have hidx : start + (d - start) + 1 = d + 1 := by omega
  rw [hidx]

theorem footprintBound_nonneg (P : Pebbling G) {start : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {d : ℕ} (hd : start ≤ d) : 0 ≤ P.footprintBound start c d := by
  rcases eq_or_lt_of_le hd with rfl | hlt
  · simpa using hc
  · exact (P.footprintBound_isBound start c).nonneg hlt

/-- **The footprint bound really is a lower bound** on the genuine footprint weight, by
induction of the one-step bound through every remaining layer.  The development takes the
recurrence `footprint recurrence` from Reyzin and works with it directly, never restating
this dominance; it is proved here. -/
theorem footprintBound_le (P : Pebbling G) (hn : 0 < n) {A : Finset V}
    {start : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hbase : c ≤ weight n (P.layerFootprint A start)) :
    (∀ {d}, start ≤ d → d < ℓ →
      P.footprintBound start c d ∈ Set.Icc S.αmin S.αmax) →
    ∀ {d}, start ≤ d → d < ℓ →
      P.footprintBound start c d ≤ weight n (P.layerFootprint A d) := by
  intro hactive
  intro d hsd hdℓ
  induction d, hsd using Nat.le_induction with
  | base => simpa using hbase
  | succ d hsd ih =>
      rw [P.footprintBound_isBound start c d hsd]
      exact P.layerFootprint_step hn hdℓ (hactive hsd (by omega)) (ih (by omega))

/-- An unpebbled source set of normalized size at least `c` starts a certified scalar
footprint bound at `c`. -/
theorem source_le_layerFootprint (P : Pebbling G) {A : Finset V} {d : ℕ}
    (hA : A ⊆ G.layer d) (havail : ∀ v ∈ A, P.unpebbled v) {c : ℝ}
    (hc : c ≤ weight n A) : c ≤ weight n (P.layerFootprint A d) := by
  classical
  have hsub : A ⊆ P.layerFootprint A d := by
    intro v hv
    apply (P.mem_layerFootprint A).mpr
    exact ⟨hA hv, v, hv, P.reaches_refl (havail v hv)⟩
  exact hc.trans (by
    unfold weight
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg n))

/-- The scalar challenge footprint bound, initialized after charging top-layer black
pebbles. -/
noncomputable def challengeBound (P : Pebbling G) : ℕ → ℝ :=
  P.footprintBound 0 (max 0 (S.ζδ - P.budget.spend 0))

theorem challengeBound_isFootprintBound (P : Pebbling G) :
    IsFootprintBound S P.budget 0 P.challengeBound :=
  P.footprintBound_isBound 0 _


noncomputable def challengeBound_struct (P : Pebbling G) (hζ : 0 ≤ S.ζδ) :
    ChallengeBound S P.budget where
  f := P.challengeBound
  bound := P.challengeBound_isFootprintBound
  init_ge := by simp [challengeBound]
  init_le := by
    simp only [challengeBound, footprintBound_start]
    exact max_le hζ (by linarith [P.budget.spend_nonneg 0])

/-- At depth zero, a red-free challenge of weight `ζδ` contains the scalar starting
footprint after the top-layer black charge. -/
theorem challenge_start_le (P : Pebbling G) (hn : 0 < n) {A : Finset V}
    (hA : A ⊆ G.layer 0) (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ weight n A) :
    max 0 (S.ζδ - P.budget.spend 0) ≤ weight n (P.layerFootprint A 0) := by
  classical
  let U := A \ P.black 0
  have hUsub : U ⊆ P.layerFootprint A 0 := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    have hvLayer := hA hv'.1
    have hdepth : G.depth v = 0 := (G.layer_mem.mp hvLayer).1
    have havail : P.unpebbled v := by
      simpa [Pebbling.unpebbled, hdepth] using And.intro hv'.2 (hred v hv'.1)
    exact (P.mem_layerFootprint A).mpr ⟨hvLayer, v, hv'.1, P.reaches_refl havail⟩
  have hcover : A ⊆ U ∪ P.black 0 := by
    intro v hv
    by_cases hb : v ∈ P.black 0
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hb⟩)
  have hcardNat : A.card ≤ U.card + (P.black 0).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hcard : (A.card : ℝ) ≤ U.card + (P.black 0).card := by exact_mod_cast hcardNat
  have hUcard : (U.card : ℝ) ≤ (P.layerFootprint A 0).card := by
    exact_mod_cast Finset.card_le_card hUsub
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hraw : S.ζδ - P.budget.spend 0 ≤ weight n (P.layerFootprint A 0) := by
    have hblack : P.budget.spend 0 * n = ((P.black 0).card : ℝ) := by
      simp only [Pebbling.budget_spend]
      field_simp
    unfold weight
    rw [le_div_iff₀ hnreal]
    unfold weight at hweight
    rw [le_div_iff₀ hnreal] at hweight
    nlinarith
  exact max_le (div_nonneg (Nat.cast_nonneg _) hnreal.le) hraw

/-! ### Concrete path certificates and source prefixes -/

/-- An actual unpebbled path beginning at `u` and ending in the challenge set `A`. -/
def PathTo (P : Pebbling G) (A : Finset V) (u : V) (L : ℝ) : Prop :=
  ∃ a ∈ A, ∃ Q : Path G.edge P.unpebbled,
    Q.first = u ∧ Q.last = a ∧ L ≤ (Q.length : ℝ)

/-- The concrete meaning of “the footprint of `A` contains an unpebbled path of length
`L`”. -/
def HasUnpebbledPathInFootprint (P : Pebbling G) (A : Finset V) (L : ℝ) : Prop :=
  ∃ u, P.PathTo A u L

theorem pathTo_mono (P : Pebbling G) (A : Finset V) {u : V} {L L' : ℝ}
    (hLL' : L' ≤ L) (h : P.PathTo A u L) : P.PathTo A u L' := by
  rcases h with ⟨a, ha, Q, hfirst, hlast, hlen⟩
  exact ⟨a, ha, Q, hfirst, hlast, hLL'.trans hlen⟩

theorem hasPath_mono (P : Pebbling G) (A : Finset V) {L L' : ℝ}
    (hLL' : L' ≤ L) (h : P.HasUnpebbledPathInFootprint A L) :
    P.HasUnpebbledPathInFootprint A L' := by
  rcases h with ⟨u, hu⟩
  exact ⟨u, P.pathTo_mono A hLL' hu⟩

/-- Every node of a `PathTo` witness really lies in the footprint. -/
theorem pathTo_nodes_mem_footprint (P : Pebbling G) (A : Finset V) {u : V} {L : ℝ}
    (h : P.PathTo A u L) :
    ∃ Q : Path G.edge P.unpebbled, Q.first = u ∧ L ≤ (Q.length : ℝ) ∧
      ∀ v ∈ Q.nodes, v ∈ P.footprint A := by
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
theorem hasPath_witness (P : Pebbling G) (A : Finset V) {L : ℝ}
    (h : P.HasUnpebbledPathInFootprint A L) :
    ∃ Q : Path G.edge P.unpebbled,
      L ≤ (Q.length : ℝ) ∧ ∀ v ∈ Q.nodes, v ∈ P.footprint A := by
  rcases h with ⟨u, hu⟩
  obtain ⟨Q, _, hlen, hfoot⟩ := P.pathTo_nodes_mem_footprint A hu
  exact ⟨Q, hlen, hfoot⟩

/-- A path returned by depth robustness, converted to the global edge relation and
certified as unpebbled because it lies in a footprint. -/
theorem depthRobust_path (P : Pebbling G) {A : Finset V} {d : ℕ} {F : Finset V}
    (hrobust : G.DepthRobustAt d G.αpi) (hF : F ⊆ G.layer d)
    (hfoot : F ⊆ P.layerFootprint A d)
    (hweight : S.pi * n ≤ (F.card : ℝ)) :
    ∃ Q : Path G.edge P.unpebbled,
      (∀ v ∈ Q.nodes, v ∈ F) ∧ G.αpi * n ≤ (Q.length : ℝ) := by
  obtain ⟨q, hqne, hqchain, hqF, hqlen⟩ := hrobust F hF hweight
  let Q : Path G.edge P.unpebbled := {
    nodes := q
    nonempty := hqne
    chain := hqchain.imp fun _ _ h => Or.inl ⟨d, h⟩
    unpebbled' := by
      intro v hv
      exact P.footprint_available A ((P.mem_layerFootprint A).mp (hfoot (hqF v hv)) |>.2)
  }
  exact ⟨Q, hqF, by simpa [Q, Path.length] using hqlen⟩

/-- The first `k` nodes of a path, as a finite source set. -/
noncomputable def prefixSource [DecidableEq V] (Q : Path G.edge P.unpebbled) (k : ℕ)
    (hk : k ≤ Q.length) : Finset V :=
  Finset.univ.image fun i : Fin k =>
    Q.nodes[i.val]'(lt_of_lt_of_le i.isLt (by simpa [Path.length] using hk))

theorem prefixSource_card [DecidableEq V] (Q : Path G.edge P.unpebbled) (k : ℕ)
    (hk : k ≤ Q.length) : (prefixSource Q k hk).card = k := by
  unfold prefixSource
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact (G.path_nodup Q).getElem_inj_iff.mp hij

theorem mem_prefixSource [DecidableEq V] (Q : Path G.edge P.unpebbled) (k : ℕ)
    (hk : k ≤ Q.length) {v : V} :
    v ∈ prefixSource Q k hk ↔
      ∃ i : Fin k, Q.nodes[i.val]'(lt_of_lt_of_le i.isLt
        (by simpa [Path.length] using hk)) = v := by
  classical
  simp [prefixSource]

theorem prefixSource_subset_of_path [DecidableEq V] (Q : Path G.edge P.unpebbled)
    (k : ℕ) (hk : k ≤ Q.length) {F : Finset V}
    (hQF : ∀ v ∈ Q.nodes, v ∈ F) : prefixSource Q k hk ⊆ F := by
  intro v hv
  rcases (mem_prefixSource Q k hk).mp hv with ⟨i, rfl⟩
  exact hQF _ (List.getElem_mem _)

theorem prefixSource_available [DecidableEq V] (Q : Path G.edge P.unpebbled)
    (k : ℕ) (hk : k ≤ Q.length) : ∀ v ∈ prefixSource Q k hk, P.unpebbled v := by
  intro v hv
  rcases (mem_prefixSource Q k hk).mp hv with ⟨i, rfl⟩
  exact Q.unpebbled' _ (List.getElem_mem _)

/-- Rounding by `ceil` costs less than one node; retaining the selected source node
in its suffix exactly absorbs that rounding loss. -/
theorem prefix_suffix_length {σ απ : ℝ} (hσ : 0 < σ) (hσα : σ ≤ απ) (hn : 0 < n)
    (Q : Path G.edge P.unpebbled) (hQlen : απ * n ≤ (Q.length : ℝ))
    {i : ℕ} (hi : i < ⌈σ * n⌉₊) :
    (απ - σ) * n ≤ ((Q.length - i : ℕ) : ℝ) := by
  have hσn : 0 < σ * (n : ℝ) := mul_pos hσ (by exact_mod_cast hn)
  have hireal : (i : ℝ) < σ * n := Nat.lt_ceil.mp hi
  have hik : i ≤ Q.length := by
    have hceil : ⌈σ * n⌉₊ ≤ Q.length := by
      apply Nat.ceil_le.mpr
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact (mul_le_mul_of_nonneg_right hσα hn0).trans hQlen
    omega
  have hcast : ((Q.length - i : ℕ) : ℝ) = (Q.length : ℝ) - i := by
    rw [Nat.cast_sub hik]
  rw [hcast]
  nlinarith

/-- A reachability path between distinct layers contains at least its two endpoints. -/
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

/-! ### Concrete chains -/

/-- The exact path length represented by `z` concrete links. -/
def chainPathLength (G : LayeredGraph V S ℓ n) (T : Tracking S) (z : ℕ) : ℝ :=
  G.αpi * n + ((z : ℝ) - 1) * (G.αpi - T.σ) * n

/-- A concrete last link together with all the path certificates needed to extend it.
The `tail` field is the certified tail from every source node to `A` that a link
carries in `latency analysis`, strengthened
inductively so that it already includes all later links. -/
structure Link [DecidableEq V] (P : Pebbling G) (T : Tracking S) (A : Finset V) where
  depth : ℕ
  inside : depth < ℓ
  source : Finset V
  source_layer : source ⊆ G.layer depth
  source_available : ∀ v ∈ source, P.unpebbled v
  source_weight : T.σ ≤ weight n source
  expandable : Expandable P.budget T.ghat depth
  count : ℕ
  count_pos : 1 ≤ count
  tail : ∀ v ∈ source,
    P.PathTo A v ((count : ℝ) * (G.αpi - T.σ) * n)
  realized : P.HasUnpebbledPathInFootprint A (chainPathLength G T count)

namespace Link

variable [DecidableEq V]

theorem source_scalar_le (L : Link P T A) :
    T.σ ≤ weight n (P.layerFootprint L.source L.depth) :=
  P.source_le_layerFootprint L.source_layer L.source_available L.source_weight

theorem scalar_active (L : Link P T A)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam) {d : ℕ}
    (hdepth : L.depth ≤ d) :
    P.footprintBound L.depth T.σ d ∈ Set.Icc S.αmin S.αmax := by
  set f := P.footprintBound L.depth T.σ
  have hbound : IsFootprintBound S P.budget L.depth f :=
    P.footprintBound_isBound L.depth T.σ
  have hinit : f L.depth = T.σ := P.footprintBound_start L.depth T.σ
  have hupper : f d ≤ S.αmax :=
    (hbound.le_αmax (by rw [hinit]; exact T.σ_pos.le)
      (by rw [hinit]; exact T.σ_lt_αmax.le) d hdepth).2
  have hcond : S.αmin + S.ρ < S.betaD S.pi := by
    linarith [T.αmin_lt_lam]
  have hlower : S.αmin ≤ f d := by
    by_cases hfe : ∃ d0, L.depth ≤ d0 ∧ d0 ≤ d ∧ S.pi ≤ f d0
    · obtain ⟨d0, hd0b, hd0d, hd0f⟩ := hfe
      rcases eq_or_lt_of_le hd0d with rfl | hlt
      · exact S.αmin_lt_pi.le.trans hd0f
      · have hpost := post_floor hbound (by rw [hinit]; exact T.σ_pos.le)
          (by rw [hinit]; exact T.σ_lt_αmax.le) hcond hd0b hd0f d hlt
        linarith
    · push Not at hfe
      have hle : ∀ i, i ≤ d - L.depth → f (L.depth + i) ≤ S.pi := fun i hi =>
        (hfe (L.depth + i) (by omega) (by omega)).le
      have hfloor := mirror_floor L.expandable hbound hinit hle
        (d - L.depth) le_rfl
      have : T.lam ≤ f d := by
        rwa [show L.depth + (d - L.depth) = d from by omega] at hfloor
      exact T.αmin_lt_lam.le.trans this
  exact ⟨hlower, hupper⟩

theorem scalar_le_actual (L : Link P T A) (hn : 0 < n)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam) {d : ℕ}
    (hdepth : L.depth ≤ d) (hd : d < ℓ) :
    P.footprintBound L.depth T.σ d ≤ weight n (P.layerFootprint L.source d) :=
  P.footprintBound_le hn T.σ_pos.le L.source_scalar_le
    (fun hde _ => L.scalar_active hnobreak hde) hdepth hd

/-- Convert an actual footprint of weight at least `π` into a depth-robust local path. -/
theorem local_path (L : Link P T A) (hn : 0 < n) {d : ℕ} (hd : d < ℓ)
    (hDepth : G.DepthRobust G.αpi)
    (hweight : S.pi ≤ weight n (P.layerFootprint L.source d)) :
    ∃ Q : Path G.edge P.unpebbled,
      (∀ v ∈ Q.nodes, v ∈ P.layerFootprint L.source d) ∧
      G.αpi * n ≤ (Q.length : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint L.source d).card : ℝ) := by
    unfold weight at hweight
    rwa [le_div_iff₀ hnreal] at hweight
  exact P.depthRobust_path (hDepth hd) (P.layerFootprint_subset L.source d)
    Finset.Subset.rfl hcard

/-- The base link supplied by `first-source lemma`, with all set and path conclusions proved
from the actual challenge footprint and the assumed depth robustness. -/
noncomputable def base (hn : 0 < n) (hσapi : T.σ ≤ G.αpi)
    (hDepth : G.DepthRobust G.αpi) {b : ℕ} (hb : b < ℓ)
    (hexp : Expandable P.budget T.ghat b)
    (hfert : S.pi ≤ weight n (P.layerFootprint A b)) : Link P T A := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint A b).card : ℝ) := by
    unfold weight at hfert
    rwa [le_div_iff₀ hnreal] at hfert
  let hpath :=
    P.depthRobust_path (hDepth hb) (P.layerFootprint_subset A b) Finset.Subset.rfl hcard
  let Q := Classical.choose hpath
  have hQspec := Classical.choose_spec hpath
  have hQF : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint A b := hQspec.1
  have hQlen : G.αpi * n ≤ (Q.length : ℝ) := hQspec.2
  let k : ℕ := ⌈T.σ * n⌉₊
  have hk : k ≤ Q.length := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hσapi (Nat.cast_nonneg n)).trans hQlen
  let source := prefixSource Q k hk
  have hsourceCard : source.card = k := prefixSource_card Q k hk
  have hsourceF : source ⊆ P.layerFootprint A b :=
    prefixSource_subset_of_path Q k hk hQF
  have hsourceLayer : source ⊆ G.layer b :=
    hsourceF.trans (P.layerFootprint_subset A b)
  have hsourceAvail : ∀ v ∈ source, P.unpebbled v :=
    prefixSource_available Q k hk
  have hsourceWeight : T.σ ≤ weight n source := by
    have hceil : T.σ * n ≤ (k : ℝ) := Nat.le_ceil _
    unfold weight
    rw [hsourceCard, le_div_iff₀ hnreal]
    exact hceil
  have hlastF : Q.last ∈ P.layerFootprint A b := hQF Q.last Q.last_mem
  have hfoot := (P.mem_layerFootprint A).mp hlastF |>.2
  let a := Classical.choose hfoot
  have haspec := Classical.choose_spec hfoot
  have haA : a ∈ A := haspec.1
  let R := Classical.choose haspec.2
  have hRspec := Classical.choose_spec haspec.2
  have hRfirst : R.first = Q.last := hRspec.1
  have hRlast : R.last = a := hRspec.2
  have hjoin : Q.last = R.first := hRfirst.symm
  let QR := Q.append R hjoin
  have hrealized : P.HasUnpebbledPathInFootprint A (chainPathLength G T 1) := by
    refine ⟨QR.first, a, haA, QR, rfl, ?_, ?_⟩
    · simpa [QR] using hRlast
    · have hlen : Q.length ≤ QR.length := by
        rw [Path.append_length]
        have := R.length_pos
        omega
      simp only [chainPathLength, Nat.cast_one, sub_self, zero_mul, add_zero]
      have hlen' : (Q.length : ℝ) ≤ (QR.length : ℝ) := by
        exact_mod_cast hlen
      exact hQlen.trans hlen'
  refine {
    depth := b
    inside := hb
    source := source
    source_layer := hsourceLayer
    source_available := hsourceAvail
    source_weight := hsourceWeight
    expandable := hexp
    count := 1
    count_pos := by omega
    tail := ?_
    realized := hrealized
  }
  intro v hv
  rcases (mem_prefixSource Q k hk).mp hv with ⟨i, hi⟩
  have hiQ : i.val < Q.length := lt_of_lt_of_le i.isLt hk
  let D := Q.drop i.val hiQ
  have hDfirst : D.first = v := by simpa [D] using (Path.drop_first Q i.val hiQ).trans hi
  have hDlast : D.last = R.first := (Path.drop_last Q i.val hiQ).trans hjoin
  let DR := D.append R hDlast
  refine ⟨a, haA, DR, by simpa [DR] using hDfirst, by simpa [DR] using hRlast, ?_⟩
  have hsuffix : (G.αpi - T.σ) * n ≤ ((Q.length - i.val : ℕ) : ℝ) :=
    prefix_suffix_length T.σ_pos hσapi hn Q hQlen i.isLt
  have hlen : D.length ≤ DR.length := by
    rw [Path.append_length]
    have := R.length_pos
    omega
  simp only [Nat.cast_one, one_mul]
  have hlen' : (D.length : ℝ) ≤ (DR.length : ℝ) := by
    exact_mod_cast hlen
  exact hsuffix.trans (by simpa [D] using hlen')

/-- Extend a concrete chain at a later fertile, expandable depth.  The connector from
the new local path to the previous source is obtained from the *actual* footprint;
the stored `tail` certificate supplies all accumulated links. -/
noncomputable def extend (hn : 0 < n) (hσapi : T.σ ≤ G.αpi)
    (hDepthRobust : G.DepthRobust G.αpi)
    (L : Link P T A) {b : ℕ} (hdepth : L.depth < b) (hb : b < ℓ)
    (hexp : Expandable P.budget T.ghat b)
    (hfert : S.pi ≤ weight n (P.layerFootprint L.source b)) : Link P T A := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  let hpath := L.local_path hn hb hDepthRobust hfert
  let Q := Classical.choose hpath
  have hQspec := Classical.choose_spec hpath
  have hQF : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint L.source b := hQspec.1
  have hQlen : G.αpi * n ≤ (Q.length : ℝ) := hQspec.2
  let k : ℕ := ⌈T.σ * n⌉₊
  have hk : k ≤ Q.length := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hσapi (Nat.cast_nonneg n)).trans hQlen
  let source := prefixSource Q k hk
  have hsourceCard : source.card = k := prefixSource_card Q k hk
  have hsourceF : source ⊆ P.layerFootprint L.source b :=
    prefixSource_subset_of_path Q k hk hQF
  have hsourceLayer : source ⊆ G.layer b :=
    hsourceF.trans (P.layerFootprint_subset L.source b)
  have hsourceAvail : ∀ v ∈ source, P.unpebbled v :=
    prefixSource_available Q k hk
  have hsourceWeight : T.σ ≤ weight n source := by
    have hceil : T.σ * n ≤ (k : ℝ) := Nat.le_ceil _
    unfold weight
    rw [hsourceCard, le_div_iff₀ hnreal]
    exact hceil
  have hlastF : Q.last ∈ P.layerFootprint L.source b := hQF Q.last Q.last_mem
  have hfoot := (P.mem_layerFootprint L.source).mp hlastF |>.2
  let y := Classical.choose hfoot
  have hyspec := Classical.choose_spec hfoot
  have hySource : y ∈ L.source := hyspec.1
  let R := Classical.choose hyspec.2
  have hRspec := Classical.choose_spec hyspec.2
  have hRfirst : R.first = Q.last := hRspec.1
  have hRlast : R.last = y := hRspec.2
  have hQdepth : G.depth Q.last = b :=
    (G.layer_mem.mp ((P.mem_layerFootprint L.source).mp hlastF |>.1)).1
  have hyDepth : G.depth y = L.depth := (G.layer_mem.mp (L.source_layer hySource)).1
  have hdepthNe : G.depth Q.last ≠ G.depth y := by
    rw [hQdepth, hyDepth]
    omega
  have hRlen : 2 ≤ R.length :=
    reaches_path_length_two R hRfirst hRlast hdepthNe
  let hOld := L.tail y hySource
  let a := Classical.choose hOld
  have haSpec := Classical.choose_spec hOld
  have haA : a ∈ A := haSpec.1
  let O := Classical.choose haSpec.2
  have hOSpec := Classical.choose_spec haSpec.2
  have hOfirst : O.first = y := hOSpec.1
  have hOlast : O.last = a := hOSpec.2.1
  have hOlen : (L.count : ℝ) * (G.αpi - T.σ) * n ≤ (O.length : ℝ) :=
    hOSpec.2.2
  have hQRjoin : Q.last = R.first := hRfirst.symm
  let QR := Q.append R hQRjoin
  have hROjoin : QR.last = O.first := by
    simpa [QR] using hRlast.trans hOfirst.symm
  let QRO := QR.append O hROjoin
  have hrealized :
      P.HasUnpebbledPathInFootprint A (chainPathLength G T (L.count + 1)) := by
    refine ⟨QRO.first, a, haA, QRO, rfl, ?_, ?_⟩
    · simpa [QRO] using hOlast
    · have hlen : Q.length + O.length ≤ QRO.length := by
        simp only [QRO, QR, Path.append_length]
        have hQpos := Q.length_pos
        have hOpos := O.length_pos
        omega
      have hlen' : (Q.length : ℝ) + (O.length : ℝ) ≤ (QRO.length : ℝ) := by
        exact_mod_cast hlen
      have hsum : G.αpi * n +
          (L.count : ℝ) * (G.αpi - T.σ) * n ≤ (QRO.length : ℝ) := by
        linarith
      have hformula : chainPathLength G T (L.count + 1) =
          G.αpi * n + (L.count : ℝ) * (G.αpi - T.σ) * n := by
        simp only [chainPathLength, Nat.cast_add, Nat.cast_one]
        ring
      rw [hformula]
      exact hsum
  refine {
    depth := b
    inside := hb
    source := source
    source_layer := hsourceLayer
    source_available := hsourceAvail
    source_weight := hsourceWeight
    expandable := hexp
    count := L.count + 1
    count_pos := by omega
    tail := ?_
    realized := hrealized
  }
  intro v hv
  rcases (mem_prefixSource Q k hk).mp hv with ⟨i, hi⟩
  have hiQ : i.val < Q.length := lt_of_lt_of_le i.isLt hk
  let D := Q.drop i.val hiQ
  have hDfirst : D.first = v := by
    simpa [D] using (Path.drop_first Q i.val hiQ).trans hi
  have hDRjoin : D.last = R.first :=
    (Path.drop_last Q i.val hiQ).trans hRfirst.symm
  let DR := D.append R hDRjoin
  have hDROjoin : DR.last = O.first := by
    simpa [DR] using hRlast.trans hOfirst.symm
  let DRO := DR.append O hDROjoin
  refine ⟨a, haA, DRO, by simpa [DRO, DR] using hDfirst,
    by simpa [DRO] using hOlast, ?_⟩
  have hsuffix : (G.αpi - T.σ) * n ≤ ((Q.length - i.val : ℕ) : ℝ) :=
    prefix_suffix_length T.σ_pos hσapi hn Q hQlen i.isLt
  have hlen : D.length + O.length ≤ DRO.length := by
    simp only [DRO, DR, Path.append_length]
    have hDpos := D.length_pos
    have hOpos := O.length_pos
    omega
  have hlen' : (D.length : ℝ) + (O.length : ℝ) ≤ (DRO.length : ℝ) := by
    exact_mod_cast hlen
  have hsum : (G.αpi - T.σ) * n +
      (L.count : ℝ) * (G.αpi - T.σ) * n ≤ (DRO.length : ℝ) := by
    have hDlen : (G.αpi - T.σ) * n ≤ (D.length : ℝ) := by
      simpa [D] using hsuffix
    linarith
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hsum

end Link

/-- The fully concrete chain system.  Its extension operation is no longer an abstract
graph-side axiom: it is `Link.extend`, proved above from actual reachability plus an
explicit uniform depth-robustness hypothesis. -/
noncomputable def chainSystem [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (A : Finset V) (hn : 0 < n) (hσapi : T.σ ≤ G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam) :
    ChainSystem S P.budget T ℓ
      (fun z => P.HasUnpebbledPathInFootprint A (chainPathLength G T z)) where
  Link := Link P T A
  depth := Link.depth
  wt := fun L => P.footprintBound L.depth T.σ
  bound := fun L => P.footprintBound_isBound L.depth T.σ
  init := fun L => P.footprintBound_start L.depth T.σ
  expandable := Link.expandable
  inside := Link.inside
  count := Link.count
  count_pos := Link.count_pos
  realizes := Link.realized
  extend := by
    intro L b hdepth hb hfert hexp
    have hactual : P.footprintBound L.depth T.σ b ≤
        weight n (P.layerFootprint L.source b) :=
      L.scalar_le_actual hn hnobreak (le_of_lt hdepth) hb
    let L' := Link.extend hn hσapi hDepth L hdepth hb hexp (hfert.trans hactual)
    exact ⟨L', rfl, rfl⟩

end Pebbling

end Concrete

end ProofOfSpace

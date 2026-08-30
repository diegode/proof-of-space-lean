import ProofOfSpace.Latency
import Mathlib.Probability.Distributions.Uniform

/-!
# Concrete graph constructions and their remaining certificates

`Latency.lean` consumes `LayeredGraph.DepthRobust` as a hypothesis about an abstract
graph.  This module names the actual graphs the development proposes for that slot and asks,
for each, whether the hypothesis is a theorem.

* `StandaloneGraph`: the reusable within-layer abstraction.
* `permutationStack`: bounded-degree vertical wiring by a tuple of permutations, with
  the realized expansion certificate carried explicitly.
* `DRSampleParentLaw`, `DRSampleSeed`, and `bucketSample`: the corrected sampler law,
  standalone graph, and deployed five-node MetaBucket contraction (indegree six).
* `FilecoinWithinLayerTarget`: the deployed `(0.2n, 0.2n)` within-layer requirement.

The deterministic half of the deployed argument is proved here, not assumed:
`intervalBlockTransfer` discharges the transfer obligation,
`bucketSample_nodeDR_of_blockNodeDR` composes it into the deployed pipeline, and
`DRSampleSeedLaw.exists_law` constructs the independent joint sampler law.
What remains open in Lean is probabilistic or literature-level, and each remaining
proposition carries a docstring saying exactly why: `PermutationExpansionWhpClaim`, and
the base block certificate for `DRSample` at the deployed size, whose distance from
the published bound is recorded by `filecoin_budget_exceeds_published_certificate` and
`filecoin_depth_exceeds_published_certificate`.
-/

namespace ProofOfSpace

open Finset
open scoped ENNReal

universe u

namespace Concrete

/-! ### Standalone within-layer graphs and the stack over them -/

/-- A topologically ordered DAG on `Fin n`, to be used inside one layer. -/
structure StandaloneGraph (n : ℕ) where
  /-- The intra-layer edge relation. -/
  edge : Fin n → Fin n → Prop
  /-- Edges respect the node order, so the graph is acyclic. -/
  edge_lt : ∀ {u v}, edge u v → u.val < v.val

namespace StandaloneGraph

variable {n : ℕ}

/-- `(e, dep)` node depth robustness: deleting at most `e` nodes leaves a directed
path on at least `dep` surviving nodes.  Path length is counted in nodes, as
everywhere in this development. -/
def NodeDR (H : StandaloneGraph n) (e dep : ℝ) : Prop :=
  ∀ X : Finset (Fin n), ((X.card : ℝ) ≤ e) →
    ∃ p : List (Fin n), p ≠ [] ∧ p.IsChain H.edge ∧
      (∀ v ∈ p, v ∉ X) ∧ dep ≤ (p.length : ℝ)

theorem NodeDR.mono {H : StandaloneGraph n} {e e' dep dep' : ℝ}
    (h : H.NodeDR e dep) (he : e' ≤ e) (hdep : dep' ≤ dep) : H.NodeDR e' dep' := by
  intro X hX
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h X (hX.trans he)
  exact ⟨p, hp, hchain, hmem, hdep.trans hlen⟩

/-! ### Block variants on a standalone layer -/

/-- The length-`B` interval ending at one of the selected nodes.  This is the
zero-based version of the development's `N_B(T)`. -/
def blockNeighborhood (B : ℕ) (T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ t ∈ T, v.val ≤ t.val ∧ t.val < v.val + B

/-- `(E,D,B)` block-depth robustness in the exact deletion convention used by ABH and
the BucketSample metagraph argument. -/
def BlockNodeDR (H : StandaloneGraph n) (E D : ℝ) (B : ℕ) : Prop :=
  ∀ T : Finset (Fin n), ((T.card : ℝ) ≤ E) →
    ∃ p : List (Fin n), p ≠ [] ∧ p.IsChain H.edge ∧
      (∀ v ∈ p, v ∉ blockNeighborhood B T) ∧ D ≤ (p.length : ℝ)

/-- A usable finite formulation of an indegree bound. -/
def InDegreeAtMost (H : StandaloneGraph n) (d : ℕ) : Prop :=
  ∀ v : Fin n, ∃ P : Finset (Fin n), P.card ≤ d ∧ ∀ u, H.edge u v → u ∈ P

theorem mem_blockNeighborhood_self {B : ℕ} (hB : 0 < B) {T : Finset (Fin n)}
    {v : Fin n} (hv : v ∈ T) : v ∈ blockNeighborhood B T := by
  simp only [blockNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hv, le_rfl, by omega⟩

/-- Block robustness in particular implies ordinary node depth robustness with the same
deletion and depth coordinates. -/
theorem BlockNodeDR.nodeDR {H : StandaloneGraph n} {E D : ℝ} {B : ℕ}
    (hB : 0 < B) (h : H.BlockNodeDR E D B) : H.NodeDR E D := by
  intro X hX
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h X hX
  exact ⟨p, hp, hchain, fun v hv hvX => hmem v hv (mem_blockNeighborhood_self hB hvX),
    hlen⟩

end StandaloneGraph

/-! ### Bounded-degree permutation interlayers -/

/-- A degree-`d` bipartite multigraph represented by `d` permutations.  This is the
finite object sampled by the Chung construction between two consecutive layers. -/
structure PermutationInterlayer (n d : ℕ) where
  perm : Fin d → Equiv.Perm (Fin n)
deriving Fintype

instance : Nonempty (PermutationInterlayer n d) :=
  ⟨⟨fun _ => Equiv.refl (Fin n)⟩⟩

namespace PermutationInterlayer

/-- Distinct predecessors reached from a set of children. -/
def neighborhood {n d : ℕ} (P : PermutationInterlayer n d) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  T.biUnion fun v => Finset.univ.image fun j : Fin d => P.perm j v

/-- The exact deterministic expansion certificate required by `LayeredGraph.expands`. -/
def Expands {n d : ℕ} (P : PermutationInterlayer n d) (S : Setting) : Prop :=
  ∀ T : Finset (Fin n),
    S.β ((T.card : ℝ) / n) * n ≤ (P.neighborhood T).card

/-- A child has at most `d` distinct inter-layer parents. -/
theorem parent_candidates_card {n d : ℕ} (P : PermutationInterlayer n d) (v : Fin n) :
    (Finset.univ.image fun j : Fin d => P.perm j v).card ≤ d := by
  calc
    (Finset.univ.image fun j : Fin d => P.perm j v).card ≤ Finset.univ.card :=
      Finset.card_image_le
    _ = d := by simp

end PermutationInterlayer

/-- A genuine bounded-interdegree stack.  Consecutive layers are connected by a union
of `d` permutations.  The only required input is the exact expansion certificate for
each sampled interlayer. -/
noncomputable def permutationStack (H : StandaloneGraph n) (S : Setting) (ℓ d : ℕ)
    (α : ℝ) (_hn : 0 < n) (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) : LayeredGraph (ℕ × Fin n) S ℓ n where
  αpi := α
  layer k := if k < ℓ then Finset.univ.image (fun i : Fin n => (k, i)) else ∅
  depth v := v.1
  rank v := (ℓ - v.1) * n + v.2.val
  intra k u v := u.1 = k ∧ v.1 = k ∧ k < ℓ ∧ H.edge u.2 v.2
  inter k u v := u.1 = k + 1 ∧ v.1 = k ∧ k + 1 < ℓ ∧
    ∃ j : Fin d, u.2 = (P k).perm j v.2
  pred k T := if k + 1 < ℓ then
    ((P k).neighborhood ((T.filter fun v => v.1 = k).image Prod.snd)).image
      (fun i : Fin n => (k + 1, i)) else ∅
  layer_mem := by
    intro k v
    by_cases hk : k < ℓ
    · rw [if_pos hk]
      simp only [hk, and_true]
      constructor
      · intro hv
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
        rw [← hi]
      · intro hv
        exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
    · simp [hk]
  layer_card := by
    intro k hk
    rw [if_pos hk, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_univ, Fintype.card_fin]
  intra_mem := by
    rintro k u v ⟨hu, hv, hk, -⟩
    constructor <;> rw [if_pos hk]
    · exact Finset.mem_image.2 ⟨u.2, Finset.mem_univ _, by rw [← hu]⟩
    · exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
  inter_mem := by
    rintro k u v ⟨hu, hv, hk, -⟩
    constructor
    · rw [if_pos hk]
      exact Finset.mem_image.2 ⟨u.2, Finset.mem_univ _, by rw [← hu]⟩
    · rw [if_pos (show k < ℓ by omega)]
      exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
  intra_rank := by
    rintro k u v ⟨hu, hv, -, hedge⟩
    rw [hu, hv]
    exact Nat.add_lt_add_left (H.edge_lt hedge) _
  inter_rank := by
    rintro k u v ⟨hu, hv, hk, -⟩
    have hsplit : (ℓ - (k + 1)) * n + n = (ℓ - k) * n := by
      have : ℓ - k = (ℓ - (k + 1)) + 1 := by omega
      rw [this]
      ring
    calc
      (ℓ - u.1) * n + u.2.val < (ℓ - (k + 1)) * n + n := by rw [hu]; omega
      _ = (ℓ - k) * n := hsplit
      _ ≤ (ℓ - v.1) * n + v.2.val := by rw [hv]; omega
  pred_subset := by
    intro k T
    by_cases hk : k + 1 < ℓ
    · rw [if_pos hk, if_pos hk]
      exact Finset.image_subset_image (Finset.subset_univ _)
    · rw [if_neg hk]
      exact Finset.empty_subset _
  pred_edge := by
    intro k T u hu
    by_cases hk : k + 1 < ℓ
    · rw [if_pos hk] at hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
      rw [PermutationInterlayer.neighborhood, Finset.mem_biUnion] at hi
      obtain ⟨x, hx, hix⟩ := hi
      obtain ⟨j, -, hij⟩ := Finset.mem_image.1 hix
      obtain ⟨v, hvfilter, hvx⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_filter] at hvfilter
      refine ⟨v, hvfilter.1, rfl, hvfilter.2, hk, j, ?_⟩
      change i = (P k).perm j v.2
      rw [hvx]
      exact hij.symm
    · rw [if_neg hk] at hu
      simp at hu
  expands := by
    intro k T hk hT
    let I := (T.filter fun v => v.1 = k).image Prod.snd
    have hdepth : ∀ v ∈ T, v.1 = k := by
      intro v hv
      have := hT hv
      rw [if_pos (show k < ℓ by omega)] at this
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
      rw [← hi]
    have hfilter : T.filter (fun v => v.1 = k) = T :=
      Finset.filter_eq_self.2 hdepth
    have hIcard : I.card = T.card := by
      change ((T.filter fun v => v.1 = k).image Prod.snd).card = T.card
      rw [hfilter, Finset.card_image_iff.mpr]
      intro a ha b hb hab
      apply Prod.ext
      · exact (hdepth a ha).trans (hdepth b hb).symm
      · exact hab
    rw [if_pos hk, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    have hcert := hP k hk I
    rw [hIcard] at hcert
    simpa only [I] using hcert

@[simp] theorem permutationStack_layer (H : StandaloneGraph n) (S : Setting)
    (ℓ d : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) {k : ℕ} (hk : k < ℓ) :
    (permutationStack H S ℓ d α hn P hP).layer k =
      Finset.univ.image (fun i : Fin n => (k, i)) :=
  if_pos hk

/-- The deployed vertical degree. -/
abbrev Chung8Interlayer (n : ℕ) := PermutationInterlayer n 8

/-- The degree-eight specialization of the bounded-degree permutation stack. -/
noncomputable abbrev chung8Stack (H : StandaloneGraph n) (S : Setting) (ℓ : ℕ) (α : ℝ)
    (hn : 0 < n) (P : ℕ → Chung8Interlayer n)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) : LayeredGraph (ℕ × Fin n) S ℓ n :=
  permutationStack H S ℓ 8 α hn P hP

/-- Changing the vertical wiring does not change the exact within-layer robustness
question. -/
theorem permutationStack_nodeDepthRobustAt_iff (H : StandaloneGraph n) (S : Setting)
    (ℓ d : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) {k : ℕ} (hk : k < ℓ) {e dep : ℝ} :
    (permutationStack H S ℓ d α hn P hP).NodeDepthRobustAt k e dep ↔
      H.NodeDR e dep := by
  classical
  set G := permutationStack H S ℓ d α hn P hP with hG
  have hlayer : G.layer k = Finset.univ.image (fun i : Fin n => (k, i)) :=
    permutationStack_layer H S ℓ d α hn P hP hk
  constructor
  · intro hstack Y hY
    have hXcard : (((Y.image (fun i : Fin n => (k, i))).card : ℝ)) ≤ e := by
      rwa [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    have hXsub : Y.image (fun i : Fin n => (k, i)) ⊆ G.layer k := by
      rw [hlayer]
      exact Finset.image_subset_image (Finset.subset_univ _)
    obtain ⟨p, hp, hchain, hmem, hlen⟩ := hstack _ hXsub hXcard
    refine ⟨p.map Prod.snd, by simpa using hp, ?_, ?_, by simpa using hlen⟩
    · refine List.isChain_map_of_isChain Prod.snd ?_ hchain
      rintro a b ⟨-, -, -, hedge⟩
      exact hedge
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      intro hcon
      have hwmem := hmem w hw
      rw [Finset.mem_sdiff] at hwmem
      refine hwmem.2 (Finset.mem_image.2 ⟨w.2, hcon, ?_⟩)
      have hwk : w.1 = k := by
        have := hwmem.1
        rw [hlayer] at this
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
        rw [← hi]
      exact Prod.ext hwk.symm rfl
  · intro hH X hX hXcard
    have hYcard : (((X.image Prod.snd).card : ℝ)) ≤ e := by
      refine le_trans ?_ hXcard
      exact_mod_cast Finset.card_image_le
    obtain ⟨p, hp, hchain, hmem, hlen⟩ := hH _ hYcard
    refine ⟨p.map (fun i : Fin n => (k, i)), by simpa using hp, ?_, ?_, by simpa using hlen⟩
    · exact List.isChain_map_of_isChain _ (fun a b h => ⟨rfl, rfl, hk, h⟩) hchain
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      rw [Finset.mem_sdiff, hlayer]
      refine ⟨Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩, fun hcon => ?_⟩
      exact hmem w hw (Finset.mem_image.2 ⟨(k, w), hcon, rfl⟩)

/-- A standalone certificate therefore supplies ordinary depth robustness for the
bounded-degree Chung stack as well. -/
theorem permutationStack_depthRobust_of_nodeDR (H : StandaloneGraph n) (S : Setting)
    (ℓ d : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S)
    (hDR : H.NodeDR ((1 - S.pi) * n) (α * n)) :
    (permutationStack H S ℓ d α hn P hP).DepthRobust α := by
  intro k hk
  exact (permutationStack H S ℓ d α hn P hP).depthRobustAt_of_nodeDepthRobustAt hk
    ((permutationStack_nodeDepthRobustAt_iff H S ℓ d α hn P hP hk).mpr hDR)

/-! ### DRSample, and the depth robustness Filecoin assumes of it

Nodes are `0, …, n-1`, the zero-based translation of the development's `[n]`.  Vertex
`v ≥ 2` has two parents: the line parent `v-1`, and a sampled parent `v-g`.  In
`DRSample.GetParent`, a bucket `i ∈ [1, ⌊log₂(v+1)⌋+1]` is selected, its capped upper
endpoint is `c = min(v, 2^i)`, and then `g ∈ [max(⌊c/2⌋,2),c]` is selected.  The
lower bound `2` keeps the random parent distinct from the line parent.  A *seed* fixes
that draw for every node; the probability law is defined below. -/

/-- The gaps the published `DRSample.GetParent` may sample at zero-based node `v`,
as a predicate on the parent `u`.

The cap is taken *before* halving.  This matters in the last, truncated bucket, and the
extra `+1` in the bucket bound and the lower bound `2` are both present in Algorithm 1
of \cite{CCS:AlwBloHar17}. -/
def DRSampleAdmissible (v u : ℕ) : Prop :=
  ∃ i g, 1 ≤ i ∧ i ≤ Nat.log 2 (v + 1) + 1 ∧
    max (min v (2 ^ i) / 2) 2 ≤ g ∧ g ≤ min v (2 ^ i) ∧ u + g = v

/-! #### The exact one-node sampling law

The support predicate above is not a probability distribution: Algorithm 1 first samples
a bucket uniformly and only then samples uniformly inside that bucket.  The following
dependent finite types retain that two-stage law exactly, including overlaps between
buckets. -/

/-- Zero-based representation of the uniformly sampled bucket index. -/
abbrev DRSampleBucket (v : ℕ) := Fin (Nat.log 2 (v + 1) + 1)

/-- The development's one-based bucket number. -/
def DRSampleBucket.index {v : ℕ} (i : DRSampleBucket v) : ℕ := i.val + 1

/-- Capped upper end of bucket `i`. -/
def DRSampleBucket.cap {v : ℕ} (i : DRSampleBucket v) : ℕ :=
  min v (2 ^ i.index)

/-- Inclusive lower end of bucket `i`. -/
def DRSampleBucket.low {v : ℕ} (i : DRSampleBucket v) : ℕ :=
  max (i.cap / 2) 2

theorem DRSampleBucket.low_le_cap {v : ℕ} (hv : 2 ≤ v) (i : DRSampleBucket v) :
    i.low ≤ i.cap := by
  have hpow : 2 ≤ 2 ^ i.index := by
    rw [DRSampleBucket.index, pow_succ]
    have := (Nat.one_le_two_pow : 1 ≤ 2 ^ i.val)
    omega
  simp only [DRSampleBucket.low, DRSampleBucket.cap]
  omega

/-- A uniformly sampled gap in the selected bucket. -/
def DRSampleGap (v : ℕ) (_hv : 2 ≤ v) (i : DRSampleBucket v) :=
  {g : Fin (v + 1) // i.low ≤ g.val ∧ g.val ≤ i.cap}

instance (v : ℕ) (hv : 2 ≤ v) (i : DRSampleBucket v) : Nonempty (DRSampleGap v hv i) :=
  ⟨⟨⟨i.low, lt_of_le_of_lt (i.low_le_cap hv) (Nat.lt_succ_of_le (min_le_left _ _))⟩,
    le_rfl, i.low_le_cap hv⟩⟩

instance (v : ℕ) (hv : 2 ≤ v) (i : DRSampleBucket v) : Fintype (DRSampleGap v hv i) :=
  Subtype.fintype _

/-- A parent together with the proof that it lies in the published support. -/
def DRSampleParent (v : ℕ) := {u : Fin (v + 1) // DRSampleAdmissible v u.val}

/-- Given a bucket and a gap, compute the sampled parent. -/
def DRSampleGap.parent {v : ℕ} (hv : 2 ≤ v) (i : DRSampleBucket v)
    (g : DRSampleGap v hv i) : DRSampleParent v := by
  have hg : g.val ≤ v := g.property.2.trans (min_le_left _ _)
  refine ⟨⟨v - g.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, ?_⟩
  refine ⟨i.index, g.val, by simp [DRSampleBucket.index], ?_, g.property.1,
    g.property.2, ?_⟩
  · have := i.isLt
    simp only [DRSampleBucket.index]
    omega
  · change v - g.val + g.val = v
    exact Nat.sub_add_cancel hg

/-- The exact `GetParent(v)` probability mass function: uniform bucket, followed by a
uniform gap conditional on that bucket.  In particular this is generally *not* uniform
over `DRSampleAdmissible v`. -/
noncomputable def DRSampleParentLaw (v : ℕ) (hv : 2 ≤ v) : PMF (DRSampleParent v) :=
  (PMF.uniformOfFintype (DRSampleBucket v)).bind fun i => by
    exact (PMF.uniformOfFintype (DRSampleGap v hv i)).map (DRSampleGap.parent hv i)

/-- Every outcome of the exact one-node law satisfies the corrected support predicate,
by construction. -/
theorem DRSampleParentLaw_admissible (v : ℕ) (_hv : 2 ≤ v)
    (u : DRSampleParent v) : DRSampleAdmissible v u.val :=
  u.property

/-- Probability assigned to a property by a finite sampler.  This is the interface used
to state finite-size and high-probability claims without replacing them by existential
seed claims. -/
noncomputable def probabilityOf {A : Type*} (p : PMF A) (P : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if P a then p a else 0

/-- A conventional finite failure-probability formulation of "with high probability". -/
def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (P : A → Prop) (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p P

/-- The exact permutation-interlayer law: a uniformly sampled `d`-tuple of permutations,
equivalently `d` independent uniform permutations. -/
noncomputable def PermutationInterlayer.uniformLaw (n d : ℕ) :
    PMF (PermutationInterlayer n d) :=
  PMF.uniformOfFintype (PermutationInterlayer n d)

/-- Probability-facing form of the expansion claim required by a stack: that a sampled
`d`-tuple of permutations *realizes* `β` in the sense of `permutation-stack construction`.  This
development does not compute the probability — `stack realization proposition` and
`deployed-layer sufficiency result` take realization as a hypothesis — and neither does this
development.  Nothing below consumes this definition; it names the gap. -/
def PermutationExpansionWhpClaim (S : Setting) (n d : ℕ) (δ : ℝ≥0∞) : Prop :=
  HoldsWithFailureAtMost (PermutationInterlayer.uniformLaw n d)
    (fun P => P.Expands S) δ

/-- One draw of the `DRSample` sampler: the sampled parent of every node. -/
structure DRSampleSeed (n : ℕ) where
  /-- The sampled second parent. -/
  parent : Fin n → Fin n
  /-- It is one of the gaps the sampler can produce. -/
  admissible : ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (parent v).val

/-- A joint seed law is faithful to Algorithm 1 when every finite event involving
sampled parents factors into the exact one-node laws.  This records independence as
well as the nonuniform marginal caused by the bucket-then-gap draw. -/
structure DRSampleSeedLaw (n : ℕ) where
  pmf : PMF (DRSampleSeed n)
  exact_finite_events : ∀ (I : Finset (Fin n))
      (hI : ∀ v ∈ I, 2 ≤ v.val)
      (u : ∀ v : I, DRSampleParent v.val),
    probabilityOf pmf (fun s => ∀ v, ∀ hv : v ∈ I,
      (s.parent v).val = (u ⟨v, hv⟩).val) =
      ∏ v : I, DRSampleParentLaw v.val (hI v.val v.property) (u v)

namespace DRSampleSeedLaw

/-- A law on complete seeds exists: `independent` below constructs it as the exact
independent product of the one-node laws. -/
def Exists (n : ℕ) : Prop := Nonempty (DRSampleSeedLaw n)

/-! ### The independent `DRSample` seed law

`DRSampleParentLaw` gives the exact law of one node's random parent.  The joint law of
a whole seed is their independent product; this section constructs it and discharges
`DRSampleSeedLaw.Exists`. -/


/-- A seed is exactly an admissible parent function. -/
def seedEquiv (n : ℕ) :
    DRSampleSeed n ≃
      {f : Fin n → Fin n // ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val} where
  toFun s := ⟨s.parent, s.admissible⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeAdmissible (n : ℕ) :
    Fintype {f : Fin n → Fin n // ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val} := by
  classical exact Subtype.fintype _

noncomputable instance instFintypeSeed (n : ℕ) : Fintype (DRSampleSeed n) :=
  Fintype.ofEquiv _ (seedEquiv n).symm

/-- The parent of an admissible outcome, as a node of the whole layer. -/
def coordEmbed {n : ℕ} (v : Fin n) (x : DRSampleParent v.val) : Fin n :=
  ⟨x.val.val, lt_of_le_of_lt (Nat.lt_succ_iff.1 x.val.isLt) v.isLt⟩

theorem coordEmbed_injective {n : ℕ} (v : Fin n) :
    Function.Injective (coordEmbed v) := by
  intro x y hxy
  refine Subtype.ext (Fin.ext ?_)
  simpa [coordEmbed, Fin.ext_iff] using hxy

/-- `GetParent(v)` as a law on the whole layer.  Nodes below `2` have no random parent
and are given a point mass, which no `DRSampleSeed` field constrains. -/
noncomputable def coordLaw {n : ℕ} (v : Fin n) : PMF (Fin n) :=
  if h : 2 ≤ v.val then (DRSampleParentLaw v.val h).map (coordEmbed v) else PMF.pure v

theorem coordLaw_apply {n : ℕ} {v : Fin n} (h : 2 ≤ v.val) (x : DRSampleParent v.val) :
    coordLaw v (coordEmbed v x) = DRSampleParentLaw v.val h x := by
  rw [coordLaw, dif_pos h, PMF.map_apply]
  refine (tsum_eq_single x ?_).trans (if_pos rfl)
  intro y hy
  exact if_neg fun hcon => hy ((coordEmbed_injective v hcon).symm)

/-- Outside the published support the law vanishes, which is what forces the product law
to live on `DRSampleSeed`. -/
theorem coordLaw_eq_zero_of_not_admissible {n : ℕ} {v w : Fin n} (h : 2 ≤ v.val)
    (hw : ¬ DRSampleAdmissible v.val w.val) : coordLaw v w = 0 := by
  rw [coordLaw, dif_pos h, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro x
  refine if_neg fun hcon => hw ?_
  have hval : w.val = x.val.val := by simpa [coordEmbed, Fin.ext_iff] using hcon
  rw [hval]
  exact x.property

/-- Summing the independent product over admissible functions is the same as summing it
over all functions. -/
theorem sum_seed_eq {n : ℕ} (F : (Fin n → Fin n) → ℝ≥0∞)
    (hF : ∀ f : Fin n → Fin n,
      ¬ (∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val) → F f = 0) :
    ∑ s : DRSampleSeed n, F s.parent = ∑ f : Fin n → Fin n, F f := by
  classical
  have h1 : ∑ f ∈ Finset.univ.filter
      (fun f : Fin n → Fin n => ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val),
        F f = ∑ f : Fin n → Fin n, F f := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro f _ hnot
    refine hF f ?_
    simpa using hnot
  have h2 : ∑ f ∈ Finset.univ.filter
      (fun f : Fin n → Fin n => ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val),
        F f
      = ∑ x : {f : Fin n → Fin n //
          ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val}, F x.val :=
    Finset.sum_subtype _ (by simp) _
  have h3 : ∑ s : DRSampleSeed n, F s.parent
      = ∑ x : {f : Fin n → Fin n //
          ∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val}, F x.val :=
    Fintype.sum_equiv (seedEquiv n) _ _ fun _ => rfl
  rw [h3, ← h2, h1]

theorem prod_coordLaw_eq_zero {n : ℕ} {f : Fin n → Fin n}
    (hf : ¬ (∀ v : Fin n, 2 ≤ v.val → DRSampleAdmissible v.val (f v).val)) :
    ∏ v : Fin n, coordLaw v (f v) = 0 := by
  push Not at hf
  obtain ⟨v, hv, hnot⟩ := hf
  exact Finset.prod_eq_zero (Finset.mem_univ v)
    (coordLaw_eq_zero_of_not_admissible hv hnot)

theorem sum_prod_coordLaw (n : ℕ) :
    ∑ f : Fin n → Fin n, ∏ v : Fin n, coordLaw v (f v) = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin n)))
    (fun v w => coordLaw v w)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Finset.prod_eq_one fun v _ => ?_
  have hv := (coordLaw v).tsum_coe
  rwa [tsum_fintype] at hv

/-- **The joint `DRSample` seed law.**  Independent coordinates, each distributed exactly
as `GetParent` of Algorithm 1. -/
noncomputable def independent (n : ℕ) : DRSampleSeedLaw n where
  pmf := PMF.ofFintype (fun s : DRSampleSeed n => ∏ v : Fin n, coordLaw v (s.parent v))
    (by rw [sum_seed_eq _ fun f hf => prod_coordLaw_eq_zero hf]; exact sum_prod_coordLaw n)
  exact_finite_events := by
    classical
    intro I hI u
    -- the prescribed parent of each constrained node, as a layer node
    set tgt : Fin n → Fin n := fun v => if hv : v ∈ I then coordEmbed v (u ⟨v, hv⟩) else v
      with htgt
    set tset : Fin n → Finset (Fin n) :=
      fun v => if v ∈ I then {tgt v} else Finset.univ with htset
    set g : Fin n → ℝ≥0∞ :=
      fun w => if hw : w ∈ I then DRSampleParentLaw w.val (hI w hw) (u ⟨w, hw⟩) else 1 with hg
    -- the event is exactly membership in the product of the prescribed singletons
    have hiff : ∀ s : DRSampleSeed n,
        (∀ (v : Fin n) (hv : v ∈ I), (s.parent v).val = ((u ⟨v, hv⟩).val).val)
          ↔ s.parent ∈ Fintype.piFinset tset := by
      intro s
      rw [Fintype.mem_piFinset]
      constructor
      · intro h v
        by_cases hv : v ∈ I
        · rw [htset]
          simp only [if_pos hv, Finset.mem_singleton, htgt, dif_pos hv]
          exact Fin.ext (h v hv)
        · rw [htset]; simp [hv]
      · intro h v hv
        have := h v
        rw [htset] at this
        simp only [if_pos hv, Finset.mem_singleton, htgt, dif_pos hv] at this
        exact congrArg Fin.val this
    -- left-hand side
    have hLHS : probabilityOf
        (PMF.ofFintype (fun s : DRSampleSeed n => ∏ v : Fin n, coordLaw v (s.parent v))
          (by rw [sum_seed_eq _ fun f hf => prod_coordLaw_eq_zero hf];
              exact sum_prod_coordLaw n))
        (fun s => ∀ (v : Fin n) (hv : v ∈ I), (s.parent v).val = ((u ⟨v, hv⟩).val).val)
        = ∏ w ∈ I, g w := by
      rw [probabilityOf, tsum_fintype]
      trans (∑ s : DRSampleSeed n, if s.parent ∈ Fintype.piFinset tset then
              ∏ v : Fin n, coordLaw v (s.parent v) else 0)
      · refine Finset.sum_congr rfl fun s _ => ?_
        simp only [PMF.ofFintype_apply, hiff]
      rw [sum_seed_eq (fun f => if f ∈ Fintype.piFinset tset then
            ∏ v : Fin n, coordLaw v (f v) else 0) ?_]
      · rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.prod_univ_sum]
        have hfac : ∀ v : Fin n, ∑ w ∈ tset v, coordLaw v w
            = if v ∈ I then g v else 1 := by
          intro v
          by_cases hv : v ∈ I
          · rw [htset]
            simp only [if_pos hv, Finset.sum_singleton, htgt, dif_pos hv, hg]
            rw [coordLaw_apply (hI v hv)]
          · rw [htset]
            simp only [if_neg hv]
            have hcv := (coordLaw v).tsum_coe
            rwa [tsum_fintype] at hcv
        rw [Finset.prod_congr rfl fun v _ => hfac v, Finset.prod_ite_mem, Finset.univ_inter]
      · intro f hf
        simp [prod_coordLaw_eq_zero hf]
    rw [hLHS, ← Finset.prod_attach I g]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [hg]
    rw [dif_pos v.property]

/-- **`DRSampleSeedLaw.Exists` is a theorem.** -/
theorem exists_law (n : ℕ) : DRSampleSeedLaw.Exists n := ⟨independent n⟩

end DRSampleSeedLaw

namespace DRSampleSeed

variable {n : ℕ}

/-- The graph a seed produces: every line edge, plus the sampled edge at each `v ≥ 2`. -/
def graph (s : DRSampleSeed n) : StandaloneGraph n where
  edge u v := u.val + 1 = v.val ∨ (2 ≤ v.val ∧ u = s.parent v)
  edge_lt := by
    rintro u v (h | ⟨hv, rfl⟩)
    · omega
    · obtain ⟨i, g, hi, -, hg, -, hsum⟩ := s.admissible v hv
      have : 1 ≤ g := le_trans (by omega : 1 ≤ max (min v.val (2 ^ i) / 2) 2) hg
      omega

/-- `DRSample` has indegree at most two: the in-neighbours of `v` are among its line
parent and its sampled parent. -/
theorem indeg_le_two (s : DRSampleSeed n) (v : Fin n) {u : Fin n}
    (h : s.graph.edge u v) : u.val + 1 = v.val ∨ u = s.parent v := by
  rcases h with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

end DRSampleSeed

/-! ### Interval metagraph and the deployed BucketSample layer -/

/-- Contract consecutive intervals of `r` base nodes.  Self-loops caused by edges
inside one interval are discarded. -/
def intervalMetaGraph (r n : ℕ) (H : StandaloneGraph (r * n)) : StandaloneGraph n where
  edge u v := u.val < v.val ∧ ∃ a b : Fin (r * n),
    a.val / r = u.val ∧ b.val / r = v.val ∧ H.edge a b
  edge_lt h := h.1

/-- Base node `j` in the interval represented by metavertex `v`. -/
def intervalVertex {r n : ℕ} (v : Fin n) (j : Fin r) : Fin (r * n) :=
  ⟨r * v.val + j.val, by
    calc
      r * v.val + j.val < r * v.val + r := Nat.add_lt_add_left j.isLt _
      _ = r * (v.val + 1) := by simp [Nat.mul_add]
      _ ≤ r * n := Nat.mul_le_mul_left r (Nat.succ_le_of_lt v.isLt)⟩

/-- The metavertex containing the sampled parent of `intervalVertex v j`. -/
def sampledParentBlock {r n : ℕ} (hr : 0 < r) (s : DRSampleSeed (r * n))
    (v : Fin n) (j : Fin r) : Fin n :=
  ⟨(s.parent (intervalVertex v j)).val / r, by
    have hp := (s.parent (intervalVertex v j)).isLt
    apply (Nat.div_lt_iff_lt_mul hr).2
    calc
      (s.parent (intervalVertex v j)).val < r * n := hp
      _ = n * r := Nat.mul_comm r n⟩

/-- All possible parents of a BucketSample metavertex: one collapsed line parent and
at most one sampled-parent block for each of its `r` base nodes. -/
def bucketParentCandidates {r n : ℕ} (hr : 0 < r) (s : DRSampleSeed (r * n))
    (v : Fin n) : Finset (Fin n) :=
  insert ⟨v.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) v.isLt⟩
    (Finset.univ.image fun j : Fin r => sampledParentBlock hr s v j)

/-- The deployed `BucketSample[n,r]`/MetaBucket graph: the interval metagraph of a
standalone DRSample seed on `r*n` nodes. -/
def bucketSample {r n : ℕ} (s : DRSampleSeed (r * n)) : StandaloneGraph n :=
  intervalMetaGraph r n s.graph

/-- Every BucketSample edge enters through one of the explicit `r+1` candidates. -/
theorem bucketSample_edge_mem_candidates {r n : ℕ} (hr : 0 < r)
    (s : DRSampleSeed (r * n)) {u v : Fin n} (h : (bucketSample s).edge u v) :
    u ∈ bucketParentCandidates hr s v := by
  classical
  obtain ⟨huv, a, b, ha, hb, hab⟩ := h
  rcases hab with hline | ⟨hb2, hsamp⟩
  · have hadm := Nat.div_add_mod a.val r
    have har := Nat.mod_lt a.val hr
    have habound : b.val ≤ (a.val / r + 1) * r := by
      have heq : b.val = a.val + 1 := by omega
      calc
        b.val = a.val + 1 := heq
        _ = r * (a.val / r) + a.val % r + 1 := by omega
        _ ≤ r * (a.val / r) + r := Nat.add_le_add_left (Nat.succ_le_of_lt har) _
        _ = (a.val / r + 1) * r := by
          rw [Nat.add_mul, one_mul]
          simp [Nat.mul_comm]
    have hblt : b.val < (a.val / r + 2) * r :=
      habound.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) hr)
    have hqlt : b.val / r < a.val / r + 2 :=
      (Nat.div_lt_iff_lt_mul hr).2 hblt
    have hqle : b.val / r ≤ a.val / r + 1 := by omega
    have huvSucc : u.val + 1 = v.val := by omega
    simp only [bucketParentCandidates, Finset.mem_insert]
    left
    apply Fin.ext
    change u.val = v.val - 1
    omega
  · let j : Fin r := ⟨b.val % r, Nat.mod_lt _ hr⟩
    have hbvertex : intervalVertex v j = b := by
      apply Fin.ext
      change r * v.val + b.val % r = b.val
      rw [← hb]
      simpa [Nat.mul_comm] using Nat.div_add_mod b.val r
    simp only [bucketParentCandidates, Finset.mem_insert]
    right
    refine Finset.mem_image.2 ⟨j, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    have hsampVal := congrArg Fin.val hsamp
    change (s.parent (intervalVertex v j)).val / r = u.val
    rw [hbvertex, ← hsampVal, ha]

/-- Consequently `BucketSample[n,r]` has within-layer indegree at most `r+1`; the SDR
choice `r=5` has indegree at most six. -/
theorem bucketSample_indegree {r n : ℕ} (hr : 0 < r) (s : DRSampleSeed (r * n)) :
    (bucketSample s).InDegreeAtMost (r + 1) := by
  classical
  intro v
  refine ⟨bucketParentCandidates hr s v, ?_, fun _ h =>
    bucketSample_edge_mem_candidates hr s h⟩
  calc
    (bucketParentCandidates hr s v).card ≤
        (Finset.univ.image fun j : Fin r => sampledParentBlock hr s v j).card + 1 := by
      exact Finset.card_insert_le _ _
    _ ≤ r + 1 := Nat.add_le_add_right (by
      calc
        (Finset.univ.image fun j : Fin r => sampledParentBlock hr s v j).card ≤
            Finset.univ.card := Finset.card_image_le
        _ = r := by simp) 1

/-- Named deployed specialization. -/
abbrev MetaBucket5 {n : ℕ} (s : DRSampleSeed (5 * n)) : StandaloneGraph n :=
  bucketSample s

theorem metaBucket5_indegree {n : ℕ} (s : DRSampleSeed (5 * n)) :
    (MetaBucket5 s).InDegreeAtMost 6 := by
  simpa using bucketSample_indegree (r := 5) (n := n) (by norm_num) s

/-! The deterministic transfer result used by the development is a substantial list/path
argument, not a consequence of the graph definitions above.  It is stated here and
proved below, as `intervalBlockTransfer`. -/

/-- Exact interval-contraction transfer obligation, in this development's node-count
path convention. -/
def IntervalBlockTransfer : Prop :=
  ∀ {r n B E D : ℕ} {H : StandaloneGraph (r * n)},
    0 < r → r ≤ B → E ≤ n → H.BlockNodeDR E D B →
      (intervalMetaGraph r n H).BlockNodeDR E (D / r) (B / r)

/-! ### Collapsing a path along a partition of the node set -/

section Collapse

variable {α β : Type*} [DecidableEq β]

/-- Delete consecutive `blk`-duplicates from a list.  `b` is the block of the previously
processed element, so the accumulator is always the block of the immediate predecessor
along the list. -/
def collapseFrom (blk : α → β) : β → List α → List β
  | _, [] => []
  | b, a :: t =>
      if blk a = b then collapseFrom blk b t
      else blk a :: collapseFrom blk (blk a) t

/-- The block sequence visited by a nonempty list, with consecutive repeats removed. -/
def collapse (blk : α → β) (a₀ : α) (t : List α) : List β :=
  blk a₀ :: collapseFrom blk (blk a₀) t

theorem collapse_ne_nil (blk : α → β) (a₀ : α) (t : List α) :
    collapse blk a₀ t ≠ [] := List.cons_ne_nil _ _

/-- Consecutive distinct blocks along the list are joined by an edge of the original
list, so a chain collapses to a chain. -/
theorem collapse_chain {blk : α → β} {R : α → α → Prop} {M : β → β → Prop}
    (hmap : ∀ a a', R a a' → blk a ≠ blk a' → M (blk a) (blk a')) :
    ∀ (t : List α) (a₀ : α), List.IsChain R (a₀ :: t) →
      List.IsChain M (collapse blk a₀ t) := by
  intro t
  induction t with
  | nil => intro a₀ _; exact List.isChain_singleton _
  | cons a t ih =>
    intro a₀ h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hR, hchain⟩ := h
    by_cases hb : blk a = blk a₀
    · have hih := ih a hchain
      simp only [collapse, collapseFrom, if_pos hb]
      rw [collapse, hb] at hih
      exact hih
    · simp only [collapse, collapseFrom, if_neg hb]
      exact List.IsChain.cons_cons (hmap a₀ a hR fun hh => hb hh.symm) (ih a hchain)

/-- Every collapsed entry is the block of an actual list element. -/
theorem collapse_mem {blk : α → β} :
    ∀ (t : List α) (a₀ : α) (m : β), m ∈ collapse blk a₀ t → ∃ a ∈ a₀ :: t, blk a = m := by
  intro t
  induction t with
  | nil =>
    intro a₀ m hm
    simp only [collapse, collapseFrom, List.mem_singleton] at hm
    exact ⟨a₀, List.mem_cons_self, hm.symm⟩
  | cons a t ih =>
    intro a₀ m hm
    by_cases hb : blk a = blk a₀
    · simp only [collapse, collapseFrom, if_pos hb, List.mem_cons] at hm
      have hm' : m ∈ collapse blk a t := by
        rw [collapse, hb]; exact List.mem_cons.2 hm
      obtain ⟨x, hx, hxm⟩ := ih a m hm'
      exact ⟨x, List.mem_cons_of_mem a₀ hx, hxm⟩
    · simp only [collapse, collapseFrom, if_neg hb, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨a₀, List.mem_cons_self, rfl⟩
      · have hm' : m ∈ collapse blk a t := by
          rw [collapse]; exact List.mem_cons.2 hm
        obtain ⟨x, hx, hxm⟩ := ih a m hm'
        exact ⟨x, List.mem_cons_of_mem a₀ hx, hxm⟩

/-- Conversely every block met by the list appears in the collapse. -/
theorem mem_collapse {blk : α → β} :
    ∀ (t : List α) (a₀ : α) (x : α), x ∈ a₀ :: t → blk x ∈ collapse blk a₀ t := by
  intro t
  induction t with
  | nil =>
    intro a₀ x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact List.mem_cons_self
  | cons a t ih =>
    intro a₀ x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact List.mem_cons_self
    · have hih := ih a x hx'
      by_cases hb : blk a = blk a₀
      · simp only [collapse, collapseFrom, if_pos hb]
        rw [collapse, hb] at hih
        exact hih
      · simp only [collapse, collapseFrom, if_neg hb]
        exact List.mem_cons_of_mem _ hih

/-- If every block holds at most `r` elements and the list repeats nothing, the list is
at most `r` times as long as its collapse. -/
theorem length_le_collapse_mul {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (blk : α → β) (r : ℕ)
    (hfib : ∀ m : β, (Finset.univ.filter fun a : α => blk a = m).card ≤ r)
    (a₀ : α) (t : List α) (hnd : (a₀ :: t).Nodup) :
    (a₀ :: t).length ≤ (collapse blk a₀ t).length * r := by
  classical
  set q := collapse blk a₀ t with hq
  have hsub : (a₀ :: t).toFinset ⊆
      q.toFinset.biUnion fun m => Finset.univ.filter fun a : α => blk a = m := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_biUnion.2
      ⟨blk x, List.mem_toFinset.2 (mem_collapse t a₀ x hx),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  calc
    (a₀ :: t).length = (a₀ :: t).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (q.toFinset.biUnion fun m => Finset.univ.filter fun a : α => blk a = m).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _m ∈ q.toFinset, r := by
        refine (Finset.card_biUnion_le).trans ?_
        exact Finset.sum_le_sum fun m _ => hfib m
    _ = q.toFinset.card * r := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ q.length * r := Nat.mul_le_mul_right r (List.toFinset_card_le q)

end Collapse

/-! ### The interval contraction transfer -/

/-- The metavertex containing a base node. -/
def metaBlock {r n : ℕ} (hr : 0 < r) (a : Fin (r * n)) : Fin n :=
  ⟨a.val / r, by
    refine (Nat.div_lt_iff_lt_mul hr).2 ?_
    simpa [Nat.mul_comm] using a.isLt⟩

theorem metaBlock_val {r n : ℕ} (hr : 0 < r) (a : Fin (r * n)) :
    (metaBlock hr a).val = a.val / r := rfl

/-- Each metavertex is the image of at most `r` base nodes. -/
theorem metaBlock_fiber_card {r n : ℕ} (hr : 0 < r) (m : Fin n) :
    (Finset.univ.filter fun a : Fin (r * n) => metaBlock hr a = m).card ≤ r := by
  classical
  have : (Finset.univ.filter fun a : Fin (r * n) => metaBlock hr a = m).card ≤
      (Finset.univ : Finset (Fin r)).card := by
    refine Finset.card_le_card_of_injOn (fun a => ⟨a.val % r, Nat.mod_lt _ hr⟩)
      (fun a _ => Finset.mem_univ _) ?_
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have ha' : a.val / r = m.val := congrArg Fin.val ha.2
    have hb' : b.val / r = m.val := congrArg Fin.val hb.2
    have hmod : a.val % r = b.val % r := by simpa using congrArg Fin.val hab
    have hdiv : a.val / r = b.val / r := ha'.trans hb'.symm
    have hda := Nat.div_add_mod a.val r
    have hdb := Nat.div_add_mod b.val r
    rw [hdiv] at hda
    exact Fin.ext (by omega)
  simpa using this

theorem intervalBlockTransfer : IntervalBlockTransfer := by
  classical
  intro r n B E D H hr hrB _hEn hBlock T' hT'card
  -- Markers: the last base node of each selected block.
  have hlast : r - 1 < r := by omega
  set T : Finset (Fin (r * n)) :=
    T'.image (fun t => intervalVertex t ⟨r - 1, hlast⟩) with hTdef
  have hTcard : ((T.card : ℝ)) ≤ (E : ℝ) := by
    refine le_trans ?_ hT'card
    exact_mod_cast Finset.card_image_le
  obtain ⟨p, hp, hchain, hmiss, hlen⟩ := hBlock T hTcard
  obtain ⟨a₀, t, rfl⟩ := List.exists_cons_of_ne_nil hp
  set blk : Fin (r * n) → Fin n := metaBlock hr with hblk
  refine ⟨collapse blk a₀ t, collapse_ne_nil _ _ _, ?_, ?_, ?_⟩
  · -- the collapse is a chain in the metagraph
    refine collapse_chain (R := H.edge) ?_ t a₀ hchain
    intro a a' hedge hne
    refine ⟨?_, a, a', rfl, rfl, hedge⟩
    have hlt : a.val < a'.val := H.edge_lt hedge
    have hle : a.val / r ≤ a'.val / r := Nat.div_le_div_right hlt.le
    have : (blk a).val ≠ (blk a').val := fun hh => hne (Fin.ext hh)
    simp only [hblk, metaBlock_val] at this ⊢
    omega
  · -- the collapse avoids the contracted block neighbourhood
    intro m hm hmem
    obtain ⟨a, ha, ham⟩ := collapse_mem t a₀ m hm
    have hmiss' := hmiss a ha
    apply hmiss'
    simp only [StandaloneGraph.blockNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨s, hs, hs1, hs2⟩ := hmem
    refine ⟨intervalVertex s ⟨r - 1, hlast⟩, Finset.mem_image.2 ⟨s, hs, rfl⟩, ?_, ?_⟩
    all_goals
      have hmval : m.val = a.val / r := by rw [← ham]; rfl
      have hdm := Nat.div_add_mod a.val r
      have hmodlt : a.val % r < r := Nat.mod_lt _ hr
      have hA : r * (a.val / r) ≤ r * s.val := Nat.mul_le_mul_left r (by omega)
      have hB : r * (s.val + 1) ≤ r * (a.val / r) + r * (B / r) := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left r (by omega)
      have hBr : r * (B / r) ≤ B := Nat.mul_div_le B r
      have hiv : (intervalVertex s (⟨r - 1, hlast⟩ : Fin r)).val = r * s.val + (r - 1) := rfl
      rw [hiv]
      rw [Nat.mul_add, Nat.mul_one] at hB
      omega
  · -- the collapse is long enough
    have hnd : (a₀ :: t).Nodup := by
      have hlt : List.IsChain (fun a b : Fin (r * n) => a.val < b.val) (a₀ :: t) :=
        hchain.imp fun _ _ h => H.edge_lt h
      have hpw : List.Pairwise (fun a b : Fin (r * n) => a.val < b.val) (a₀ :: t) :=
        List.isChain_iff_pairwise.1 hlt
      exact hpw.imp fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h)
    have hcount : (a₀ :: t).length ≤ (collapse blk a₀ t).length * r :=
      length_le_collapse_mul blk r (metaBlock_fiber_card hr) a₀ t hnd
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    rw [div_le_iff₀ hrR]
    calc (D : ℝ) ≤ ((a₀ :: t).length : ℝ) := hlen
      _ ≤ (((collapse blk a₀ t).length * r : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = ((collapse blk a₀ t).length : ℝ) * r := by push_cast; ring

/-! ### The deployed transfer -/

theorem StandaloneGraph.BlockNodeDR.mono {n : ℕ} {H : StandaloneGraph n} {E E' D D' : ℝ}
    {B : ℕ} (h : H.BlockNodeDR E D B) (hE : E' ≤ E) (hD : D' ≤ D) :
    H.BlockNodeDR E' D' B := by
  intro T hT
  obtain ⟨p, hp, hchain, hmiss, hlen⟩ := h T (hT.trans hE)
  exact ⟨p, hp, hchain, hmiss, hD.trans hlen⟩

/-- **End-to-end deterministic pipeline for the deployed layer.**

A block certificate for the base `DRSample` graph on `r·n` nodes becomes ordinary node
depth robustness for the `BucketSample[n,r]` metagraph: `intervalBlockTransfer` contracts
it, and `BlockNodeDR.nodeDR` reads the path off the contracted certificate.  Both steps
are theorems, so the only remaining input is the base block certificate itself. -/
theorem bucketSample_nodeDR_of_blockNodeDR {r n E D B : ℕ}
    (hr : 0 < r) (hrB : r ≤ B) (hEn : E ≤ n)
    (seed : DRSampleSeed (r * n)) (hblock : seed.graph.BlockNodeDR (E : ℝ) (D : ℝ) B) :
    (bucketSample seed).NodeDR (E : ℝ) ((D / r : ℕ) : ℝ) := by
  have h1 := intervalBlockTransfer hr hrB hEn hblock
  have h2 : (bucketSample seed).BlockNodeDR (E : ℝ) ((D / r : ℕ) : ℝ) (B / r) :=
    h1.mono le_rfl (Nat.cast_div_le)
  exact h2.nodeDR ((Nat.one_le_div_iff hr).mpr hrB)

/-- **The within-layer depth robustness the Filecoin/SDR deployment assumes.**

The latency corollary takes `hαpi : G.αpi = 1/5` together with
`hDepth : G.DepthRobust G.αpi` at `π = 4/5`.  For a bounded-degree permutation stack
whose layers are the `DRSample` graph of a seed, that hypothesis is exactly this
statement: deleting any `n/5` nodes leaves a directed path on `n/5` survivors. -/
def FilecoinWithinLayerTarget (s : DRSampleSeed n) : Prop :=
  s.graph.NodeDR ((n : ℝ) / 5) ((n : ℝ) / 5)

/-- The probability-facing version of the deployed ordinary-depth claim.  Unlike
`DRSampleFilecoinConjecture`, this is a statement about the exact independent law. -/
def DRSampleFilecoinWhpClaim (L : DRSampleSeedLaw n) (δ : ℝ≥0∞) : Prop :=
  HoldsWithFailureAtMost L.pmf FilecoinWithinLayerTarget δ

/-! #### Exact integer target at `n = 2^30` -/

def FilecoinLayerSize : ℕ := 2 ^ 30
def FilecoinDeletionVertices : ℕ := FilecoinLayerSize / 5

/-- Floors are used for the deletion budget, which is also the promised path length: the
deployed target is `NodeDR (n/5) (n/5)` at `n = 2^30`. -/
theorem filecoin_exact_integer_values :
    FilecoinLayerSize = 1073741824 ∧
    FilecoinDeletionVertices = 214748364 := by
  have hsize : FilecoinLayerSize = 1073741824 := by
    norm_num [FilecoinLayerSize]
  refine ⟨hsize, ?_⟩
  rw [FilecoinDeletionVertices, hsize]

/-! ### What the published `DRSample` certificate delivers at `n = 2^30`

The theorems above are the whole deterministic half of the deployed argument.  What is
still missing is the *base* block certificate at the deployed size, and the two results
below record, as machine-checked arithmetic, how far the published one is from it.

The only published robustness theorem for `DRSample` is Theorem 3.1 of
\cite{CCS:AlwBloHar17}: a sampled graph is `(e, d, b)`-block-depth robust with high
probability for `e ≥ 2.43·10⁻⁴ N / log N`, `d ≥ 0.03 N`, `b ≥ 160 log N`.  At the deployed
base size `N = 5·2^30` that puts `e` in the tens of thousands. -/

/-- **The published deletion budget falls far short of the deployed one.**

For any block certificate whose deletion budget is at most `10^6` metavertices — two
orders of magnitude more generous than the published `Θ(N / log N)` bound at
`N = 5·2^30` — the deployed budget `⌊2^30/5⌋` already exceeds it, so the contracted
certificate covers none of the deletions the target allows. -/
theorem filecoin_budget_exceeds_published_certificate {E : ℕ} (hE : E ≤ 10 ^ 6) :
    ¬ (E > FilecoinDeletionVertices) := by
  have h : FilecoinDeletionVertices = 214748364 := filecoin_exact_integer_values.2
  omega

/-- **The published depth coordinate is short by more than a factor of six.**

Contracting intervals of `r = 5` divides the certified depth by `5`, so the published
`0.03 N` at `N = 5·2^30` becomes `0.03·2^30` metavertices, against the required
`⌊0.2·2^30⌋`.  Six times the published value is still below the target. -/
theorem filecoin_depth_exceeds_published_certificate :
    6 * (3 * FilecoinLayerSize / 100) < FilecoinDeletionVertices := by
  have h1 : FilecoinLayerSize = 1073741824 := filecoin_exact_integer_values.1
  have h2 : FilecoinDeletionVertices = 214748364 := filecoin_exact_integer_values.2
  rw [h1, h2]
  norm_num

/-- The target really is the latency theorem's graph hypothesis: a seed meeting it
yields a `LayeredGraph`, expansion included, satisfying `DepthRobust α_π` at
`α_π = 1/5`, for any `Setting` with `π = 4/5`. -/
theorem depthRobust_of_filecoinWithinLayerTarget {S : Setting} (hpi : S.pi = (4 : ℝ) / 5)
    (s : DRSampleSeed n) (ℓ d : ℕ) (hn : 0 < n)
    (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S)
    (h : FilecoinWithinLayerTarget s) :
    (permutationStack s.graph S ℓ d ((1 : ℝ) / 5) hn P hP).DepthRobust
      (permutationStack s.graph S ℓ d ((1 : ℝ) / 5) hn P hP).αpi := by
  refine permutationStack_depthRobust_of_nodeDR _ _ _ _ _ _ _ _
    (h.mono (le_of_eq ?_) (le_of_eq ?_))
  · rw [hpi]; ring
  · ring

/-- **Open.**  Whether *some* seed meets the target at the deployed size.  The sampler
draws a seed at random, so the deployed claim is that this holds with high probability;
`FilecoinWithinLayerTarget` is not a property of the construction's shape, as
`shortSeed_not_target` below shows.  The prior analysis records the question as unproved.
The two quantitative facts behind that are recorded here explicitly: the audited
certificate reaches deletion budget `4971` at `n = 2^30`, against the
`0.2 n = 214,748,364` demanded here, and at `n = 2^15` a local search *refutes* the
triple for one sampled graph. -/
def DRSampleFilecoinConjecture (n : ℕ) : Prop :=
  ∃ s : DRSampleSeed n, FilecoinWithinLayerTarget s

/-! #### The target is not universal over the sampler's support

The shortest *random* gap allowed by the published sampler is `g = 2`, not `g = 1`.
Choosing it everywhere gives the square of the line: all edges have gap one or two.
Deleting two consecutive nodes every ten positions separates this graph into constant
size pieces while using at most one fifth of the nodes.  Thus the target is not true of
every draw in the sampler's support.  This does not imply that a good seed cannot be
exhibited deterministically; it only rules out a support-only universal proof. -/

/-- The genuine DRSample seed that always draws the shortest random gap `g = 2`. -/
def shortSeed (n : ℕ) : DRSampleSeed n where
  parent v := ⟨v.val - 2, lt_of_le_of_lt (Nat.sub_le _ _) v.isLt⟩
  admissible := by
    intro v hv
    refine ⟨1, 2, le_refl _, by omega, ?_, ?_, ?_⟩
    · simp only [pow_one]
      omega
    · simp only [pow_one]
      omega
    · change v.val - 2 + 2 = v.val
      omega

theorem shortSeed_edge {n : ℕ} {u v : Fin n} (h : (shortSeed n).graph.edge u v) :
    u.val + 1 = v.val ∨ u.val + 2 = v.val := by
  rcases h with h | ⟨hv, h⟩
  · exact Or.inl h
  · right
    have : u.val = v.val - 2 := congrArg Fin.val h
    omega

/-- The two-node barriers used against `shortSeed`: the final two nodes of every
complete ten-node block. -/
def shortSeedBarrier (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val < 10 * (n / 10) ∧ 8 ≤ v.val % 10

theorem shortSeedBarrier_card (n : ℕ) : (shortSeedBarrier n).card = 2 * (n / 10) := by
  classical
  let q := n / 10
  let f : Fin q × Fin 2 → Fin n := fun x =>
    ⟨10 * x.1.val + 8 + x.2.val, by
      have hq : 10 * q ≤ n := Nat.mul_div_le n 10
      have hx := x.1.isLt
      have hy := x.2.isLt
      omega⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hb := b.isLt
    have hd := d.isLt
    have hval := congrArg Fin.val h
    dsimp only [f] at hval
    have hab : 8 + b.val < 10 := by omega
    have hcd : 8 + d.val < 10 := by omega
    have hdiva : (10 * a.val + 8 + b.val) / 10 = a.val := by omega
    have hdivc : (10 * c.val + 8 + d.val) / 10 = c.val := by omega
    have hac : a.val = c.val := by rw [← hdiva, hval, hdivc]
    have hacFin : a = c := Fin.ext hac
    subst c
    have hbd : b.val = d.val := by omega
    exact Prod.ext rfl (Fin.ext hbd)
  have hset : shortSeedBarrier n = Finset.univ.image f := by
    ext v
    constructor
    · intro hv
      rw [shortSeedBarrier, Finset.mem_filter] at hv
      have hr : v.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have hq : v.val / 10 < q := by
        dsimp only [q]
        omega
      have hres : v.val % 10 - 8 < 2 := by omega
      refine Finset.mem_image.2 ⟨(⟨v.val / 10, hq⟩, ⟨v.val % 10 - 8, hres⟩),
        Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp only [f]
      have hdivmod := Nat.div_add_mod v.val 10
      omega
    · rintro hv
      obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.1 hv
      simp only [shortSeedBarrier, Finset.mem_filter, Finset.mem_univ, true_and]
      have ha := a.isLt
      have hb := b.isLt
      have hq : 10 * q ≤ n := Nat.mul_div_le n 10
      constructor
      · change 10 * a.val + 8 + b.val < 10 * q
        omega
      · have hab : 8 + b.val < 10 := by omega
        have hmod : (10 * a.val + (8 + b.val)) % 10 = 8 + b.val := by
          rw [Nat.add_mod]
          simp [hab]
        change 8 ≤ (10 * a.val + 8 + b.val) % 10
        omega
  rw [hset, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  simp [q, Nat.mul_comm]

/-- A path with step size at most two cannot cross one of the two-node barriers;
all its nodes remain in one ten-node block. -/
theorem shortSeed_path_block {n : ℕ} : ∀ (p : List (Fin n)) (hp : p ≠ []),
    p.IsChain (shortSeed n).graph.edge →
    (∀ v ∈ p, v ∉ shortSeedBarrier n) →
    ∀ v ∈ p, v.val / 10 = (p.head hp).val / 10 := by
  intro p
  induction p with
  | nil => intro hp; exact absurd rfl hp
  | cons v q ih =>
    intro _ hchain hmem x hx
    simp only [List.head_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · cases q with
      | nil => simp at hx
      | cons w r =>
        have hvw := shortSeed_edge hchain.rel
        have hvnot := hmem v (by simp)
        have hwnot := hmem w (by simp)
        have hvres : v.val % 10 < 8 ∨ 10 * (n / 10) ≤ v.val := by
          rw [shortSeedBarrier, Finset.mem_filter] at hvnot
          push Not at hvnot
          by_cases hvfull : v.val < 10 * (n / 10)
          · exact Or.inl (hvnot (Finset.mem_univ _) hvfull)
          · exact Or.inr (Nat.le_of_not_gt hvfull)
        have hsame : v.val / 10 = w.val / 10 := by
          have hvlt := v.isLt
          have hwlt := w.isLt
          have hvdivmod := Nat.div_add_mod v.val 10
          have hwdivmod := Nat.div_add_mod w.val 10
          have hnmod := Nat.div_add_mod n 10
          rcases hvw with hvw | hvw <;> omega
        have htail := ih (by simp) hchain.of_cons
          (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) x hx
        simp only [List.head_cons] at htail
        exact htail.trans hsame.symm

/-- A strictly increasing path contained in one ten-node block has at most ten
nodes. -/
theorem shortSeed_path_length_le_ten {n : ℕ} (p : List (Fin n)) (hp : p ≠ [])
    (hchain : p.IsChain (shortSeed n).graph.edge)
    (hmem : ∀ v ∈ p, v ∉ shortSeedBarrier n) : p.length ≤ 10 := by
  have hlt : p.IsChain (fun a b : Fin n => a.val < b.val) :=
    hchain.imp (fun _ _ h => (shortSeed n).graph.edge_lt h)
  have hnodup : p.Nodup := by
    rw [List.isChain_iff_pairwise] at hlt
    exact hlt.nodup
  let b := (p.head hp).val / 10
  let vals := p.map Fin.val
  have hvalsNodup : vals.Nodup := by
    exact hnodup.map Fin.val_injective
  have hsub : vals.toFinset ⊆ Finset.Ico (10 * b) (10 * b + 10) := by
    intro x hx
    have hxv : x ∈ vals := List.mem_toFinset.mp hx
    obtain ⟨v, hvp, rfl⟩ := List.mem_map.mp hxv
    have hblock := shortSeed_path_block p hp hchain hmem v hvp
    rw [Finset.mem_Ico]
    have hvdivmod := Nat.div_add_mod v.val 10
    have hvmod := Nat.mod_lt v.val (by norm_num : 0 < 10)
    omega
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hvalsNodup, Nat.card_Ico] at hcard
  simpa only [vals, List.length_map, Nat.add_sub_cancel_left] using hcard

/-- **The `DRSample` shape does not give the Filecoin target.**  For every `n ≥ 51` the
sampler has an admissible draw whose graph fails `(0.2 n, 0.2 n)` depth robustness. -/
theorem shortSeed_not_target (n : ℕ) (hn : 51 ≤ n) :
    ¬ FilecoinWithinLayerTarget (shortSeed n) := by
  classical
  intro h
  let X := shortSeedBarrier n
  have hXcardNat : X.card ≤ n / 5 := by
    rw [show X.card = 2 * (n / 10) by simp only [X, shortSeedBarrier_card]]
    omega
  have hXcard : ((X.card : ℝ)) ≤ (n : ℝ) / 5 := by
    have h1 : ((X.card : ℝ)) ≤ (((n / 5 : ℕ)) : ℝ) := by
      exact_mod_cast hXcardNat
    have h2 : (((n / 5 : ℕ)) : ℝ) ≤ (n : ℝ) / 5 := Nat.cast_div_le
    linarith
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h X hXcard
  have hshort : p.length ≤ 10 := shortSeed_path_length_le_ten p hp hchain hmem
  have h10 : ((p.length : ℝ)) ≤ 10 := by exact_mod_cast hshort
  have h51 : (51 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

end Concrete

end ProofOfSpace

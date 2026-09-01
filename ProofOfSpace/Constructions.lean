import ProofOfSpace.Latency
import Mathlib.Probability.Distributions.Uniform

/-!
# Concrete Chung permutation stacks

This module contains exactly the construction layer used by the two public latency
theorems: an abstract within-layer DAG, a tuple-of-permutations interlayer, the resulting
stack, and the probability-facing expansion claim proved in `UnionBound.lean`.
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

/-- Expansion measured against an integer *failure profile* rather than a real-valued
`β`: no nonempty source set has a neighbourhood as small as `m` allows.  This is the form
the union bound needs, and it refers to no expansion function at all.  The empty set is
excluded because it can never be expanded. -/
def ExpandsProfile {n d : ℕ} (P : PermutationInterlayer n d) (m : ℕ → ℕ) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty → m T.card < (P.neighborhood T).card

end PermutationInterlayer

/-! ### Chung's one-permutation port model -/

/-- A degree-eight Chung interlayer is one permutation of all `8n` ports.  This is the
sampling model in Appendix A of Reyzin's paper; it is not a tuple of eight vertex
permutations. -/
structure PortInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)
deriving Fintype

instance : Nonempty (PortInterlayer n) := ⟨⟨Equiv.refl _⟩⟩

namespace PortInterlayer

/-- All eight ports belonging to the vertices in `T`. -/
def ports (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

@[simp] theorem card_ports (T : Finset (Fin n)) : (ports T).card = 8 * T.card := by
  simp [ports]

/-- Distinct predecessor vertices hit by the permuted ports of `T`. -/
def neighborhood (P : PortInterlayer n) (T : Finset (Fin n)) : Finset (Fin n) :=
  (ports T).image fun q => (P.perm q).2

/-- The operational expansion certificate consumed by the deterministic stack. -/
def Expands (P : PortInterlayer n) (S : Setting) : Prop :=
  ∀ (T : Finset (Fin n)) (x : ℝ),
    x ∈ Set.Icc S.αmin S.αmax → x ≤ (T.card : ℝ) / n →
      S.β x * n ≤ (P.neighborhood T).card

end PortInterlayer

/-- The layered stack built from Chung port permutations. -/
noncomputable def portStack (H : StandaloneGraph n) (S : Setting) (ℓ : ℕ)
    (α : ℝ) (_hn : 0 < n) (P : ℕ → PortInterlayer n)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) : LayeredGraph (ℕ × Fin n) S ℓ n where
  αpi := α
  layer k := if k < ℓ then Finset.univ.image (fun i : Fin n => (k, i)) else ∅
  depth v := v.1
  rank v := (ℓ - v.1) * n + v.2.val
  intra k u v := u.1 = k ∧ v.1 = k ∧ k < ℓ ∧ H.edge u.2 v.2
  inter k u v := u.1 = k + 1 ∧ v.1 = k ∧ k + 1 < ℓ ∧
    ∃ q ∈ PortInterlayer.ports ({v.2} : Finset (Fin n)), ((P k).perm q).2 = u.2
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
      rw [PortInterlayer.neighborhood] at hi
      obtain ⟨q, hq, hqi⟩ := Finset.mem_image.1 hi
      rw [PortInterlayer.ports, Finset.mem_product] at hq
      obtain ⟨v, hvfilter, hvq⟩ := Finset.mem_image.1 hq.2
      rw [Finset.mem_filter] at hvfilter
      refine ⟨v, hvfilter.1, rfl, hvfilter.2, hk, q, ?_, ?_⟩
      · rw [PortInterlayer.ports, Finset.mem_product]
        exact ⟨Finset.mem_univ _, by simp [hvq]⟩
      · exact hqi
    · rw [if_neg hk] at hu
      simp at hu
  expands := by
    intro k T x hk hT hxactive hx
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
    have hxI : x ≤ (I.card : ℝ) / n := by rwa [hIcard]
    rw [if_pos hk, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    exact hP k hk I x hxactive hxI

@[simp] theorem portStack_layer (H : StandaloneGraph n) (S : Setting)
    (ℓ : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PortInterlayer n)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) {k : ℕ} (hk : k < ℓ) :
    (portStack H S ℓ α hn P hP).layer k =
      Finset.univ.image (fun i : Fin n => (k, i)) :=
  if_pos hk

theorem portStack_nodeDepthRobustAt_iff (H : StandaloneGraph n) (S : Setting)
    (ℓ : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PortInterlayer n)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) {k : ℕ} (hk : k < ℓ) {e dep : ℝ} :
    (portStack H S ℓ α hn P hP).NodeDepthRobustAt k e dep ↔ H.NodeDR e dep := by
  classical
  set G := portStack H S ℓ α hn P hP with hG
  have hlayer : G.layer k = Finset.univ.image (fun i : Fin n => (k, i)) :=
    portStack_layer H S ℓ α hn P hP hk
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

theorem portStack_depthRobust_of_nodeDR (H : StandaloneGraph n) (S : Setting)
    (ℓ : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PortInterlayer n)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S)
    (hDR : H.NodeDR ((1 - S.pi) * n) (α * n)) :
    (portStack H S ℓ α hn P hP).DepthRobust α := by
  intro k hk
  exact (portStack H S ℓ α hn P hP).depthRobustAt_of_nodeDepthRobustAt hk
    ((portStack_nodeDepthRobustAt_iff H S ℓ α hn P hP hk).mpr hDR)

/-- The uniform law on one permutation of all degree-eight ports. -/
noncomputable def PortInterlayer.uniformLaw (n : ℕ) : PMF (PortInterlayer n) :=
  PMF.uniformOfFintype (PortInterlayer n)

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
    intro k T x hk hT hxactive hx
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
    have hnreal : (0 : ℝ) < n := by exact_mod_cast _hn
    have hactual0 : 0 ≤ (T.card : ℝ) / n :=
      div_nonneg (Nat.cast_nonneg _) hnreal.le
    have hactual1 : (T.card : ℝ) / n ≤ 1 := by
      rw [div_le_one hnreal]
      have hcard : T.card ≤ n := by
        calc
          T.card = I.card := hIcard.symm
          _ ≤ n := by simpa using Finset.card_le_univ I
      exact_mod_cast hcard
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨S.αmin_nonneg.trans hxactive.1, hxactive.2.trans S.αmax_le_one⟩
    have hβ : S.β x ≤ S.β ((T.card : ℝ) / n) :=
      S.β_strictMonoOn.monotoneOn hx01 ⟨hactual0, hactual1⟩ hx
    calc
      S.β x * n ≤ S.β ((T.card : ℝ) / n) * n :=
        mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg n)
      _ ≤ ((P k).neighborhood I).card := hcert

@[simp] theorem permutationStack_layer (H : StandaloneGraph n) (S : Setting)
    (ℓ d : ℕ) (α : ℝ) (hn : 0 < n) (P : ℕ → PermutationInterlayer n d)
    (hP : ∀ k, k + 1 < ℓ → (P k).Expands S) {k : ℕ} (hk : k < ℓ) :
    (permutationStack H S ℓ d α hn P hP).layer k =
      Finset.univ.image (fun i : Fin n => (k, i)) :=
  if_pos hk

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

end Concrete

end ProofOfSpace

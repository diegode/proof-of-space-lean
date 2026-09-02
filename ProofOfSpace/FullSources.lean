/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Latency

/-!
# Full-length path sources, and the family between them and the prefix

`PayChain.lean` carries the chain itself, parameterized by what one completed link is
worth.  A `SourceRule` is the whole of what the graph side supplies, and this module
proves the two rules that are not `sourceRule_prefix`.

The prefix rule of `PayChain.lean` reaches a footprint of weight `π`, takes *one*
depth-robust path of length `α_π n` inside it, and keeps the first `σ n` nodes of that
path as the next source.  A source node is then the `i`-th node of a prefix, so the
certificate it carries is only the suffix behind it and a link is worth `(α_π - σ) n`.

`sourceRule_full` replaces the prefix by a set of *full-length path sources*.  If the
footprint has weight `τ + σ` and the layer is depth robust at the lower threshold `τ`,
then at least `σ n` distinct nodes of the footprint each *begin* a path of length `α_π n`
inside it (`card_fullSources`).  Taking those as the source, every source node carries a
whole `α_π n`, so a link is worth `α_π n`.  The price is the threshold: everything the
ledger prices is stated at `S.pi`, so `S.pi` is here the *superfertile* threshold the
footprint must reach, and the graph assumption is depth robustness at `S.pi - T.σ`.

`sourceRule_mixed` is the family between the two.  It reads the *slack* `π - τ` between
the fertility threshold and the threshold the graph is actually robust at, spends `j` of
it on full-length source nodes, and fills the source up to weight `σ` with a prefix
chosen to avoid them; a link is worth `(α_π - σ) n + j`.  `j = 0` is the prefix rule and
`j = σ n` is the full rule, so no layer graph has to sit at either end.

Nothing in the accounting changes with the rule: all three produce the same `SourceData`,
so `payChainSystem` is a `ChainSystem` for the same `Setting`, `Budget` and `Tracking`,
and the ledger of `PotentialLedger.lean` prices it unchanged.  The trade reads in two
directions.  At a fixed certificate, keep `S.pi` and strengthen the graph assumption.  At
a fixed graph assumption, raise `S.pi` to `threshold + σ`, which re-prices the
certificate.

`latency_full_asymptotic` is the statement the slope lives in: for every layer count the
chain realizes `α_π/potSpan` of unpebbled path per layer past the head.
-/

namespace ProofOfSpace

namespace Concrete

open Finset Set

universe u

variable {V : Type u}

namespace LayeredGraph

variable {S : Setting} {ℓ n : ℕ} (G : LayeredGraph V S ℓ n)

/-- Depth robustness at an explicit threshold `τ`, rather than at the `Setting`'s `π`.
`LayeredGraph.DepthRobustAt` is the case `τ = S.pi`. -/
def DepthRobustAtThr (d : ℕ) (τ α : ℝ) : Prop :=
  ∀ F : Finset V, F ⊆ G.layer d → τ * n ≤ (F.card : ℝ) →
    ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
      (∀ v ∈ p, v ∈ F) ∧ α * n ≤ (p.length : ℝ)

/-- Uniform depth robustness at threshold `τ` over all layers. -/
def DepthRobustThr (τ α : ℝ) : Prop :=
  ∀ {d : ℕ}, d < ℓ → G.DepthRobustAtThr d τ α

theorem depthRobustAt_iff_thr {d : ℕ} {α : ℝ} :
    G.DepthRobustAt d α ↔ G.DepthRobustAtThr d S.pi α := Iff.rfl

theorem depthRobust_iff_thr {α : ℝ} :
    G.DepthRobust α ↔ G.DepthRobustThr S.pi α := Iff.rfl

/-- A lower threshold is a stronger assumption. -/
theorem DepthRobustAtThr.mono {d : ℕ} {τ τ' α : ℝ} (hτ : τ ≤ τ') (hn : 0 ≤ (n : ℝ))
    (h : G.DepthRobustAtThr d τ α) : G.DepthRobustAtThr d τ' α :=
  fun F hF hcard => h F hF ((mul_le_mul_of_nonneg_right hτ hn).trans hcard)

/-- Threshold-`τ` robustness is deletion-form robustness at budget `(1 - τ) n`.  This is
`depthRobustAt_of_nodeDepthRobustAt` with the threshold free, and it is the bridge to the
standalone-graph certificates of `Constructions.lean`, which are stated as deletion
budgets. -/
theorem depthRobustAtThr_of_nodeDepthRobustAt [DecidableEq V] {d : ℕ} {τ α : ℝ}
    (hd : d < ℓ) (h : G.NodeDepthRobustAt d ((1 - τ) * n) (α * n)) :
    G.DepthRobustAtThr d τ α := by
  intro F hF hFcard
  have hXcard : (((G.layer d \ F).card : ℝ)) ≤ (1 - τ) * n := by
    rw [Finset.card_sdiff_of_subset hF, Nat.cast_sub (Finset.card_le_card hF),
      G.layer_card hd]
    linarith
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h (G.layer d \ F) Finset.sdiff_subset hXcard
  refine ⟨p, hp, hchain, ?_, hlen⟩
  intro v hv
  have := hmem v hv
  rwa [Finset.sdiff_sdiff_eq_self hF] at this

/-- The converse, so that moving between the two APIs never silently strengthens the
graph hypothesis. -/
theorem nodeDepthRobustAt_of_depthRobustAtThr [DecidableEq V] {d : ℕ} {τ α : ℝ}
    (hd : d < ℓ) (h : G.DepthRobustAtThr d τ α) :
    G.NodeDepthRobustAt d ((1 - τ) * n) (α * n) := by
  intro X hX hXcard
  have hFcard : τ * n ≤ ((G.layer d \ X).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hX, Nat.cast_sub (Finset.card_le_card hX),
      G.layer_card hd]
    linarith
  obtain ⟨p, hp, hchain, hmem, hlen⟩ := h (G.layer d \ X) Finset.sdiff_subset hFcard
  exact ⟨p, hp, hchain, hmem, hlen⟩

/-! ### Full-length path sources -/

/-- The nodes of `F` that *begin* an intra-layer path of normalized length `α` all of
whose nodes lie in `F`. -/
noncomputable def fullSources (d : ℕ) (F : Finset V) (α : ℝ) : Finset V := by
  classical
  exact F.filter fun u => ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
    (∀ v ∈ p, v ∈ F) ∧ α * n ≤ (p.length : ℝ) ∧ p.head? = some u

theorem mem_fullSources {d : ℕ} {F : Finset V} {α : ℝ} {u : V} :
    u ∈ G.fullSources d F α ↔ u ∈ F ∧ ∃ p : List V, p ≠ [] ∧ p.IsChain (G.intra d) ∧
      (∀ v ∈ p, v ∈ F) ∧ α * n ≤ (p.length : ℝ) ∧ p.head? = some u := by
  classical
  simp [fullSources]

theorem fullSources_subset {d : ℕ} {F : Finset V} {α : ℝ} :
    G.fullSources d F α ⊆ F := fun _ hu => (G.mem_fullSources.mp hu).1

/-- **The full-length path-source lemma.**  A footprint of weight `τ + s` in a layer that
is depth robust at threshold `τ` contains at least `s n` distinct nodes, each of which
begins a path of length `α n` inside the footprint.

Deleting the sources from `F` would leave more than `τ n` nodes; depth robustness produces
a long path among them, and the first node of that path was a source after all. -/
theorem card_fullSources {d : ℕ} {F : Finset V} {τ s α : ℝ}
    (hDR : G.DepthRobustAtThr d τ α) (hF : F ⊆ G.layer d)
    (hcard : (τ + s) * n ≤ (F.card : ℝ)) :
    s * n ≤ ((G.fullSources d F α).card : ℝ) := by
  classical
  set Sr := G.fullSources d F α with hSr
  by_contra hcon
  push Not at hcon
  have hsub : Sr ⊆ F := G.fullSources_subset
  have hdiff : ((F \ Sr).card : ℝ) = (F.card : ℝ) - (Sr.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  have hbig : τ * n ≤ ((F \ Sr).card : ℝ) := by
    rw [hdiff]; nlinarith
  obtain ⟨p, hpne, hpchain, hpmem, hplen⟩ :=
    hDR (F \ Sr) (Finset.sdiff_subset.trans hF) hbig
  set u := p.head hpne with hu
  have huF : u ∈ F \ Sr := hpmem u (List.head_mem hpne)
  have huSr : u ∈ Sr := by
    rw [hSr, G.mem_fullSources]
    refine ⟨(Finset.mem_sdiff.mp huF).1, p, hpne, hpchain, ?_, hplen, ?_⟩
    · exact fun v hv => (Finset.mem_sdiff.mp (hpmem v hv)).1
    · rw [List.head?_eq_some_head hpne]
  exact (Finset.mem_sdiff.mp huF).2 huSr

end LayeredGraph

namespace Pebbling

variable {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n} {P : Pebbling G}

/-- A full-length source, converted to a genuine unpebbled path of the stacked graph that
starts at the source node.  This is `depthRobust_path` for one source. -/
theorem fullSource_path (P : Pebbling G) {A : Finset V} {d : ℕ} {F : Finset V} {α : ℝ}
    (hfoot : F ⊆ P.layerFootprint A d) {u : V} (hu : u ∈ G.fullSources d F α) :
    ∃ Q : Path G.edge P.unpebbled,
      Q.first = u ∧ (∀ v ∈ Q.nodes, v ∈ F) ∧ α * n ≤ (Q.length : ℝ) := by
  obtain ⟨-, p, hpne, hpchain, hpmem, hplen, hphead⟩ := G.mem_fullSources.mp hu
  let Q : Path G.edge P.unpebbled := {
    nodes := p
    nonempty := hpne
    chain := hpchain.imp fun _ _ h => Or.inl ⟨d, h⟩
    unpebbled' := by
      intro v hv
      exact P.footprint_available A ((P.mem_layerFootprint A).mp (hfoot (hpmem v hv))).2 }
  refine ⟨Q, ?_, hpmem, by simpa [Q, Path.length] using hplen⟩
  have hh : p.head? = some (p.head hpne) := List.head?_eq_some_head hpne
  exact Option.some.inj (hh.symm.trans hphead)

end Pebbling

namespace Pebbling

variable {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n} {P : Pebbling G}

/-- **The full-length source rule.**  At a *superfertile* footprint — one of weight `S.pi`
in a layer that is depth robust at the lower threshold `S.pi - T.σ` — the full-length
path-source lemma already produces `σ n` nodes each beginning a whole `α_π n` path inside
the footprint.  No prefix is taken, so nothing is lost to the suffix behind a source node
and the payoff is `y = α_π`. -/
noncomputable def sourceData_full [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi)
    {b : ℕ} (hb : b < ℓ) (D : Finset V)
    (hfert : S.pi ≤ weight n (P.layerFootprint D b)) :
    SourceData P T G.αpi D b := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint D b).card : ℝ) := by
    unfold weight at hfert
    rwa [le_div_iff₀ hnreal] at hfert
  -- the long path: threshold `S.pi - T.σ` is stronger than the `S.pi` of ordinary
  -- depth robustness
  have hDR : G.DepthRobustAt b G.αpi :=
    LayeredGraph.DepthRobustAtThr.mono G (by linarith [T.σ_pos]) (Nat.cast_nonneg n)
      (hDepth hb)
  let hpath :=
    P.depthRobust_path hDR (P.layerFootprint_subset D b) Finset.Subset.rfl hcard
  let Q := Classical.choose hpath
  have hQspec := Classical.choose_spec hpath
  have hFcard : ((S.pi - T.σ) + T.σ) * n ≤ (((P.layerFootprint D b)).card : ℝ) := by
    calc ((S.pi - T.σ) + T.σ) * n = S.pi * n := by ring
      _ ≤ _ := hcard
  have hZcard : T.σ * n ≤ ((G.fullSources b (P.layerFootprint D b) G.αpi).card : ℝ) :=
    G.card_fullSources (hDepth hb) (P.layerFootprint_subset D b) hFcard
  refine { long := Q, long_mem := hQspec.1, long_length := hQspec.2,
           Z := G.fullSources b (P.layerFootprint D b) G.αpi,
           Z_sub := G.fullSources_subset, Z_weight := ?_, Z_path := ?_ }
  · rw [weight, le_div_iff₀ hnreal]; exact hZcard
  · intro u hu
    obtain ⟨R, hRfirst, hRmem, hRlen⟩ := P.fullSource_path (A := D) Finset.Subset.rfl hu
    exact ⟨R, hRfirst, hRmem, hRlen⟩

set_option linter.unusedDecidableInType false in
theorem sourceRule_full [DecidableEq V] (P : Pebbling G) (T : Tracking S) (hn : 0 < n)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi) :
    SourceRule P T G.αpi :=
  fun _ hb D hfert => ⟨sourceData_full P T hn hDepth hb D hfert⟩

/-! ### Between the two rules

The prefix rule assumes ordinary depth robustness at the fertility threshold `π` and pays
`(α_π - σ) n`; the full rule assumes it at `π - σ` and pays `α_π n`.  Nothing forces a
layer graph to sit at either end.  `sourceData_mixed` reads the *slack* `π - τ` between
the fertility threshold and the threshold the graph is actually robust at, spends it on
`j ≤ (π - τ) n` full-length source nodes, and fills the source up to weight `σ` with a
prefix of a path chosen to avoid them.  The `j` full nodes carry the whole `α_π n`; the
prefix is `j` nodes shorter than it would otherwise be, so its last node carries `j` more.
Either way a link is worth `(α_π - σ) n + j`.

`j = 0` is the prefix rule, `sourceRule_prefix`.  As `j` grows to `σ n` the prefix
vanishes and the second depth-robustness call with it, which is exactly `sourceRule_full`;
that limit is stated separately because dropping the call is what lets it read the
threshold at `π - σ` rather than at `π - ⌈σ n⌉ / n`.
-/

/-- `depthRobust_path` at an explicit robustness threshold. -/
theorem depthRobustThr_path (P : Pebbling G) {A : Finset V} {d : ℕ} {F : Finset V} {τ : ℝ}
    (hrobust : G.DepthRobustAtThr d τ G.αpi) (hF : F ⊆ G.layer d)
    (hfoot : F ⊆ P.layerFootprint A d)
    (hweight : τ * n ≤ (F.card : ℝ)) :
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

/-- The suffix behind the `i`-th node of a prefix that stops `j` nodes early. -/
theorem mixed_suffix_length {σ' απ : ℝ} {j : ℕ} (P : Pebbling G)
    (Q : Path G.edge P.unpebbled) (hQlen : απ * n ≤ (Q.length : ℝ))
    {i : ℕ} (hi : ((i : ℝ) + j) < σ' * n) (hiQ : i ≤ Q.length) :
    (απ - σ') * n + j ≤ ((Q.length - i : ℕ) : ℝ) := by
  have hcast : ((Q.length - i : ℕ) : ℝ) = (Q.length : ℝ) - i := by
    rw [Nat.cast_sub hiQ]
  rw [hcast]
  nlinarith

/-- **The mixed source.**  `j` nodes that begin a whole `α_π n` path, plus the first
`⌈σ n⌉ - j` nodes of a path that avoids them.  The source has weight `σ` and every one of
its nodes begins a path of length `(α_π - σ) n + j` inside the footprint. -/
noncomputable def sourceData_mixed [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hσapi : T.σ ≤ G.αpi) {τ : ℝ} (j : ℕ)
    (hDepth : G.DepthRobustThr τ G.αpi)
    (hj : (j : ℝ) ≤ (S.pi - τ) * n) (hjσ : (j : ℝ) ≤ T.σ * n)
    {b : ℕ} (hb : b < ℓ) (D : Finset V)
    (hfert : S.pi ≤ weight n (P.layerFootprint D b)) :
    SourceData P T (G.αpi - T.σ + (j : ℝ) / n) D b := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint D b).card : ℝ) := by
    unfold weight at hfert
    rwa [le_div_iff₀ hnreal] at hfert
  -- `j` full-length sources, paid for by the robustness slack
  have hFcard : (τ + (S.pi - τ)) * n ≤ (((P.layerFootprint D b)).card : ℝ) := by
    calc (τ + (S.pi - τ)) * n = S.pi * n := by ring
      _ ≤ _ := hcard
  have hXcard : (S.pi - τ) * n
      ≤ ((G.fullSources b (P.layerFootprint D b) G.αpi).card : ℝ) :=
    G.card_fullSources (hDepth hb) (P.layerFootprint_subset D b) hFcard
  have hjX : j ≤ (G.fullSources b (P.layerFootprint D b) G.αpi).card := by
    have h : (j : ℝ) ≤ ((G.fullSources b (P.layerFootprint D b) G.αpi).card : ℝ) :=
      hj.trans hXcard
    exact_mod_cast h
  let hYex := Finset.exists_subset_card_eq hjX
  let Y := Classical.choose hYex
  have hYspec := Classical.choose_spec hYex
  have hYX : Y ⊆ G.fullSources b (P.layerFootprint D b) G.αpi := hYspec.1
  have hYcard : Y.card = j := hYspec.2
  have hYF : Y ⊆ P.layerFootprint D b := hYX.trans G.fullSources_subset
  -- a depth-robust path avoiding them
  have hbig : τ * n ≤ (((P.layerFootprint D b) \ Y).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hYF, Nat.cast_sub (Finset.card_le_card hYF), hYcard]
    linarith
  let hQex := P.depthRobustThr_path (A := D) (hDepth hb)
    (Finset.sdiff_subset.trans (P.layerFootprint_subset D b)) Finset.sdiff_subset hbig
  let Q := Classical.choose hQex
  have hQspec := Classical.choose_spec hQex
  have hQF : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b \ Y := hQspec.1
  have hQlen : G.αpi * n ≤ (Q.length : ℝ) := hQspec.2
  have hQmem : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b :=
    fun v hv => Finset.sdiff_subset (hQF v hv)
  -- the prefix that tops the source up to weight `σ`
  have hceilQ : ⌈T.σ * n⌉₊ ≤ Q.length := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hσapi (Nat.cast_nonneg n)).trans hQlen
  have hk₂ : ⌈T.σ * n⌉₊ - j ≤ Q.length := le_trans (Nat.sub_le _ _) hceilQ
  refine { long := Q, long_mem := hQmem, long_length := hQlen,
           Z := Y ∪ prefixSource Q (⌈T.σ * n⌉₊ - j) hk₂,
           Z_sub := ?_, Z_weight := ?_, Z_path := ?_ }
  · exact Finset.union_subset hYF
      ((prefixSource_subset_of_path Q _ hk₂ hQF).trans Finset.sdiff_subset)
  · have hdisj : Disjoint Y (prefixSource Q (⌈T.σ * n⌉₊ - j) hk₂) := by
      refine Finset.disjoint_left.mpr fun v hvY hvP => ?_
      exact (Finset.mem_sdiff.mp
        (prefixSource_subset_of_path Q _ hk₂ hQF hvP)).2 hvY
    have hcard' : (Y ∪ prefixSource Q (⌈T.σ * n⌉₊ - j) hk₂).card
        = j + (⌈T.σ * n⌉₊ - j) := by
      rw [Finset.card_union_of_disjoint hdisj, hYcard, prefixSource_card Q _ hk₂]
    have hge : ⌈T.σ * n⌉₊ ≤ j + (⌈T.σ * n⌉₊ - j) := by omega
    have hgeR : T.σ * n ≤ ((j + (⌈T.σ * n⌉₊ - j) : ℕ) : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast hge
    rw [weight, hcard', le_div_iff₀ hnreal]
    exact hgeR
  · intro u hu
    have hyn : (G.αpi - T.σ + (j : ℝ) / n) * n = (G.αpi - T.σ) * n + j := by
      field_simp
    rcases Finset.mem_union.mp hu with huY | huP
    · obtain ⟨R, hRfirst, hRmem, hRlen⟩ :=
        P.fullSource_path (A := D) Finset.Subset.rfl (hYX huY)
      refine ⟨R, hRfirst, hRmem, ?_⟩
      rw [hyn]
      nlinarith [hRlen]
    · rcases (mem_prefixSource Q _ hk₂).mp huP with ⟨i, hi⟩
      have hiQ : i.val < Q.length := lt_of_lt_of_le i.isLt hk₂
      have hij : i.val + j < ⌈T.σ * n⌉₊ := by
        have := i.isLt
        omega
      have hijR : ((i.val : ℝ) + j) < T.σ * n := by
        have h := Nat.lt_ceil.mp hij
        push_cast at h
        exact h
      refine ⟨Q.drop i.val hiQ, ?_, ?_, ?_⟩
      · simpa using (Path.drop_first Q i.val hiQ).trans hi
      · intro w hw
        exact hQmem w (List.mem_of_mem_drop hw)
      · rw [hyn]
        have := P.mixed_suffix_length (σ' := T.σ) (απ := G.αpi) (j := j) Q hQlen hijR
          (le_of_lt hiQ)
        simpa using this

set_option linter.unusedDecidableInType false in
/-- **The mixed source rule**: the graph is depth robust at threshold `τ`, and every
node of `(π - τ) n` worth of slack buys one more node of payoff per link. -/
theorem sourceRule_mixed [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hσapi : T.σ ≤ G.αpi) {τ : ℝ} (j : ℕ)
    (hDepth : G.DepthRobustThr τ G.αpi)
    (hj : (j : ℝ) ≤ (S.pi - τ) * n) (hjσ : (j : ℝ) ≤ T.σ * n) :
    SourceRule P T (G.αpi - T.σ + (j : ℝ) / n) :=
  fun _ hb D hfert => ⟨sourceData_mixed P T hn hσapi j hDepth hj hjσ hb D hfert⟩

set_option linter.unusedDecidableInType false in
/-- The prefix rule of `PayChain.lean` is the mixed rule at `j = 0`: no slack is spent, so
the whole source is the `⌈σ n⌉`-prefix and the threshold is the fertility threshold. -/
theorem sourceRule_prefix_eq_mixed_zero [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hσapi : T.σ ≤ G.αpi) (hDepth : G.DepthRobust G.αpi) :
    SourceRule P T (G.αpi - T.σ) := by
  have h := sourceRule_mixed P T hn hσapi (τ := S.pi) 0 hDepth (by simp)
    (by simpa using mul_nonneg T.σ_pos.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  simpa using h

end Pebbling

end Concrete

/-! ### The latency theorems -/

/-- The full payoff realizes `z α_π n`, which is `payLength` at `y = α_π`. -/
theorem payLength_full {V : Type u} {S : Setting} {ℓ n : ℕ}
    (G : Concrete.LayeredGraph V S ℓ n) (z : ℕ) :
    Concrete.Pebbling.payLength G G.αpi z = (z : ℝ) * G.αpi * n := by
  simp only [Concrete.Pebbling.payLength]; ring

/-- **The full-payoff latency bound.**  `latency_pay` at the full-length source rule:
every completed chain link contributes a whole `α_π n`, so `z` links realize `z α_π n`.
The hypotheses are exactly those of `latency_potential`, with one replacement — depth
robustness is required at the threshold `S.pi - T.σ` rather than at `S.pi`. -/
theorem latency_full {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hαpi : 0 ≤ G.αpi)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A ((z : ℝ) * G.αpi * n) := by
  classical
  rw [← payLength_full G z]
  exact latency_pay G P T Cert hn hαpi
    (Concrete.Pebbling.sourceRule_full P T hn hDepth)
    hζmax hentry hnobreak hslack hz1 hz A hA hred hweight

/-- **The asymptotic latency bound.**  Past a fixed head — the initial search plus the
whole black budget, both priced by the ledger — every further layer buys `α_π / potSpan`
of unpebbled path.  This is the statement the certified slope lives in: the coefficient of
`ℓ` is `α_π / potSpan`, and nothing else in it grows with `ℓ`. -/
theorem latency_full_asymptotic {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hαpi : 0 ≤ G.αpi)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    (hspan : 0 < LedgerCert.potSpan C Cert)
    (hlong : LedgerCert.potHead C Cert + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((((ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat)
        / LedgerCert.potSpan C Cert) * G.αpi * n) := by
  classical
  have hmain := latency_pay_asymptotic G P T Cert hn hαpi
    (Concrete.Pebbling.sourceRule_full P T hn hDepth)
    hζmax hentry hnobreak hslack hspan hlong A hA hred hweight
  refine P.hasPath_mono A ?_ hmain
  ring_nf
  nlinarith [hmain]

end ProofOfSpace

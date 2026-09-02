/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Latency

/-!
# Full-payoff links: `α_π n` of new path per chain link

The chain of `Concrete.lean` reaches a footprint of weight `π`, takes *one* depth-robust
path of length `α_π n` inside it, and keeps the first `σ n` nodes of that path as the next
source.  A source node is then the `i`-th node of a prefix, so the certificate it carries
is only the suffix behind it: every link past the first contributes `(α_π - σ) n`, and the
chain of `z` links realizes `α_π n + (z-1)(α_π - σ) n`.

This module replaces the prefix by a set of *full-length path sources*.  If the footprint
has weight `τ + σ` and the layer is depth robust at the lower threshold `τ`, then at least
`σ n` distinct nodes of the footprint each *begin* a path of length `α_π n` inside it
(`card_fullSources`).  Taking those as the source, every source node carries a whole
`α_π n`, so a chain of `z` links realizes `z α_π n`: the payoff per link rises from
`α_π - σ` to `α_π`.

The price is the threshold.  Everything the ledger prices is stated at `S.pi`, so `S.pi`
is here the *superfertile* threshold the footprint must reach, and the graph assumption is
depth robustness at `S.pi - T.σ`.  Nothing else in the accounting changes: `FullLink`
carries the same source data as `Concrete.Link`, so `fullChainSystem` is a `ChainSystem`
for the same `Setting`, `Budget` and `Tracking`, and the ledger of `PotentialLedger.lean`
prices it unchanged.  The trade reads in two directions.  At a fixed certificate, keep
`S.pi` and strengthen the graph assumption from depth robustness at `S.pi` to depth
robustness at `S.pi - T.σ`.  At a fixed graph assumption, keep the depth-robustness
threshold and raise `S.pi` to `threshold + σ`, which re-prices the certificate.

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

/-- The scalar footprint recurrence started at a source set is dominated by the actual
footprint of that set.  This is `Concrete.Pebbling.Link.scalar_le_actual` stated for the
source data alone, so that both link types can use it. -/
theorem sourceBound_le_actual (P : Pebbling G) (hn : 0 < n) {T : Tracking S}
    {b : ℕ} {src : Finset V} (hlayer : src ⊆ G.layer b)
    (havail : ∀ v ∈ src, P.unpebbled v) (hweight : T.σ ≤ weight n src) {d : ℕ}
    (hactive : ∀ e, b ≤ e → e ≤ d →
      P.footprintBound b T.σ e ∈ Set.Icc S.αmin S.αmax)
    (hdepth : b ≤ d) (hd : d < ℓ) :
    P.footprintBound b T.σ d ≤ weight n (P.layerFootprint src d) := by
  have hstart : T.σ ≤ weight n (P.layerFootprint src b) :=
    P.source_le_layerFootprint hlayer havail hweight
  have go : ∀ e, b ≤ e → e ≤ d → e < ℓ →
      P.footprintBound b T.σ e ≤ weight n (P.layerFootprint src e) := by
    intro e hbe hed heℓ
    induction e, hbe using Nat.le_induction with
    | base => simpa using hstart
    | succ e hbe ih =>
        rw [P.footprintBound_isBound b T.σ e hbe]
        exact P.layerFootprint_step hn heℓ (hactive e hbe (by omega))
          (ih (by omega) (by omega))
  exact go d hdepth le_rfl hd


/-- The source set produced by the full-length path-source lemma at a *superfertile*
footprint — one of weight `S.pi`, where the graph is depth robust at the lower threshold
`S.pi - T.σ` — together with everything a link needs of it. -/
theorem fullSource_data (P : Pebbling G) (T : Tracking S) (hn : 0 < n)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi) {A : Finset V} {b : ℕ} (hb : b < ℓ)
    (hfert : S.pi ≤ weight n (P.layerFootprint A b)) :
    G.fullSources b (P.layerFootprint A b) G.αpi ⊆ G.layer b ∧
      (∀ v ∈ G.fullSources b (P.layerFootprint A b) G.αpi, P.unpebbled v) ∧
      T.σ ≤ weight n (G.fullSources b (P.layerFootprint A b) G.αpi) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hFcard : ((S.pi - T.σ) + T.σ) * n ≤ (((P.layerFootprint A b)).card : ℝ) := by
    have h : S.pi * n ≤ (((P.layerFootprint A b)).card : ℝ) := by
      unfold weight at hfert; rwa [le_div_iff₀ hnreal] at hfert
    calc ((S.pi - T.σ) + T.σ) * n = S.pi * n := by ring
      _ ≤ _ := h
  have hcard : T.σ * n ≤ ((G.fullSources b (P.layerFootprint A b) G.αpi).card : ℝ) :=
    G.card_fullSources (hDepth hb) (P.layerFootprint_subset A b) hFcard
  refine ⟨(G.fullSources_subset).trans (P.layerFootprint_subset A b), ?_, ?_⟩
  · intro v hv
    exact P.footprint_available A
      ((P.mem_layerFootprint A).mp (G.fullSources_subset hv)).2
  · rw [weight, le_div_iff₀ hnreal]; exact hcard

/-- **A full-payoff chain link.**  Unlike `Concrete.Pebbling.Link`, whose source is a
`σ n`-prefix of one long path and whose nodes therefore carry only the suffix behind them,
*every* node of a `FullLink` source begins a path of length `count · α_π · n` ending in the
challenge set. -/
structure FullLink [DecidableEq V] (P : Pebbling G) (T : Tracking S) (A : Finset V)
    (cs : ℝ) where
  depth : ℕ
  inside : depth < ℓ
  source : Finset V
  source_layer : source ⊆ G.layer depth
  source_available : ∀ v ∈ source, P.unpebbled v
  source_weight : T.σ ≤ weight n source
  expandable : Expandable P.budget T.ghat depth cs
  count : ℕ
  count_pos : 1 ≤ count
  /-- The full payoff: `α_π n` per link, not `(α_π - σ) n`. -/
  tail : ∀ v ∈ source, P.PathTo A v ((count : ℝ) * G.αpi * n)

namespace FullLink

variable [DecidableEq V] {T : Tracking S} {A : Finset V} {cs : ℝ}

theorem source_nonempty (L : FullLink P T A cs) : L.source.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hcon
  have h0 : L.source.card = 0 := by omega
  have hw := L.source_weight
  rw [weight, h0] at hw
  simp only [Nat.cast_zero, zero_div] at hw
  exact absurd hw (not_le.mpr T.σ_pos)

/-- The realized path of a link: any one source node already carries the whole chain. -/
theorem realized (L : FullLink P T A cs) :
    P.HasUnpebbledPathInFootprint A ((L.count : ℝ) * G.αpi * n) := by
  obtain ⟨v, hv⟩ := L.source_nonempty
  exact ⟨v, L.tail v hv⟩

theorem source_scalar_le (L : FullLink P T A cs) :
    T.σ ≤ weight n (P.layerFootprint L.source L.depth) :=
  P.source_le_layerFootprint L.source_layer L.source_available L.source_weight

/-- **The base link.**  A superfertile challenge footprint already yields `σ n` nodes each
beginning a whole `α_π n` path, and each such path continues to the challenge set through
the footprint. -/
noncomputable def base (P : Pebbling G) (T : Tracking S) (A : Finset V) (hn : 0 < n)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi) {b : ℕ} (hb : b < ℓ)
    (hexp : Expandable P.budget T.ghat b cs)
    (hfert : S.pi ≤ weight n (P.layerFootprint A b)) : FullLink P T A cs := by
  classical
  have hdata := P.fullSource_data T hn hDepth hb hfert
  refine { depth := b, inside := hb,
           source := G.fullSources b (P.layerFootprint A b) G.αpi,
           source_layer := hdata.1, source_available := hdata.2.1,
           source_weight := hdata.2.2,
           expandable := hexp, count := 1, count_pos := le_rfl, tail := ?_ }
  intro v hv
  obtain ⟨Q, hQfirst, hQF, hQlen⟩ := P.fullSource_path (A := A) Finset.Subset.rfl hv
  have hlastF : Q.last ∈ P.layerFootprint A b := hQF Q.last Q.last_mem
  obtain ⟨a, haA, R, hRfirst, hRlast⟩ := ((P.mem_layerFootprint A).mp hlastF).2
  let QR := Q.append R hRfirst.symm
  refine ⟨a, haA, QR, by simpa [QR] using hQfirst, by simpa [QR] using hRlast, ?_⟩
  have hlen : Q.length ≤ QR.length := by
    simp only [QR, Path.append_length]
    have := R.length_pos
    omega
  have hlen' : (Q.length : ℝ) ≤ (QR.length : ℝ) := by exact_mod_cast hlen
  simp only [Nat.cast_one, one_mul]
  exact hQlen.trans hlen'

/-- **The extension.**  At a later superfertile expandable depth every new source node
begins a fresh `α_π n` path, whose end reaches the previous source through the footprint
and there picks up the whole accumulated tail. -/
noncomputable def extend (hn : 0 < n)
    (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi)
    (L : FullLink P T A cs) {b : ℕ} (hdepth : L.depth < b) (hb : b < ℓ)
    (hexp : Expandable P.budget T.ghat b cs)
    (hfert : S.pi ≤ weight n (P.layerFootprint L.source b)) : FullLink P T A cs := by
  classical
  have hdata := P.fullSource_data T hn hDepth hb hfert
  refine { depth := b, inside := hb,
           source := G.fullSources b (P.layerFootprint L.source b) G.αpi,
           source_layer := hdata.1, source_available := hdata.2.1,
           source_weight := hdata.2.2,
           expandable := hexp, count := L.count + 1, count_pos := by omega, tail := ?_ }
  intro v hv
  obtain ⟨Q, hQfirst, hQF, hQlen⟩ :=
    P.fullSource_path (A := L.source) Finset.Subset.rfl hv
  have hlastF : Q.last ∈ P.layerFootprint L.source b := hQF Q.last Q.last_mem
  have hmem := (P.mem_layerFootprint L.source).mp hlastF
  obtain ⟨y, hySource, R, hRfirst, hRlast⟩ := hmem.2
  have hQdepth : G.depth Q.last = b := (G.layer_mem.mp hmem.1).1
  have hyDepth : G.depth y = L.depth := (G.layer_mem.mp (L.source_layer hySource)).1
  have hdepthNe : G.depth Q.last ≠ G.depth y := by rw [hQdepth, hyDepth]; omega
  have hRlen : 2 ≤ R.length := reaches_path_length_two R hRfirst hRlast hdepthNe
  obtain ⟨a, haA, O, hOfirst, hOlast, hOlen⟩ := L.tail y hySource
  let QR := Q.append R hRfirst.symm
  have hROjoin : QR.last = O.first := by simpa [QR] using hRlast.trans hOfirst.symm
  let QRO := QR.append O hROjoin
  refine ⟨a, haA, QRO, by simpa [QRO, QR] using hQfirst, by simpa [QRO] using hOlast, ?_⟩
  have hlen : Q.length + O.length ≤ QRO.length := by
    simp only [QRO, QR, Path.append_length]
    have := Q.length_pos
    have := O.length_pos
    omega
  have hlen' : (Q.length : ℝ) + (O.length : ℝ) ≤ (QRO.length : ℝ) := by exact_mod_cast hlen
  push_cast
  nlinarith [hQlen, hOlen, hlen']

end FullLink

/-- The chain system of full-payoff links.  It is a `ChainSystem` for the *same* `Setting`,
`Budget` and `Tracking` as `Concrete.Pebbling.chainSystem`, so the ledger of
`PotentialLedger.lean` prices it unchanged.  What differs is the realized length —
`z · α_π · n` rather than `α_π n + (z-1)(α_π - σ) n` — and the graph assumption, depth
robustness at `S.pi - T.σ` rather than at `S.pi`. -/
noncomputable def fullChainSystem [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (A : Finset V) (hn : 0 < n) (hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi)
    (cs : ℝ) (hcs : 1 ≤ cs) (hslack : T.lam + (cs - 1) * T.ghat ≤ T.σ) :
    ChainSystem S P.budget T cs ℓ
      (fun z => P.HasUnpebbledPathInFootprint A ((z : ℝ) * G.αpi * n)) where
  one_le_cs := hcs
  cs_slack := hslack
  Link := FullLink P T A cs
  depth := FullLink.depth
  wt := fun L => P.footprintBound L.depth T.σ
  bound := fun L => P.footprintBound_isBound L.depth T.σ
  init := fun L => P.footprintBound_start L.depth T.σ
  expandable := FullLink.expandable
  inside := FullLink.inside
  count := FullLink.count
  count_pos := FullLink.count_pos
  realizes := fun L => L.realized
  extend := by
    intro L b hdepth hb hfert hexp hactive
    have hactual : P.footprintBound L.depth T.σ b ≤
        weight n (P.layerFootprint L.source b) :=
      P.sourceBound_le_actual hn L.source_layer L.source_available L.source_weight
        hactive (le_of_lt hdepth) hb
    exact ⟨FullLink.extend hn hDepth L hdepth hb hexp (hfert.trans hactual), rfl, rfl⟩

end Pebbling

end Concrete

/-! ### The latency theorems -/

/-- **The full-payoff latency bound.**  Every completed chain link contributes a whole
`α_π n`, so `z` links realize `z α_π n`.  The hypotheses are exactly those of
`latency_potential`, with one replacement: depth robustness is required at the threshold
`S.pi - T.σ`, and `S.pi` is correspondingly the weight the footprint must reach for the
search to stop. -/
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
  have hζ : 0 ≤ S.ζδ := by
    have h1 := S.piBar_pos
    have h2 := S.ρ_nonneg
    linarith
  let CS := P.fullChainSystem T A hn hDepth Cert.cs Cert.one_le_cs hslack
  let Ch := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ Ch.f b → Expandable P.budget T.ghat b Cert.cs →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.FullLink.base P T A hn hDepth hb hexp
      (P.challenge_fertile hn hζ hζmax hentry hA hred hweight hb hfertScalar), rfl, rfl⟩
  obtain ⟨L, hL⟩ := LedgerCert.ChainSystem.potential_count Cert CS Ch hζmax hentry
    (fun L => CS.link_floor hnobreak L) (fun L => CS.link_le_αmax L) hrestart hz1 hz
  refine P.hasPath_mono A ?_ (CS.realizes L)
  have hcast : (z : ℝ) ≤ ((CS.count L : ℕ) : ℝ) := by exact_mod_cast hL
  have hnn : (0 : ℝ) ≤ G.αpi * n := mul_nonneg hαpi (Nat.cast_nonneg n)
  nlinarith

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
  set Sp := LedgerCert.potSpan C Cert with hSp
  set r : ℝ := ((ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat) / Sp with hr
  have hnum : 0 < (ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat := by
    linarith
  have hr0 : (0 : ℝ) < r := div_pos hnum hspan
  set z : ℕ := ⌈r⌉₊ with hzdef
  have hz1 : 1 ≤ z := Nat.ceil_pos.mpr hr0
  have hzr : r ≤ (z : ℝ) := Nat.le_ceil r
  have hzlt : (z : ℝ) - 1 < r := by
    have := Nat.ceil_lt_add_one hr0.le
    rw [← hzdef] at this
    linarith
  have hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ) := by
    rw [← hSp]
    have hmul : ((z : ℝ) - 1) * Sp < r * Sp := by
      exact mul_lt_mul_of_pos_right hzlt hspan
    have hrS : r * Sp = (ℓ : ℝ) - LedgerCert.potHead C Cert
        - Cert.lam * S.ρ / T.ghat := by
      rw [hr]; field_simp
    linarith
  have hmain := latency_full G P T Cert hn hαpi hDepth hζmax hentry hnobreak hslack
    hz1 hz A hA hred hweight
  refine P.hasPath_mono A ?_ hmain
  have hnn : (0 : ℝ) ≤ G.αpi * n := mul_nonneg hαpi (Nat.cast_nonneg n)
  nlinarith

end ProofOfSpace

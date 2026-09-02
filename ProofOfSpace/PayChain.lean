/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Concrete
import ProofOfSpace.Ledger
import ProofOfSpace.PotentialLedger

/-!
# One chain, one payoff parameter

The chain of the latency argument is the same object whatever its source rule is: a
sequence of ever-shallower source sets of weight `σ`, each reached from the one above
through the footprint, ending in the challenge set.  Only two numbers about it vary.

* how much *new* path one completed link is worth — call it `y n`;
* what the source rule assumes of the layer graph in order to deliver `y`.

This file carries the chain itself, parameterized by `y` alone.  A `SourceRule` is the
whole of what the graph side has to supply: at a fertile footprint, one intra-layer path
of the depth-robust length `α_π n`, and a source set of weight `σ` every node of which
begins a path of length `y n` inside that footprint.  `PayLink` is the link, and
`payChainSystem` prices it with the ledger of `PotentialLedger.lean`, which never sees
`y`.

The two rules the development uses are the extreme cases.  `sourceRule_prefix`, below,
takes the first `σ n` nodes of one depth-robust path: a source node is the `i`-th node of
a prefix, so it carries only the suffix behind it and `y = α_π - σ`; it assumes no more
than ordinary depth robustness at the fertility threshold.  `sourceRule_full`, in
`FullSources.lean`, takes the nodes that begin a *whole* `α_π n` path inside the
footprint, so `y = α_π`; it assumes depth robustness at the lower threshold `π - σ`.
Everything between the two is `sourceRule_mixed`.
-/

namespace ProofOfSpace

namespace Concrete

namespace Pebbling

universe u

variable {V : Type u} {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n}

/-- The path length realized by a chain of `z` links each worth `y n`, the first worth
the whole depth-robust `α_π n`.  `Latency.lean`'s `latencyLength` is the case
`y = α_π - σ` and the full-payoff length `z α_π n` is the case `y = α_π`. -/
def payLength (G : LayeredGraph V S ℓ n) (y : ℝ) (z : ℕ) : ℝ :=
  G.αpi * n + ((z : ℝ) - 1) * y * n

theorem payLength_mono {y : ℝ} (hy : 0 ≤ y) {z z' : ℕ} (hzz' : z ≤ z') :
    payLength G y z ≤ payLength G y z' := by
  have hcast : (z : ℝ) ≤ (z' : ℝ) := by exact_mod_cast hzz'
  have hyn : (0 : ℝ) ≤ y * n := mul_nonneg hy (Nat.cast_nonneg n)
  simp only [payLength]
  nlinarith

/-! ### Splicing

Both link constructions end the same way: a path that lives inside a footprint is
continued through that footprint into whatever the footprint's target set already
carries.  These two lemmas are that step, once for the challenge set and once for the
source set of the link below.
-/

/-- A path inside the footprint of the challenge set already reaches the challenge set. -/
theorem splice_challenge (P : Pebbling G) {A : Finset V} {b : ℕ}
    {Q : Path G.edge P.unpebbled} (hQ : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint A b) :
    P.PathTo A Q.first (Q.length : ℝ) := by
  classical
  have hlastF : Q.last ∈ P.layerFootprint A b := hQ Q.last Q.last_mem
  obtain ⟨a, haA, R, hRfirst, hRlast⟩ := ((P.mem_layerFootprint A).mp hlastF).2
  let QR := Q.append R hRfirst.symm
  refine ⟨a, haA, QR, by simp [QR], by simpa [QR] using hRlast, ?_⟩
  have hlen : Q.length ≤ QR.length := by
    simp only [QR, Path.append_length]
    have := R.length_pos
    omega
  exact_mod_cast hlen

/-- A path inside the footprint of a source set `D` sitting at a *different* depth
reaches `D`, and there picks up everything `D` already carries. -/
theorem splice_source (P : Pebbling G) {A D : Finset V} {b c : ℕ} (hbc : b ≠ c)
    (hD : D ⊆ G.layer c) {m : ℝ} (hcarry : ∀ w ∈ D, P.PathTo A w m)
    {Q : Path G.edge P.unpebbled} (hQ : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b) :
    P.PathTo A Q.first ((Q.length : ℝ) + m) := by
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

/-! ### The source rule -/

/-- **What a source construction has to deliver** at a fertile footprint: one intra-layer
path of the full depth-robust length `α_π n`, which is what the *first* link of a chain
realizes, and a source set of weight `σ` every node of which begins a path of length
`y n`, which is what every *further* link is worth.  Both live inside the footprint, so
both continue into the target set through it. -/
structure SourceData (P : Pebbling G) (T : Tracking S) (y : ℝ) (D : Finset V) (b : ℕ) where
  /-- One path of the full depth-robust length. -/
  long : Path G.edge P.unpebbled
  long_mem : ∀ v ∈ long.nodes, v ∈ P.layerFootprint D b
  long_length : G.αpi * n ≤ (long.length : ℝ)
  /-- The next source set. -/
  Z : Finset V
  Z_sub : Z ⊆ P.layerFootprint D b
  Z_weight : T.σ ≤ weight n Z
  /-- The payoff: every source node begins a path of length `y n` inside the footprint. -/
  Z_path : ∀ u ∈ Z, ∃ Q : Path G.edge P.unpebbled, Q.first = u ∧
    (∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b) ∧ y * n ≤ (Q.length : ℝ)

/-- A source construction, uniform over depths and over the set whose footprint is
being used. -/
def SourceRule (P : Pebbling G) (T : Tracking S) (y : ℝ) : Prop :=
  ∀ b : ℕ, b < ℓ → ∀ D : Finset V, S.pi ≤ weight n (P.layerFootprint D b) →
    Nonempty (SourceData P T y D b)

/-! ### The link -/

/-- **A chain link paying `y n`.**  Identical to the link of the original argument except
that the per-node payoff is the parameter `y`: every node of the source begins a path of
length `count · y · n` ending in the challenge set, and the chain as a whole realizes
`α_π n + (count - 1) y n`, the first link at the full depth-robust length. -/
structure PayLink [DecidableEq V] (P : Pebbling G) (T : Tracking S) (A : Finset V)
    (cs y : ℝ) where
  depth : ℕ
  inside : depth < ℓ
  source : Finset V
  source_layer : source ⊆ G.layer depth
  source_available : ∀ v ∈ source, P.unpebbled v
  source_weight : T.σ ≤ weight n source
  expandable : Expandable P.budget T.ghat depth cs
  count : ℕ
  count_pos : 1 ≤ count
  tail : ∀ v ∈ source, P.PathTo A v ((count : ℝ) * y * n)
  realized : P.HasUnpebbledPathInFootprint A (payLength G y count)

namespace PayLink

variable [DecidableEq V] {P : Pebbling G} {T : Tracking S} {A : Finset V} {cs y : ℝ}

/-- **The base link.**  A fertile challenge footprint yields the source rule's set and
its long path; both continue into the challenge set through the footprint. -/
noncomputable def base (hrule : SourceRule P T y) {b : ℕ} (hb : b < ℓ)
    (hexp : Expandable P.budget T.ghat b cs)
    (hfert : S.pi ≤ weight n (P.layerFootprint A b)) : PayLink P T A cs y := by
  classical
  let SD := (hrule b hb A hfert).some
  refine { depth := b, inside := hb, source := SD.Z,
           source_layer := SD.Z_sub.trans (P.layerFootprint_subset A b),
           source_available := fun v hv =>
             P.footprint_available A ((P.mem_layerFootprint A).mp (SD.Z_sub hv)).2,
           source_weight := SD.Z_weight,
           expandable := hexp, count := 1, count_pos := le_rfl,
           tail := ?_, realized := ?_ }
  · intro v hv
    obtain ⟨Q, hQfirst, hQF, hQlen⟩ := SD.Z_path v hv
    have h := P.splice_challenge hQF
    rw [hQfirst] at h
    refine P.pathTo_mono A ?_ h
    simpa only [Nat.cast_one, one_mul] using hQlen
  · refine ⟨SD.long.first, ?_⟩
    refine P.pathTo_mono A ?_ (P.splice_challenge SD.long_mem)
    simpa only [payLength, Nat.cast_one, sub_self, zero_mul, add_zero] using SD.long_length

/-- **The extension.**  At a later fertile expandable depth the source rule supplies a
fresh source; each of its nodes reaches the previous source through the footprint and
there picks up the whole accumulated tail. -/
noncomputable def extend (hrule : SourceRule P T y) (L : PayLink P T A cs y) {b : ℕ}
    (hdepth : L.depth < b) (hb : b < ℓ) (hexp : Expandable P.budget T.ghat b cs)
    (hfert : S.pi ≤ weight n (P.layerFootprint L.source b)) : PayLink P T A cs y := by
  classical
  let SD := (hrule b hb L.source hfert).some
  have hbc : b ≠ L.depth := by omega
  refine { depth := b, inside := hb, source := SD.Z,
           source_layer := SD.Z_sub.trans (P.layerFootprint_subset L.source b),
           source_available := fun v hv =>
             P.footprint_available L.source
               ((P.mem_layerFootprint L.source).mp (SD.Z_sub hv)).2,
           source_weight := SD.Z_weight,
           expandable := hexp, count := L.count + 1, count_pos := by omega,
           tail := ?_, realized := ?_ }
  · intro v hv
    obtain ⟨Q, hQfirst, hQF, hQlen⟩ := SD.Z_path v hv
    have h := P.splice_source hbc L.source_layer L.tail hQF
    rw [hQfirst] at h
    refine P.pathTo_mono A ?_ h
    push_cast
    nlinarith [hQlen]
  · refine ⟨SD.long.first, ?_⟩
    refine P.pathTo_mono A ?_ (P.splice_source hbc L.source_layer L.tail SD.long_mem)
    simp only [payLength]
    push_cast
    nlinarith [SD.long_length]

end PayLink

/-- The scalar footprint recurrence started at a source set is dominated by the actual
footprint of that set. -/
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

/-- The chain system of `y`-paying links.  The ledger of `PotentialLedger.lean` prices it
without ever seeing `y`: the payoff enters only through `Realizes`. -/
noncomputable def payChainSystem [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (A : Finset V) (hn : 0 < n) {y : ℝ} (hrule : SourceRule P T y)
    (cs : ℝ) (hcs : 1 ≤ cs) (hslack : T.lam + (cs - 1) * T.ghat ≤ T.σ) :
    ChainSystem S P.budget T cs ℓ
      (fun z => P.HasUnpebbledPathInFootprint A (payLength G y z)) where
  one_le_cs := hcs
  cs_slack := hslack
  Link := PayLink P T A cs y
  depth := PayLink.depth
  wt := fun L => P.footprintBound L.depth T.σ
  bound := fun L => P.footprintBound_isBound L.depth T.σ
  init := fun L => P.footprintBound_start L.depth T.σ
  expandable := PayLink.expandable
  inside := PayLink.inside
  count := PayLink.count
  count_pos := PayLink.count_pos
  realizes := PayLink.realized
  extend := by
    intro L b hdepth hb hfert hexp hactive
    have hactual : P.footprintBound L.depth T.σ b ≤
        weight n (P.layerFootprint L.source b) :=
      P.sourceBound_le_actual hn L.source_layer L.source_available L.source_weight
        hactive (le_of_lt hdepth) hb
    exact ⟨PayLink.extend hrule L hdepth hb hexp (hfert.trans hactual), rfl, rfl⟩

/-! ### The prefix source rule -/

/-- **The prefix source.**  Ordinary depth robustness at the fertility threshold gives one
path of length `α_π n` inside the footprint; its first `⌈σ n⌉` nodes are a source of
weight `σ`, and the `i`-th of them carries only the suffix behind it. -/
noncomputable def sourceData_prefix [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hσapi : T.σ ≤ G.αpi) (hDepth : G.DepthRobust G.αpi)
    {b : ℕ} (hb : b < ℓ) (D : Finset V)
    (hfert : S.pi ≤ weight n (P.layerFootprint D b)) :
    SourceData P T (G.αpi - T.σ) D b := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint D b).card : ℝ) := by
    unfold weight at hfert
    rwa [le_div_iff₀ hnreal] at hfert
  let hpath :=
    P.depthRobust_path (hDepth hb) (P.layerFootprint_subset D b) Finset.Subset.rfl hcard
  let Q := Classical.choose hpath
  have hQspec := Classical.choose_spec hpath
  have hQF : ∀ v ∈ Q.nodes, v ∈ P.layerFootprint D b := hQspec.1
  have hQlen : G.αpi * n ≤ (Q.length : ℝ) := hQspec.2
  let k : ℕ := ⌈T.σ * n⌉₊
  have hk : k ≤ Q.length := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hσapi (Nat.cast_nonneg n)).trans hQlen
  refine { long := Q, long_mem := hQF, long_length := hQlen,
           Z := prefixSource Q k hk,
           Z_sub := prefixSource_subset_of_path Q k hk hQF,
           Z_weight := ?_, Z_path := ?_ }
  · have hceil : T.σ * n ≤ (k : ℝ) := Nat.le_ceil _
    unfold weight
    rw [prefixSource_card Q k hk, le_div_iff₀ hnreal]
    exact hceil
  · intro v hv
    rcases (mem_prefixSource Q k hk).mp hv with ⟨i, hi⟩
    have hiQ : i.val < Q.length := lt_of_lt_of_le i.isLt hk
    refine ⟨Q.drop i.val hiQ, ?_, ?_, ?_⟩
    · simpa using (Path.drop_first Q i.val hiQ).trans hi
    · intro w hw
      exact hQF w (List.mem_of_mem_drop hw)
    · have hsuffix : (G.αpi - T.σ) * n ≤ ((Q.length - i.val : ℕ) : ℝ) :=
        prefix_suffix_length T.σ_pos hσapi hn Q hQlen i.isLt
      simpa using hsuffix

set_option linter.unusedDecidableInType false in
theorem sourceRule_prefix [DecidableEq V] (P : Pebbling G) (T : Tracking S)
    (hn : 0 < n) (hσapi : T.σ ≤ G.αpi) (hDepth : G.DepthRobust G.αpi) :
    SourceRule P T (G.αpi - T.σ) :=
  fun _ hb D hfert => ⟨sourceData_prefix P T hn hσapi hDepth hb D hfert⟩

end Pebbling

end Concrete

end ProofOfSpace

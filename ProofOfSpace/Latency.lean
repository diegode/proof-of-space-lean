import ProofOfSpace.Concrete
import ProofOfSpace.Ledger
import ProofOfSpace.PotentialLedger

/-!
# The concrete latency theorems

This module is the single public home of `latency_general`, stated in
this development.  The chain
construction lives in `Ledger.lean` and its constants in `Chain.lean`; this file adds
the path-length interpretation, the finite hardness estimate, the small-layer
depth-robustness bound, and the certified Filecoin specialization.

`latency_general` assumes `general scalar conditions` and permits chain breaks. Its link
count is the maximum of the certified ledger and constant-charge bounds.
`FilecoinLatencyParameters` records the numerical identities `ĝ = g_π`, `g̃ = g_π`,
`b^max = 0`, and `σ̃ = 3/5` used by the degree-eight specialization.

`latency_potential` uses the reference-trajectory potential from
`PotentialLedger.lean`. Its head, per-link span, and budget charge are `potHead`,
`potSpan`, and `λρ/ĝ`. A `RefChain` is an explicit argument because no reference chain
is valid for every `Setting`. At the Chung-8 Filecoin parameters, the resulting
asymptotic coefficient is greater than `0.02135`.
-/

namespace ProofOfSpace

/-- The path length supplied by a chain with `z` completed links. -/
def latencyLength (απ σ : ℝ) (n z : ℕ) : ℝ :=
  απ * n + ((z : ℝ) - 1) * (απ - σ) * n

/-- Hardness gap obtained by normalizing a latency bound by the initialization work. -/
noncomputable def hardnessGap (ℓ n : ℕ) (latency : ℝ) : ℝ :=
  1 - latency / ((ℓ : ℝ) * n)

theorem latencyLength_mono
    {απ σ : ℝ} {n z z' : ℕ} (hσ : σ ≤ απ) (hzz' : z ≤ z') :
    latencyLength απ σ n z ≤ latencyLength απ σ n z' := by
  have hcast : (z : ℝ) ≤ (z' : ℝ) := by exact_mod_cast hzz'
  have hcoefficient : 0 ≤ (απ - σ) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hσ) (Nat.cast_nonneg n)
  calc
    latencyLength απ σ n z =
        απ * n + ((z : ℝ) - 1) * ((απ - σ) * n) := by
          simp only [latencyLength]
          ring
    _ ≤ απ * n + ((z' : ℝ) - 1) * ((απ - σ) * n) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (sub_le_sub_right hcast 1) hcoefficient) _
    _ = latencyLength απ σ n z' := by
          simp only [latencyLength]
          ring

/-- The ceiling entry in `z_min` gives the finite linear lower bound on its value. -/
theorem ledgerRatio_le_zMinNoBreak {S : Setting} {T : Tracking S} {ℓ s : ℕ} :
    ((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T ≤
      (zMinNoBreak S T ℓ s : ℝ) := by
  let ratio := ((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T
  have hceil : ⌈ratio⌉₊ ≤ zMinNoBreak S T ℓ s := by
    unfold zMinNoBreak
    exact (le_max_left _ _).trans (le_max_right _ _)
  calc
    ((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T = ratio := rfl
    _ ≤ (⌈ratio⌉₊ : ℕ) := Nat.le_ceil ratio
    _ ≤ (zMinNoBreak S T ℓ s : ℕ) := by exact_mod_cast hceil

namespace ChainSystem

universe u

variable {S : Setting} {B : Budget S} {T : Tracking S}
variable {ℓ : ℕ} {Realizes : ℕ → Prop}

/-- Specialization of `Ledger.latency_gen` to any monotone notion of having a path of
length `L`.  This is the shape every concrete corollary below consumes. -/
theorem latency_path
    {Path : ℝ → Prop} {απ σ : ℝ} {n : ℕ}
    (CS : ChainSystem.{u} S B T ℓ (fun z => Path (latencyLength απ σ n z)))
    (GR : GeneralRegime S) (hρ : 0 < S.ρ) (chall : ChallengeBound S B)
    (restart : ∀ b : ℕ, b < ℓ → S.pi ≤ chall.f b → Expandable B T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1)
    (hℓ : s₀ S T < ℓ) (hσ : σ ≤ απ)
    (path_mono : ∀ ⦃L L'⦄, L' ≤ L → Path L → Path L') :
    Path (latencyLength απ σ n (zMin S T ℓ)) := by
  apply CS.latency_gen GR hρ chall restart hℓ
  intro z z' hzz' hpath
  exact path_mono (latencyLength_mono hσ hzz') hpath

end ChainSystem

/-- A fertile footprint level already gives the meaningful small-layer latency bound
`απ n`; no expandable level or chain is needed. -/
theorem latency_without_expandability {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (hn : 0 < n)
    (A : Finset V) (hA : A ⊆ G.layer 0) (d : ℕ) (_hd : d < ℓ)
    (hDepth : G.DepthRobustAt d G.αpi)
    (hfert : S.pi ≤ Concrete.Pebbling.weight n (P.layerFootprint A d)) :
    P.HasUnpebbledPathInFootprint A (G.αpi * n) := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : S.pi * n ≤ ((P.layerFootprint A d).card : ℝ) := by
    unfold Concrete.Pebbling.weight at hfert
    rwa [le_div_iff₀ hnreal] at hfert
  obtain ⟨Q, hQfoot, hQlen⟩ :=
    P.depthRobust_path hDepth (P.layerFootprint_subset A d) Finset.Subset.rfl hcard
  have hQlast := hQfoot Q.last Q.last_mem
  have hQdepth : G.depth Q.last = d :=
    (G.layer_mem.mp ((P.mem_layerFootprint A).mp hQlast |>.1)).1
  obtain ⟨a, ha, O, hOfirst, hOlast⟩ :=
    (P.mem_layerFootprint A).mp hQlast |>.2
  have haDepth : G.depth a = 0 := (G.layer_mem.mp (hA ha)).1
  have hOlastDepth : G.depth O.last = 0 := by rw [hOlast, haDepth]
  have hOfirstDepth : G.depth O.first = d := by rw [hOfirst, hQdepth]
  have hOlen : d + 1 ≤ O.length := by
    have := G.depth_add_one_le_path_length O hOlastDepth
    rwa [hOfirstDepth] at this
  let QO := Q.append O hOfirst.symm
  have hQOlenNat : Q.length + d ≤ QO.length := by
    simp only [QO, Concrete.Path.append_length]
    omega
  have hQOlen : (Q.length : ℝ) + d ≤ (QO.length : ℝ) := by
    exact_mod_cast hQOlenNat
  refine ⟨QO.first, a, ha, QO, rfl, ?_, ?_⟩
  · simpa [QO] using hOlast
  · have hQreal : G.αpi * n ≤ (Q.length : ℝ) := hQlen
    have hdreal : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith

namespace Concrete

namespace Pebbling

variable {V : Type u} {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n}

/-- **The pebbling half of `first-source lemma`.**  Wherever the scalar
challenge footprint bound is fertile, so is the *actual* reachability footprint of a red-free
challenge set of weight `ζ_δ`.  This is the only thing a chain restart needs from the
graph beyond what an ordinary extension needs. -/
theorem challenge_fertile (P : Pebbling G) (hn : 0 < n) (hζ : 0 ≤ S.ζδ)
    {A : Finset V} (hA : A ⊆ G.layer 0) (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ weight n A) {b : ℕ} (hb : b < ℓ)
    (hfertScalar : S.pi ≤ (P.challengeBound_struct hζ).f b) :
    S.pi ≤ weight n (P.layerFootprint A b) := by
  have hstart : max 0 (S.ζδ - P.budget.spend 0) ≤ weight n (P.layerFootprint A 0) :=
    P.challenge_start_le hn hA hred hweight
  have hactual : P.challengeBound b ≤ weight n (P.layerFootprint A b) :=
    P.footprintBound_le hn (le_max_left _ _) hstart (Nat.zero_le b) hb
  exact hfertScalar.trans (by simpa [challengeBound_struct] using hactual)

end Pebbling

end Concrete

/-- The adjusted challenge weight is nonnegative in the general regime. -/
theorem zetaDelta_nonneg {S : Setting} (GR : GeneralRegime S) : 0 ≤ S.ζδ := by
  have h := GR.entry
  simp only [Setting.zetaFloor] at h
  linarith [S.αmin_nonneg, S.ρ_nonneg]

/-! ### The general parameter regime -/

/-- `(b^max + 1) h_1`, the per-link level span certified when breaks are possible: the
`h_1` of `optimized span bound`, shared between the at most `b^max + 1` chain segments. -/
noncomputable def genLinkSpan (S : Setting) (T : Tracking S) : ℝ :=
  ((bMax S T : ℝ) + 1) * h₁ S T

theorem genLinkSpan_pos {S : Setting} {T : Tracking S} : 0 < genLinkSpan S T := by
  have := h₁_pos (S := S) (T := T)
  simp only [genLinkSpan]
  positivity

/-- The one-time overhead subtracted by the ledger entry of `zMin`. -/
noncomputable def s₁ (S : Setting) (T : Tracking S) : ℝ :=
  (sCap S T : ℝ) + ledgerSlack S T + (bMax S T : ℝ) * h₁ S T

/-- The one-time overhead subtracted by the **joint** ledger entry of `zMin`:
`searchHead + 2ρ/min{ĝ,g̃}`, the offset that charges the black budget once rather than
once for the infertile levels, once for the blocked windows and twice for the attempts.
At the Filecoin parameters it is below `14.82`. -/
noncomputable def s₂ (S : Setting) (T : Tracking S) : ℝ :=
  searchHead S + jointSlack S T

/-- The joint entry of `zMin` gives its finite linear lower bound, whenever no break can
be paid for.  The slope is `1/h_1`, as for `genLedgerRatio_le_zMin`; what improves is the
offset. -/
theorem jointRatio_le_zMin {S : Setting} {T : Tracking S} (h : bMax S T = 0) {ℓ : ℕ} :
    ((ℓ : ℝ) - s₂ S T) / h₁ S T ≤ (zMin S T ℓ : ℝ) := by
  set r := ((ℓ : ℝ) - s₂ S T) / h₁ S T with hr
  have hentry : ⌈r⌉₊ ≤ zMin S T ℓ := by
    have hj : jointEntry S T ℓ = ⌈r⌉₊ := by
      simp only [jointEntry, h, if_pos, hr, s₂]
      ring_nf
    rw [← hj]
    unfold zMin
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  calc
    r ≤ (⌈r⌉₊ : ℕ) := Nat.le_ceil r
    _ ≤ (zMin S T ℓ : ℕ) := by exact_mod_cast hentry

/-- The ceiling entry in `zMin` gives its finite linear lower bound.  This is
`ledgerRatio_le_zMinNoBreak` with the break allowance; with `b^max = 0` it *is* that lemma. -/
theorem genLedgerRatio_le_zMin {S : Setting} {T : Tracking S} {ℓ : ℕ} :
    ((ℓ : ℝ) - s₁ S T) / genLinkSpan S T ≤ (zMin S T ℓ : ℝ) := by
  have hnum : (ℓ : ℝ) - s₁ S T
      = (ℓ : ℝ) - sCap S T - ledgerSlack S T - bMax S T * h₁ S T := by
    simp only [s₁]; ring
  rw [hnum]
  set r := ((ℓ : ℝ) - sCap S T - ledgerSlack S T - bMax S T * h₁ S T) /
    genLinkSpan S T with hr
  have hceil : ⌈r⌉₊ ≤ zMin S T ℓ := by
    unfold zMin
    exact (le_max_left _ _).trans (le_max_right _ _)
  calc
    r ≤ (⌈r⌉₊ : ℕ) := Nat.le_ceil r
    _ ≤ (zMin S T ℓ : ℕ) := by exact_mod_cast hceil

/--
**Concrete latency lower bound, general parameters** (`latency_general`).

For an actual layered graph and pebble placement, and under the nontriviality
assumptions `general scalar conditions` alone, every red-free adjusted challenge set of
normalized weight at least `ζ_δ` has an unpebbled directed path of length
`α_π n + (z_min - 1)(α_π - σ) n` in its genuine reachability footprint, with
`z_min = zMin`.

`LayeredGraph.DepthRobust` is the construction assumption.  The footprint recurrence,
the general infertile-gain floor `g̃`, the base link, chain extension with breaks, the
restart search, path splicing and the level accounting are all proved.
-/
theorem latency_general {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S) (GR : GeneralRegime S)
    (hn : 0 < n) (hρ : 0 < S.ρ) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hinside : s₀ S T < ℓ)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      (latencyLength G.αpi T.σ n (zMin S T ℓ)) := by
  classical
  have hζ : 0 ≤ S.ζδ := zetaDelta_nonneg GR
  let CS := P.chainSystem T A hn hσapi.le hDepth
  let C := P.challengeBound_struct hζ
  -- the restart: `first-source lemma` supplies the level, `Link.base` the link
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ C.f b → Expandable P.budget T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.Link.base hn hσapi.le hDepth hb hexp
      (P.challenge_fertile hn hζ hA hred hweight hb hfertScalar), rfl, rfl⟩
  have hchain := CS.latency_gen GR hρ C hrestart hinside (by
    intro z z' hzz' hz'
    apply P.hasPath_mono A _ hz'
    simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using
      latencyLength_mono hσapi.le hzz')
  simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using hchain

/-- The explicit path witness form of the general-regime latency theorem. -/
theorem latency_general_witness {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S) (GR : GeneralRegime S)
    (hn : 0 < n) (hρ : 0 < S.ρ) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hinside : s₀ S T < ℓ)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    ∃ Q : Concrete.Path G.edge P.unpebbled,
      latencyLength G.αpi T.σ n (zMin S T ℓ) ≤ (Q.length : ℝ) ∧
        ∀ v ∈ Q.nodes, v ∈ P.footprint A := by
  apply P.hasPath_witness A
  exact latency_general G P T GR hn hρ hσapi hDepth hinside A hA hred hweight

/-! ### The potential-ledger latency bound -/

/--
**Concrete latency lower bound from the potential ledger.**

`latency_general` counts chain links with `zMin`, whose joint entry prices every unit of
the black budget at the flat rate `1/ĝ` and does so twice — once for the infertile skips
and once for the levels inside blocked ranges.  `potential_count` counts them against a
reference trajectory instead, charging the budget once at the certificate's rate `λ/ĝ`.
This theorem is `latency_general` with that count substituted: the chain system, the
restart, and the monotonicity of the path length are literally the same, and only the
accounting differs.

A reference chain is deliberately **not** a hypothesis of `latency_general`.  Unlike
`Tracking.mid`, which always admits the trivial value `σ`, no chain is admissible for
every `Setting` — the width condition `x (k+1) - x k ≥ ĝ` fails as soon as the gains do —
so making one a field or a hypothesis there would be a new assumption.  It enters here as
an explicit argument, and is exhibited only where its conditions are theorems about the
curve at hand.
-/
theorem latency_potential {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A (latencyLength G.αpi T.σ n z) := by
  classical
  have hζ : 0 ≤ S.ζδ := by
    have h1 := S.piBar_pos
    have h2 := S.ρ_nonneg
    linarith
  let CS := P.chainSystem T A hn hσapi.le hDepth
  let Ch := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ Ch.f b → Expandable P.budget T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.Link.base hn hσapi.le hDepth hb hexp
      (P.challenge_fertile hn hζ hA hred hweight hb hfertScalar), rfl, rfl⟩
  obtain ⟨L, hL⟩ := LedgerCert.ChainSystem.potential_count Cert CS Ch hζmax hentry
    (fun L => CS.link_floor hnobreak L) (fun L => CS.link_le_αmax L) hrestart hz1 hz
  refine P.hasPath_mono A ?_ (CS.realizes L)
  simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using
    latencyLength_mono (απ := G.αpi) (σ := T.σ) (n := n) hσapi.le hL

/-- The explicit path witness form of the potential-ledger latency theorem. -/
theorem latency_potential_witness {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    ∃ Q : Concrete.Path G.edge P.unpebbled,
      latencyLength G.αpi T.σ n z ≤ (Q.length : ℝ) ∧
        ∀ v ∈ Q.nodes, v ∈ P.footprint A := by
  apply P.hasPath_witness A
  exact latency_potential G P T Cert hn hσapi hDepth hζmax hentry hnobreak hz1 hz
    A hA hred hweight

/-- The finite linear form: the certified path length grows linearly in `ℓ` with leading
slope `(α_π - σ)/((b^max + 1) h_1)`.  All constants are independent of `ℓ`, which is the
`L = Ω(ℓ n)` of `latency_general`; with `b^max = 0` it is the slope of the no-break
corollary. -/
theorem latencyLength_general_lower_bound
    {S : Setting} {T : Tracking S} {ℓ n : ℕ} {απ σ : ℝ} (hσ : σ ≤ απ) :
    απ * n +
        ((((ℓ : ℝ) - s₁ S T) / genLinkSpan S T - 1) * (απ - σ) * n) ≤
      latencyLength απ σ n (zMin S T ℓ) := by
  have hcount := genLedgerRatio_le_zMin (S := S) (T := T) (ℓ := ℓ)
  have hcoefficient : 0 ≤ (απ - σ) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hσ) (Nat.cast_nonneg n)
  calc
    απ * n +
        ((((ℓ : ℝ) - s₁ S T) / genLinkSpan S T - 1) * (απ - σ) * n) =
      απ * n +
        ((((ℓ : ℝ) - s₁ S T) / genLinkSpan S T - 1) * ((απ - σ) * n)) := by
          ring
    _ ≤ απ * n + (((zMin S T ℓ : ℝ) - 1) * ((απ - σ) * n)) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right (sub_le_sub_right hcount 1) hcoefficient) _
    _ = latencyLength απ σ n (zMin S T ℓ) := by
          simp only [latencyLength]
          ring

/-- The general-regime hardness gap: `ε_hardness ≤ 1 - Ω(1)`, with constant
`(α_π - σ)/((b^max + 1) h_1)` and an explicit `O(1/ℓ)` correction. -/
theorem hardnessGap_general_upper_bound
    {S : Setting} {T : Tracking S} {ℓ n : ℕ} {απ σ : ℝ}
    (hℓ : 0 < ℓ) (hn : 0 < n) (hσ : σ ≤ απ) :
    hardnessGap ℓ n (latencyLength απ σ n (zMin S T ℓ)) ≤
      1 - (απ - σ) / genLinkSpan S T +
        ((απ - σ) * (s₁ S T / genLinkSpan S T + 1) - απ) / ℓ := by
  have hlower := latencyLength_general_lower_bound
    (S := S) (T := T) (ℓ := ℓ) (n := n) hσ
  have hden : 0 < (ℓ : ℝ) * n := by positivity
  have hspan : (0 : ℝ) < genLinkSpan S T := genLinkSpan_pos
  have hdiv := div_le_div_of_nonneg_right hlower hden.le
  unfold hardnessGap
  calc
    1 - latencyLength απ σ n (zMin S T ℓ) / ((ℓ : ℝ) * n) ≤
      1 - (απ * n +
        ((((ℓ : ℝ) - s₁ S T) / genLinkSpan S T - 1) *
          (απ - σ) * n)) / ((ℓ : ℝ) * n) := sub_le_sub_left hdiv 1
    _ = 1 - (απ - σ) / genLinkSpan S T +
        ((απ - σ) * (s₁ S T / genLinkSpan S T + 1) - απ) / ℓ := by
          field_simp [ne_of_gt hspan, ne_of_gt hℓ, ne_of_gt hn]
          ring

/-- The concrete path also satisfies the ledger's explicit linear lower bound.  This
is the finite, constant-explicit form of the development's `Ω(ℓ n)` conclusion. -/
theorem latency_concrete_ledger_witness {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S) (GR : GeneralRegime S)
    (hn : 0 < n) (hρ : 0 < S.ρ) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hinside : s₀ S T < ℓ)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    ∃ Q : Concrete.Path G.edge P.unpebbled,
      G.αpi * n +
          ((((ℓ : ℝ) - s₁ S T) / genLinkSpan S T - 1) * (G.αpi - T.σ) * n) ≤
            (Q.length : ℝ) ∧
        ∀ v ∈ Q.nodes, v ∈ P.footprint A := by
  apply P.hasPath_witness A
  apply P.hasPath_mono A
    (latencyLength_general_lower_bound
      (S := S) (T := T) (ℓ := ℓ) (n := n) hσapi.le)
  exact latency_general G P T GR hn hρ hσapi hDepth hinside A hA hred hweight

/-- A finite linear lower bound whose leading slope is `(απ - σ) / h₁`. -/
theorem latencyLength_ledger_lower_bound
    {S : Setting} {T : Tracking S} {ℓ s n : ℕ} {απ σ : ℝ}
    (hσ : σ ≤ απ) :
    απ * n +
        ((((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T - 1) *
          (απ - σ) * n) ≤
      latencyLength απ σ n (zMinNoBreak S T ℓ s) := by
  have hcount := ledgerRatio_le_zMinNoBreak (S := S) (T := T) (ℓ := ℓ) (s := s)
  have hcoefficient : 0 ≤ (απ - σ) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hσ) (Nat.cast_nonneg n)
  calc
    απ * n +
        ((((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T - 1) *
          (απ - σ) * n) =
      απ * n +
        ((((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T - 1) *
          ((απ - σ) * n)) := by ring
    _ ≤ απ * n +
        (((zMinNoBreak S T ℓ s : ℝ) - 1) * ((απ - σ) * n)) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (sub_le_sub_right hcount 1) hcoefficient) _
    _ = latencyLength απ σ n (zMinNoBreak S T ℓ s) := by
          simp only [latencyLength]
          ring
/--
Finite form of the theorem's hardness-gap estimate.  The last summand is a constant
multiple of `1 / ℓ` when all graph parameters other than the number of layers are fixed.
-/
theorem hardnessGap_upper_bound
    {S : Setting} {T : Tracking S} {ℓ s n : ℕ} {απ σ : ℝ}
    (hℓ : 0 < ℓ) (hn : 0 < n) (hσ : σ ≤ απ) :
    hardnessGap ℓ n (latencyLength απ σ n (zMinNoBreak S T ℓ s)) ≤
      1 - (απ - σ) / h₁ S T +
        ((απ - σ) *
          (((s : ℝ) + ledgerSlack S T) / h₁ S T + 1) - απ) / ℓ := by
  have hlower := latencyLength_ledger_lower_bound
    (S := S) (T := T) (ℓ := ℓ) (s := s) (n := n) hσ
  have hden : 0 < (ℓ : ℝ) * n := by positivity
  have hdiv := div_le_div_of_nonneg_right hlower hden.le
  unfold hardnessGap
  calc
    1 - latencyLength απ σ n (zMinNoBreak S T ℓ s) / ((ℓ : ℝ) * n) ≤
      1 - (απ * n +
        ((((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T - 1) *
          (απ - σ) * n)) / ((ℓ : ℝ) * n) := sub_le_sub_left hdiv 1
    _ = 1 - (απ - σ) / h₁ S T +
        ((απ - σ) *
          (((s : ℝ) + ledgerSlack S T) / h₁ S T + 1) - απ) / ℓ := by
          field_simp [ne_of_gt h₁_pos, ne_of_gt hℓ, ne_of_gt hn]
          ring

/-! ### Filecoin Chung-8 specialization -/

/-- The numerical certificates used in `cor:filecoin`.  The Chung threshold is
recorded by the certified interval printed in the development, rather than identified with a
rounded decimal. -/
structure FilecoinLatencyParameters (S : Setting) (T : Tracking S) : Prop where
  pi_eq : S.pi = (4 : ℝ) / 5
  rho_eq : S.ρ = (4 : ℝ) / 5
  zetaDelta_eq : S.ζδ = (4311 : ℝ) / 5000
  sigma_eq : T.σ = (74 : ℝ) / 625
  gpi_lower : (1113 : ℝ) / 10000 < S.gpi
  gpi_upper : S.gpi < (557 : ℝ) / 5000
  /-- `ĝ = g_π`: the tracked gain is the one the constants are computed with.  At the
  deployed parameters this is `gain_δ(σ) ≥ 2 g_π` (`Tracking.ghat_eq_gpi`). -/
  ghat_eq : T.ghat = S.gpi
  /-- `g̃ = g_π`: the infertile-level gain floor is the same one (`gtilde_eq_gpi`). -/
  gtilde_eq : S.gtilde = S.gpi
  /-- No chain break can be paid for (`bMax_eq_zero`), so `s_0 = s` and the general
  chain length collapses onto `zMinNoBreak`. -/
  bMax_eq : bMax S T = 0
  /-- The doubled-gain mid-point is `σ̃ = 3/5`, certified by `2 g_π ≤ gain_δ(3/5)` on the
  Chung-8 curve.  This is what turns the growth constant from `a > 6.118` into
  `Φ_{3/5}(π) + 1 < 4.961`. -/
  mid_eq : T.mid = (3 : ℝ) / 5

namespace FilecoinLatencyParameters

variable {S : Setting} {T : Tracking S}

theorem infertileCap_eq (F : FilecoinLatencyParameters S T) : infertileCap S S.gpi = 7 := by
  unfold infertileCap
  apply (Nat.ceil_eq_iff (by norm_num : (7 : ℕ) ≠ 0)).2
  rw [F.rho_eq, F.zetaDelta_eq, F.pi_eq]
  constructor
  · rw [lt_div_iff₀ S.gpi_pos']
    nlinarith [F.gpi_upper]
  · rw [div_le_iff₀ S.gpi_pos']
    nlinarith [F.gpi_lower]

theorem blockedCap_eq (F : FilecoinLatencyParameters S T) : blockedCap S S.gpi = 7 := by
  unfold blockedCap
  have hceil : ⌈S.ρ / S.gpi⌉₊ = 8 := by
    apply (Nat.ceil_eq_iff (by norm_num : (8 : ℕ) ≠ 0)).2
    rw [F.rho_eq]
    constructor
    · rw [lt_div_iff₀ S.gpi_pos']
      nlinarith [F.gpi_upper]
    · rw [div_le_iff₀ S.gpi_pos']
      nlinarith [F.gpi_lower]
  rw [hceil]

theorem sCapOf_eq (F : FilecoinLatencyParameters S T) :
    sCapOf S S.gpi S.gpi = 14 := by
  simp only [sCapOf, F.infertileCap_eq, F.blockedCap_eq]

theorem spendCap_eq (F : FilecoinLatencyParameters S T) :
    spendCap S T = 8 := by
  unfold spendCap
  rw [F.ghat_eq, F.rho_eq]
  apply (Nat.ceil_eq_iff (by norm_num : (8 : ℕ) ≠ 0)).2
  constructor
  · rw [lt_div_iff₀ S.gpi_pos']
    nlinarith [F.gpi_upper]
  · rw [div_le_iff₀ S.gpi_pos']
    nlinarith [F.gpi_lower]

theorem growthCap_eq (F : FilecoinLatencyParameters S T) :
    growthCap S T = 13 := by
  unfold growthCap growthSpan
  rw [F.ghat_eq]
  have hnum : 0 ≤ S.pi - T.σ + S.ρ := by
    rw [F.pi_eq, F.sigma_eq, F.rho_eq]
    norm_num
  have hfloor : ⌊(S.pi - T.σ + S.ρ) / S.gpi⌋₊ = 13 := by
    apply (Nat.floor_eq_iff (div_nonneg hnum S.gpi_pos'.le)).2
    constructor
    · rw [le_div_iff₀ S.gpi_pos']
      rw [F.pi_eq, F.sigma_eq, F.rho_eq]
      nlinarith [F.gpi_upper]
    · rw [div_lt_iff₀ S.gpi_pos']
      rw [F.pi_eq, F.sigma_eq, F.rho_eq]
      nlinarith [F.gpi_lower]
  rw [hfloor]
  norm_num

theorem h₀_eq (F : FilecoinLatencyParameters S T) :
    h₀ S T = 29 := by
  simp only [h₀, F.growthCap_eq, F.spendCap_eq]

/-- **The growth constant is the two-piece one.**  `Φ_{3/5}(π) + 1 < a`, so the `min`
defining `growthConst` picks the potential entry.  The criterion is
`growthPot_pi_succ_lt_asymptoticGrowth`: the doubled-gain segment `[σ, 3/5]` has length
`0.4816`, well above `2 ĝ < 0.2228`. -/
theorem growthConst_eq (F : FilecoinLatencyParameters S T) :
    growthConst S T = growthPot S T ((3 : ℝ) / 5) S.pi + 1 := by
  have hcπ : (3 : ℝ) / 5 ≤ S.pi := by rw [F.pi_eq]; norm_num
  have hgap : 2 * T.ghat < (3 : ℝ) / 5 - T.σ := by
    rw [F.ghat_eq, F.sigma_eq]
    linarith [F.gpi_upper]
  have h := growthPot_pi_succ_lt_asymptoticGrowth (S := S) (T := T) hcπ hgap
  simp only [growthConst, F.mid_eq]
  exact min_eq_right h.le

theorem h₁_eq (F : FilecoinLatencyParameters S T) :
    h₁ S T = (551 : ℝ) / 1250 / S.gpi + 2 := by
  have hcπ : (3 : ℝ) / 5 ≤ S.pi := by rw [F.pi_eq]; norm_num
  have hpos := S.gpi_pos'
  have hgp : growthPot S T ((3 : ℝ) / 5) S.pi
      = ((3 : ℝ) / 5 - T.σ) / (2 * T.ghat) + (S.pi - (3 : ℝ) / 5) / T.ghat :=
    growthPot_pi hcπ
  rw [h₁, F.growthConst_eq, hgp, F.ghat_eq, F.pi_eq, F.sigma_eq]
  field_simp
  ring

theorem ledgerSlack_eq (F : FilecoinLatencyParameters S T) :
    ledgerSlack S T = 2 * ((4 : ℝ) / 5) / S.gpi := by
  simp only [ledgerSlack, F.ghat_eq, F.rho_eq]

/-- `min{ĝ, g̃} = g_π`: both certified gain rates collapse onto `g_π` here. -/
theorem gmin_eq (F : FilecoinLatencyParameters S T) : gmin S T = S.gpi := by
  simp only [gmin, F.ghat_eq, F.gtilde_eq, min_self]

theorem jointSlack_eq (F : FilecoinLatencyParameters S T) :
    jointSlack S T = 2 * ((4 : ℝ) / 5) / S.gpi := by
  simp only [jointSlack, F.gmin_eq, F.rho_eq]

/-- The joint head is `1 - 0.0622/g_π ≈ 0.4414`: the ceiling slack of
`infertile-capacity lemma` less the head start the challenge weight `ζ_δ > π` already
gives.  The `max 0` is inactive because `g_π > 0.0622`. -/
theorem searchHead_eq (F : FilecoinLatencyParameters S T) :
    searchHead S = 1 + ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / S.gpi := by
  have h : (0 : ℝ) ≤ 1 + ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / S.gpi := by
    have hge : -1 ≤ ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / S.gpi := by
      rw [le_div_iff₀ S.gpi_pos']
      nlinarith [F.gpi_lower]
    linarith
  simp only [searchHead, F.gtilde_eq, F.pi_eq, F.zetaDelta_eq]
  exact max_eq_right h

theorem h₁_bounds (F : FilecoinLatencyParameters S T) :
    (1489 : ℝ) / 250 < h₁ S T ∧ h₁ S T < (5961 : ℝ) / 1000 := by
  rw [F.h₁_eq]
  constructor
  · have h : (1489 : ℝ) / 250 - 2 < (551 : ℝ) / 1250 / S.gpi := by
      rw [lt_div_iff₀ S.gpi_pos']
      nlinarith [F.gpi_upper]
    linarith
  · have h : (551 : ℝ) / 1250 / S.gpi < (5961 : ℝ) / 1000 - 2 := by
      rw [div_lt_iff₀ S.gpi_pos']
      nlinarith [F.gpi_lower]
    linarith

theorem ledgerSlack_bounds (F : FilecoinLatencyParameters S T) :
    (359 : ℝ) / 25 < ledgerSlack S T ∧
      ledgerSlack S T < (719 : ℝ) / 50 := by
  rw [F.ledgerSlack_eq]
  constructor
  · rw [lt_div_iff₀ S.gpi_pos']
    nlinarith [F.gpi_upper]
  · rw [div_lt_iff₀ S.gpi_pos']
    nlinarith [F.gpi_lower]

/-- **The joint offset, evaluated:** `14.804 < s₂ < 14.817`. -/
theorem s₂_bounds (F : FilecoinLatencyParameters S T) :
    (3701 : ℝ) / 250 < s₂ S T ∧ s₂ S T < (14817 : ℝ) / 1000 := by
  rw [s₂, F.searchHead_eq, F.jointSlack_eq]
  constructor
  · have h : (3701 : ℝ) / 250 - 1
        < ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / S.gpi + 2 * ((4 : ℝ) / 5) / S.gpi := by
      rw [← add_div, lt_div_iff₀ S.gpi_pos']
      nlinarith [F.gpi_upper]
    linarith
  · have h : ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / S.gpi + 2 * ((4 : ℝ) / 5) / S.gpi
        < (14817 : ℝ) / 1000 - 1 := by
      rw [← add_div, div_lt_iff₀ S.gpi_pos']
      nlinarith [F.gpi_lower]
    linarith


/-- The ledger slope `(α_π - σ)/h_1`, with a certified rounding interval. -/
theorem ledgerSlope_bounds (F : FilecoinLatencyParameters S T) :
    (1368 : ℝ) / 100000 <
        ((1 : ℝ) / 5 - (74 : ℝ) / 625) / h₁ S T ∧
      ((1 : ℝ) / 5 - (74 : ℝ) / 625) / h₁ S T <
        (1371 : ℝ) / 100000 := by
  have hbounds := F.h₁_bounds
  constructor
  · rw [lt_div_iff₀ h₁_pos]
    nlinarith [hbounds.2]
  · rw [div_lt_iff₀ h₁_pos]
    nlinarith [hbounds.1]

/-- The explicit Filecoin link count: the base link, per-link ledger entry, joint-ledger
entry, and constant-charge entry. -/
noncomputable def filecoinZMin (gpi : ℝ) (ℓ : ℕ) : ℕ :=
  max 1 (max
    ⌈((ℓ : ℝ) - 14 - 2 * ((4 : ℝ) / 5) / gpi) / ((551 : ℝ) / 1250 / gpi + 2)⌉₊
    (max
      ⌈((ℓ : ℝ) - (1 + ((4 : ℝ) / 5 - (4311 : ℝ) / 5000) / gpi)
          - 2 * ((4 : ℝ) / 5) / gpi) / ((551 : ℝ) / 1250 / gpi + 2)⌉₊
      ((ℓ - 14) / 29 + 1)))

/-- The explicit Filecoin link count is monotone in the layer count. -/
theorem filecoinZMin_mono {gpi : ℝ} (hgpi : 0 < gpi) :
    Monotone (filecoinZMin gpi) := by
  intro ℓ₁ ℓ₂ hℓ
  have hden : 0 ≤ ((551 : ℝ) / 1250 / gpi + 2) := by positivity
  have hcast : (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) := by exact_mod_cast hℓ
  unfold filecoinZMin
  refine max_le_max (le_refl 1) (max_le_max ?_ (max_le_max ?_ ?_))
  · exact Nat.ceil_le_ceil (div_le_div_of_nonneg_right (by linarith) hden)
  · exact Nat.ceil_le_ceil (div_le_div_of_nonneg_right (by linarith) hden)
  · exact Nat.add_le_add_right
      (Nat.div_le_div_right (Nat.sub_le_sub_right hℓ 14)) 1

theorem zMinNoBreak_eq (F : FilecoinLatencyParameters S T) (ℓ : ℕ) :
    zMinNoBreak S T ℓ (sCapOf S S.gpi S.gpi) = filecoinZMin S.gpi ℓ := by
  rw [F.sCapOf_eq, zMinNoBreak, filecoinZMin, F.ledgerSlack_eq, F.h₁_eq, F.h₀_eq,
    F.searchHead_eq, F.jointSlack_eq]
  norm_num

/-- The general search overhead is the closed form `s(g_π, g_π)` here. -/
theorem sCap_eq_sCapOf (F : FilecoinLatencyParameters S T) :
    sCap S T = sCapOf S S.gpi S.gpi := by
  simp only [sCap, F.ghat_eq, F.gtilde_eq]

theorem sCap_eq (F : FilecoinLatencyParameters S T) : sCap S T = 14 :=
  F.sCap_eq_sCapOf.trans F.sCapOf_eq

/-- With no break to pay for, the whole non-chain overhead of `global constants` is
the search overhead. -/
theorem s₀_eq (F : FilecoinLatencyParameters S T) : s₀ S T = 14 := by
  simp only [s₀, F.bMax_eq, Nat.zero_mul, Nat.add_zero]
  exact F.sCap_eq

/-- **The general chain length, evaluated.**  `zMin` of `minimum link-count definition` is `filecoinZMin`
here: no break weakens either entry, and both constants are the closed forms above. -/
theorem zMin_eq (F : FilecoinLatencyParameters S T) (ℓ : ℕ) :
    zMin S T ℓ = filecoinZMin S.gpi ℓ := by
  rw [zMin_eq_zMinNoBreak F.bMax_eq, F.sCap_eq_sCapOf, F.zMinNoBreak_eq]

/-- Formal corollary corresponding to `cor:filecoin`: after substituting the
Filecoin numerical certificates, the chain length is exactly `filecoinZMin`. -/
theorem latency_corollary (F : FilecoinLatencyParameters S T)
    {V : Type u} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (GR : GeneralRegime S)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5) (hℓ : 14 < ℓ)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((filecoinZMin S.gpi ℓ : ℝ) - 1) *
          ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) := by
  have hρ : 0 < S.ρ := by rw [F.rho_eq]; norm_num
  have hσapi : T.σ < G.αpi := by rw [F.sigma_eq, hαpi]; norm_num
  have hinside : s₀ S T < ℓ := by rw [F.s₀_eq]; exact hℓ
  have hpath := latency_general G P T GR hn hρ hσapi hDepth hinside A hA hred hweight
  simpa only [latencyLength, hαpi, F.sigma_eq, F.zMin_eq] using hpath

end FilecoinLatencyParameters

end ProofOfSpace

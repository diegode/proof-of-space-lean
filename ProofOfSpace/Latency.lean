import ProofOfSpace.PayChain

/-!
# The concrete latency theorems

This module contains the deterministic latency engine used by the Chung-8 result. The
chain itself lives in `PayChain.lean`, parameterized by the per-link payoff `y`; the
reference-trajectory accounting lives in `PotentialLedger.lean`. `latency_pay` is the
engine: it prices *any* source rule, and its head, per-link span, and budget charge are
`potHead`, `potSpan`, and `λρ/ĝ`; `λ` is the certificate's charge rate, `1.32` at the
Chung-8 parameters. A `RefChain` is an explicit argument because no reference chain is
valid for every `Setting`.

`latency_potential` and `latency_general` are `latency_pay` at the prefix source rule,
`y = α_π - σ`; `FullSources.lean` instantiates the same engine at `y = α_π`. At the
Chung-8 Filecoin parameters the prefix rule's asymptotic coefficient is greater than
`0.02135`, the full rule's greater than `0.0523`.
-/

namespace ProofOfSpace

/-- The path length supplied by a chain with `z` completed links. -/
def latencyLength (απ σ : ℝ) (n z : ℕ) : ℝ :=
  απ * n + ((z : ℝ) - 1) * (απ - σ) * n

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


namespace Concrete

namespace Pebbling

variable {V : Type u} {S : Setting} {ℓ n : ℕ} {G : LayeredGraph V S ℓ n}

/-- **The pebbling half of `first-source lemma`.**  Wherever the scalar
challenge footprint bound is fertile, so is the *actual* reachability footprint of a red-free
challenge set of weight `ζ_δ`.  This is the only thing a chain restart needs from the
graph beyond what an ordinary extension needs. -/
theorem challenge_fertile (P : Pebbling G) (hn : 0 < n) (hζ : 0 ≤ S.ζδ)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    {A : Finset V} (hA : A ⊆ G.layer 0) (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ weight n A) {b : ℕ} (hb : b < ℓ)
    (hfertScalar : S.pi ≤ (P.challengeBound_struct hζ).f b) :
    S.pi ≤ weight n (P.layerFootprint A b) := by
  have hstart : max 0 (S.ζδ - P.budget.spend 0) ≤ weight n (P.layerFootprint A 0) :=
    P.challenge_start_le hn hA hred hweight
  have hactual : P.challengeBound b ≤ weight n (P.layerFootprint A b) :=
    P.footprintBound_le hn (le_max_left _ _) hstart
      (fun {d} _ _ => by
        change P.challengeBound d ∈ Set.Icc S.αmin S.αmax
        exact ⟨S.αmin_lt_piBar.le.trans
          ((P.challengeBound_struct hζ).piBar_lt hζmax hentry d).le,
          (P.challengeBound_struct hζ).le_αmax hζmax hentry d⟩)
      (Nat.zero_le b) hb
  exact hfertScalar.trans (by simpa [challengeBound_struct] using hactual)

/-- The challenge-footprint comparison under the general entry condition used by
`latency_general`. -/
theorem challenge_fertile_gen (P : Pebbling G) (hn : 0 < n) (hζ : 0 ≤ S.ζδ)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.ζδ - S.ρ)
    {A : Finset V} (hA : A ⊆ G.layer 0) (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ weight n A) {b : ℕ} (hb : b < ℓ)
    (hfertScalar : S.pi ≤ (P.challengeBound_struct hζ).f b) :
    S.pi ≤ weight n (P.layerFootprint A b) := by
  let C := P.challengeBound_struct hζ
  have hstart : max 0 (S.ζδ - P.budget.spend 0) ≤ weight n (P.layerFootprint A 0) :=
    P.challenge_start_le hn hA hred hweight
  have hactual : P.challengeBound b ≤ weight n (P.layerFootprint A b) :=
    P.footprintBound_le hn (le_max_left _ _) hstart
      (fun {d} _ _ => ⟨hentry.le.trans (C.zetaFloor_le hζmax hentry d),
        (C.invariants_gen hζmax hentry d).2⟩)
      (Nat.zero_le b) hb
  exact hfertScalar.trans (by simpa [C, challengeBound_struct] using hactual)

end Pebbling

end Concrete

/-! ### The engine: any source rule, priced by the potential ledger -/

/--
**The latency bound at an arbitrary per-link payoff.**

A reference chain is an explicit argument. Unlike `Tracking.mid`, which always admits
the trivial value `σ`, no chain is admissible for
every `Setting` — the width condition `x (k+1) - x k ≥ ĝ` fails as soon as the gains do —
and is exhibited only where its conditions are theorems about the curve at hand.

The graph enters only through `hrule`. Everything else — the search for a fertile
expandable depth, the ledger that prices the chain in layers, the head, the span and the
black-budget charge — is independent of what a link is worth.
-/
theorem latency_pay {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C) {y : ℝ}
    (hn : 0 < n) (hy : 0 ≤ y) (hrule : Concrete.Pebbling.SourceRule P T y)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A (Concrete.Pebbling.payLength G y z) := by
  classical
  have hζ : 0 ≤ S.ζδ := by
    have h1 := S.piBar_pos
    have h2 := S.ρ_nonneg
    linarith
  let CS := P.payChainSystem T A hn hrule Cert.cs Cert.one_le_cs hslack
  let Ch := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ Ch.f b → Expandable P.budget T.ghat b Cert.cs →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.PayLink.base hrule hb hexp
      (P.challenge_fertile hn hζ hζmax hentry hA hred hweight hb hfertScalar), rfl, rfl⟩
  obtain ⟨L, hL⟩ := LedgerCert.ChainSystem.potential_count Cert CS Ch hζmax hentry
    (fun L => CS.link_floor hnobreak L) (fun L => CS.link_le_αmax L) hrestart hz1 hz
  exact P.hasPath_mono A (Concrete.Pebbling.payLength_mono hy hL) (CS.realizes L)

/-- **The asymptotic form of `latency_pay`.**  Past a fixed head — the initial search plus
the whole black budget, both priced by the ledger — every further layer buys `y / potSpan`
of unpebbled path.  This is the statement the certified slope lives in: the coefficient of
`ℓ` is `y / potSpan`, and nothing else in it grows with `ℓ`.  Eliminating the link count
costs one link, which is why the offset is `- 1`. -/
theorem latency_pay_asymptotic {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C) {y : ℝ}
    (hn : 0 < n) (hy : 0 ≤ y) (hrule : Concrete.Pebbling.SourceRule P T y)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    (hspan : 0 < LedgerCert.potSpan C Cert)
    (hlong : LedgerCert.potHead C Cert + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      (G.αpi * n + ((((ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat)
        / LedgerCert.potSpan C Cert) - 1) * y * n) := by
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
    have hmul : ((z : ℝ) - 1) * Sp < r * Sp := mul_lt_mul_of_pos_right hzlt hspan
    have hrS : r * Sp = (ℓ : ℝ) - LedgerCert.potHead C Cert
        - Cert.lam * S.ρ / T.ghat := by
      rw [hr]; field_simp
    linarith
  have hmain := latency_pay G P T Cert hn hy hrule hζmax hentry hnobreak hslack
    hz1 hz A hA hred hweight
  refine P.hasPath_mono A ?_ hmain
  have hyn : (0 : ℝ) ≤ y * n := mul_nonneg hy (Nat.cast_nonneg n)
  simp only [Concrete.Pebbling.payLength]
  nlinarith

/-! ### The break-aware general latency bound -/

/-- The adjusted challenge weight is nonnegative in the general regime. -/
theorem zetaDelta_nonneg {S : Setting} (GR : GeneralRegime S) : 0 ≤ S.ζδ := by
  have h := GR.entry
  simp only [Setting.zetaFloor] at h
  linarith [S.αmin_nonneg, S.ρ_nonneg]

/-- Concrete latency lower bound under exactly the general scalar conditions. -/
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
  have hy : (0 : ℝ) ≤ G.αpi - T.σ := by linarith
  let hrule := Concrete.Pebbling.sourceRule_prefix P T hn hσapi.le hDepth
  let CS := P.payChainSystem T A hn hrule 1 le_rfl (by simpa using T.lam_le_σ)
  let C := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ C.f b → Expandable P.budget T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.PayLink.base hrule hb hexp
      (P.challenge_fertile_gen hn hζ GR.zeta_le GR.entry hA hred hweight hb
        hfertScalar), rfl, rfl⟩
  have hchain := CS.latency_gen GR hρ C hrestart hinside (by
    intro z z' hzz' hz'
    exact P.hasPath_mono A (Concrete.Pebbling.payLength_mono hy hzz') hz')
  simpa only [Concrete.Pebbling.payLength, latencyLength] using hchain

/-! ### The potential-ledger latency bound -/

/--
**Concrete latency lower bound from the potential ledger.**

`latency_pay` at the prefix source rule: the source of a link is the first `σ n` nodes of
one depth-robust path inside the footprint, so a source node carries only the suffix
behind it and a completed link is worth `(α_π - σ) n`.  The graph assumption is ordinary
depth robustness at the fertility threshold.
-/
theorem latency_potential {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A (latencyLength G.αpi T.σ n z) := by
  classical
  exact latency_pay G P T Cert hn (by linarith)
    (Concrete.Pebbling.sourceRule_prefix P T hn hσapi.le hDepth)
    hζmax hentry hnobreak hslack hz1 hz A hA hred hweight

/-- **The asymptotic form at the prefix payoff.**  Every layer past the ledger head buys
another `(α_π - σ) / potSpan` of unpebbled path, under ordinary depth robustness at the
fertility threshold — the graph assumption of `latency_potential`, not the lower threshold
`FullSources.lean` asks for. -/
theorem latency_potential_asymptotic {V : Type u}
    {S : Setting} {ℓ n : ℕ} (G : Concrete.LayeredGraph V S ℓ n)
    (P : Concrete.Pebbling G) (T : Tracking S)
    {C : RefChain S T} (Cert : LedgerCert S T C)
    (hn : 0 < n) (hσapi : T.σ < G.αpi)
    (hDepth : G.DepthRobust G.αpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam)
    (hslack : T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ)
    (hspan : 0 < LedgerCert.potSpan C Cert)
    (hlong : LedgerCert.potHead C Cert + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ))
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : S.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      (G.αpi * n + ((((ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat)
        / LedgerCert.potSpan C Cert) - 1) * (G.αpi - T.σ) * n) := by
  classical
  exact latency_pay_asymptotic G P T Cert hn (by linarith)
    (Concrete.Pebbling.sourceRule_prefix P T hn hσapi.le hDepth)
    hζmax hentry hnobreak hslack hspan hlong A hA hred hweight

end ProofOfSpace

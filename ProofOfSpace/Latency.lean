import ProofOfSpace.Concrete
import ProofOfSpace.Ledger
import ProofOfSpace.PotentialLedger

/-!
# The concrete latency theorems

This module contains the deterministic latency engine used by the Chung-8 result. The
chain construction lives in `Chain.lean`, and the reference-trajectory accounting in
`PotentialLedger.lean`. `latency_potential` uses the reference-trajectory potential from
`PotentialLedger.lean`. Its head, per-link span, and budget charge are `potHead`,
`potSpan`, and `λρ/ĝ`; `λ` is the certificate's charge rate, `1.32` at the Chung-8
parameters. A `RefChain` is an explicit argument because no reference chain
is valid for every `Setting`. At the Chung-8 Filecoin parameters, the resulting
asymptotic coefficient is greater than `0.02135`.
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
  let CS := P.chainSystem T A hn hσapi.le hDepth 1 le_rfl (by simpa using T.lam_le_σ)
  let C := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ C.f b → Expandable P.budget T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.Link.base hn hσapi.le hDepth hb hexp
      (P.challenge_fertile_gen hn hζ GR.zeta_le GR.entry hA hred hweight hb
        hfertScalar), rfl, rfl⟩
  have hchain := CS.latency_gen GR hρ C hrestart hinside (by
    intro z z' hzz' hz'
    apply P.hasPath_mono A _ hz'
    simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using
      latencyLength_mono hσapi.le hzz')
  simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using hchain

/-! ### The potential-ledger latency bound -/

/--
**Concrete latency lower bound from the potential ledger.**

A reference chain is an explicit argument. Unlike `Tracking.mid`, which always admits
the trivial value `σ`, no chain is admissible for
every `Setting` — the width condition `x (k+1) - x k ≥ ĝ` fails as soon as the gains do —
and is exhibited only where its conditions are theorems about the curve at hand.
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
  have hζ : 0 ≤ S.ζδ := by
    have h1 := S.piBar_pos
    have h2 := S.ρ_nonneg
    linarith
  let CS := P.chainSystem T A hn hσapi.le hDepth Cert.cs Cert.one_le_cs hslack
  let Ch := P.challengeBound_struct hζ
  have hrestart : ∀ b : ℕ, b < ℓ → S.pi ≤ Ch.f b → Expandable P.budget T.ghat b Cert.cs →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1 := fun b hb hfertScalar hexp =>
    ⟨Concrete.Pebbling.Link.base hn hσapi.le hDepth hb hexp
      (P.challenge_fertile hn hζ hζmax hentry hA hred hweight hb hfertScalar), rfl, rfl⟩
  obtain ⟨L, hL⟩ := LedgerCert.ChainSystem.potential_count Cert CS Ch hζmax hentry
    (fun L => CS.link_floor hnobreak L) (fun L => CS.link_le_αmax L) hrestart hz1 hz
  refine P.hasPath_mono A ?_ (CS.realizes L)
  simpa only [Concrete.Pebbling.chainPathLength, latencyLength] using
    latencyLength_mono (απ := G.αpi) (σ := T.σ) (n := n) hσapi.le hL

end ProofOfSpace

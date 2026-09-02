/-
# The potential ledger for the fertile–expandable search

The reference-trajectory potential of `Potential.lean` prices both infertile skips and
blocked ranges in a single ledger:

    (p - t) + Ψ p  ≤  Ψ t + [loss if the position is fertile] + λ · X / ĝ,
    Ψ d = m - refPot (f d),

carried through both kinds of search step, where `X` is the spend on `(t, p]`.  At a
fertile stopping position `Ψ ≥ 0`, so the span is `Ψ t + loss + λ X / ĝ`.

Three numerical certificates make the induction go through, packaged as `LedgerCert`:

* `topLip` — reached from at or above the top chain point, `refPot` falls at rate
  `1/(x_m - x_{m-1})`, not at the global rate `1/ĝ`.  That is the only rate the ledger
  ever needs, because a fertile position always has `β_δ f ≥ β_δ π > x_m`, and it is
  where `λ` comes down: at the Chung-8 chain `1/(x₄-x₃) = 6.46` against `1/ĝ = 8.98`.
* `chord` — the top-bucket chord of `β_δ`, in potential units.  An infertile step
  carrying saturation loss `θ` sits `κ θ` above `x_m` after one free level, so staying
  infertile costs more than `(x_m - π) + κ θ` of spend; `inf_rate` prices that.
* `blockDrop` — a blocked range below a fertile depth begins with one free level, so its
  endpoint is at least `β_δ π - x` and the potential it can destroy is affine in its own
  spend `x`.  `blk_rate` prices that against the `(k + cs) ĝ` the block itself needs.

The slack `cs` is the expandability constant the search runs at: `Expandable B ĝ t cs`
asks for `(i + cs) ĝ`, and `mirror_floor` accepts any `cs ≤ 1 + (σ - π̂)/ĝ` because it
proves the tracked footprint stays above `σ` when only `π̂` is required.  A larger `cs`
shortens every blocked range.

All of them are statements about the chain alone, discharged numerically for the Chung-8
chain.  Nothing here assumes the chain is the `β_δ` orbit.
-/
import ProofOfSpace.Potential
import ProofOfSpace.Chain

namespace ProofOfSpace

open Set Finset

variable {S : Setting} {B : Budget S} {T : Tracking S}

/--
**The two per-step certificates of the potential ledger.**

`lam` is the charge rate, in levels per unit of black-pebble weight divided by `ĝ`, and
`loss` bounds the saturation loss `refPot v - (m-1)` below `π`.  `Continuation.lean`'s
accounting is the special case `lam = 2`, `loss = 1`, which every chain satisfies; the
content is that a good chain does much better.
-/
structure LedgerCert (S : Setting) (T : Tracking S) (C : RefChain S T) where
  /-- Levels charged per unit spend, in units of `1/ĝ`. -/
  lam : ℝ
  /-- Bound on the saturation loss of a subfertile value. -/
  loss : ℝ
  /-- The expandability slack the search runs at: a link is `(i + cs) ĝ`-expandable.
  `cs = 1` is the classical notion; a larger `cs` shortens every blocked range. -/
  cs : ℝ
  /-- The width `x_m - x_{m-1}` of the top bucket. -/
  wtop : ℝ
  /-- The top-bucket chord slope of `β_δ`, measured per unit of potential. -/
  kappa : ℝ
  /-- Affine drop bound of a blocked range: slope and offset. -/
  a2 : ℝ
  b2 : ℝ
  one_le_lam : 1 ≤ lam
  loss_nonneg : 0 ≤ loss
  one_le_cs : 1 ≤ cs
  wtop_pos : 0 < wtop
  kappa_nonneg : 0 ≤ kappa
  /-- Below `π` the potential is within `loss` of saturation-minus-one. -/
  loss_ge : ∀ v, C.x 0 ≤ v → v ≤ S.pi → C.refPot v - ((C.m : ℝ) - 1) ≤ loss
  /-- **The top-bucket Lipschitz bound.**  Reached from at or above the top chain point,
  the potential falls at rate `1/wtop`, not at the global rate `1/ĝ`.  This is the only
  place the ledger looks at, because a fertile position always has `β_δ f ≥ β_δ π > x_m`. -/
  topLip : ∀ u v : ℝ, C.x C.m ≤ u → v ≤ u →
    C.refPot u - C.refPot v ≤ (u - v) / wtop
  /-- The top-bucket chord of `β_δ`, in potential units: a position carrying saturation
  loss `θ` already sits `κ θ` above the top chain point after one free level. -/
  chord : ∀ v : ℝ, C.x (C.m - 1) ≤ v → v ≤ S.pi →
    C.x C.m + kappa * (C.refPot v - ((C.m : ℝ) - 1)) ≤ S.betaD v
  /-- `ĝ ≤ λ · wtop`: one unit of spend never costs more than `λ/ĝ` in the top bucket. -/
  ghat_le_lam_wtop : T.ghat ≤ lam * wtop
  /-- **The infertile rate.**  A step that stays infertile spends more than
  `(x_m - π) + κ θ`, and that pays for both the level and the saturation loss `θ`. -/
  inf_rate : ∀ θ s : ℝ, 0 ≤ θ → θ ≤ loss → 0 ≤ s →
    (C.x C.m - S.pi) + kappa * θ ≤ s → θ + (s - kappa * θ) / wtop ≤ lam * s / T.ghat
  /-- **The blocked-range drop.**  A blocked range below a fertile depth begins with one
  free level, so its endpoint is at least `β_δ π - x`; the potential it can lose is an
  affine function of its own spend `x`. -/
  blockDrop : ∀ x : ℝ, (1 + cs) * T.ghat ≤ x → x ≤ S.ρ →
    ((C.m : ℝ)) - C.refPot (S.betaD S.pi - x) ≤ a2 * x + b2
  /-- The affine drop bound already covers one whole level. -/
  blockDrop_one : ∀ x : ℝ, (1 + cs) * T.ghat ≤ x → 1 ≤ a2 * x + b2
  /-- **The blocked rate.**  `x` is the spend witnessing the block, `y` the spend at the
  level the search resumes from. -/
  blk_rate : ∀ x y : ℝ, (1 + cs) * T.ghat ≤ x → x ≤ S.ρ → 0 ≤ y →
    (x / T.ghat - cs + 1) + (a2 * x + b2 - 1) + y / T.ghat
      ≤ -loss + lam * (x + y) / T.ghat

namespace RefChain

variable (C : RefChain S T)

/-- The remaining-potential of the ledger: how far the footprint is from saturating the
chain. -/
noncomputable def psi (f : ℕ → ℝ) (d : ℕ) : ℝ := (C.m : ℝ) - C.refPot (f d)

theorem psi_nonneg (f : ℕ → ℝ) (d : ℕ) : 0 ≤ C.psi f d := by
  have := C.refPot_le_m (f d)
  simp only [psi]
  linarith

/-- One free level of the footprint recurrence, read through the potential. -/
theorem refPot_level {f : ℕ → ℝ} {start d : ℕ} (hbound : IsFootprintBound S B start f)
    (hd : start ≤ d) (hmem : f d ∈ Icc (0 : ℝ) 1) (hbase : C.x 0 ≤ f d)
    (hgain : 0 ≤ S.gainD (f d)) :
    min (C.refPot (f d) + 1) (C.m : ℝ) - B.spend (d + 1) / T.ghat
      ≤ C.refPot (f (d + 1)) := by
  have hstep := C.refPot_step hmem hbase
  have hbeta0 : 0 ≤ S.betaD (f d) := by
    rw [S.betaD_eq]; linarith [hmem.1]
  have hle : f (d + 1) ≤ S.betaD (f d) := by
    rw [hbound d hd]
    exact max_le hbeta0 (by linarith [B.spend_nonneg (d + 1)])
  have hge : S.betaD (f d) - B.spend (d + 1) ≤ f (d + 1) := by
    rw [hbound d hd]
    exact le_max_right _ _
  have hlip := C.refPot_lipschitz hle
  have hdiv : (S.betaD (f d) - f (d + 1)) / T.ghat ≤ B.spend (d + 1) / T.ghat := by
    rw [div_le_div_iff_of_pos_right T.ghat_pos]
    linarith
  linarith

end RefChain

namespace ChainSystem

variable {cs : ℝ} {ℓ : ℕ} {Realizes : ℕ → Prop}

/-! ### The no-break hypotheses of the ledger, discharged for a chain system

`search_ledger` asks only that the tracked footprint stay inside `[π̂, α_δ^max]` at every
depth below the link it starts from.  For a chain system both halves are theorems in the
no-break regime, and neither is a new assumption: the upper one is the enclosure
`IsFootprintBound.le_αmax`, and the lower one is `Growth.mirror_floor` while the
footprint is still below `π` and `Growth.post_floor` once it has passed it.  The
no-break condition `ρ < β_δ(π) - π̂` — the very inequality `Ledger.bMax_eq_zero` turns
into "no break can be paid for" — is exactly what makes the post-fertile floor
`β_δ(π) - ρ` clear `π̂`.
-/

/-- A link's tracked footprint never leaves the active interval. -/
theorem link_le_αmax (CS : ChainSystem.{u} S B T cs ℓ Realizes) (L : CS.Link) :
    ∀ d, CS.depth L ≤ d → CS.wt L d ≤ S.αmax := by
  intro d hd
  have hinit : CS.wt L (CS.depth L) = T.σ := CS.init L
  exact ((CS.bound L).le_αmax (by rw [hinit]; exact T.σ_pos.le)
    (by rw [hinit]; exact T.σ_lt_αmax.le) d hd).2

/-- **A link's tracked footprint never falls below the tracking floor**, in the no-break
regime. -/
theorem link_floor (CS : ChainSystem.{u} S B T cs ℓ Realizes)
    (hnobreak : S.ρ < S.betaD S.pi - T.lam) (L : CS.Link) :
    ∀ d, CS.depth L ≤ d → T.lam ≤ CS.wt L d := by
  intro d hd
  set b := CS.depth L with hb
  set f := CS.wt L with hf
  have hbound : IsFootprintBound S B b f := CS.bound L
  have hinit : f b = T.σ := CS.init L
  have hexp : Expandable B T.ghat b cs := CS.expandable L
  have hcond : S.αmin + S.ρ < S.betaD S.pi := by
    have := T.αmin_lt_lam
    linarith
  by_cases hfe : ∃ d0, b ≤ d0 ∧ d0 ≤ d ∧ S.pi ≤ f d0
  · obtain ⟨d0, hd0b, hd0d, hd0f⟩ := hfe
    rcases eq_or_lt_of_le hd0d with rfl | hlt
    · exact le_trans T.lam_lt_pi.le hd0f
    · have hpost := post_floor hbound (by rw [hinit]; exact T.σ_pos.le)
        (by rw [hinit]; exact T.σ_lt_αmax.le) hcond hd0b hd0f d hlt
      linarith
  · push Not at hfe
    have hle : ∀ i, i ≤ d - b → f (b + i) ≤ S.pi := fun i hi =>
      (hfe (b + i) (by omega) (by omega)).le
    have hfloor := mirror_floor CS.cs_slack hexp hbound hinit hle (d - b) le_rfl
    rwa [show b + (d - b) = d from by omega] at hfloor

end ChainSystem

/-! ### The two kinds of step -/

namespace LedgerCert

variable {C : RefChain S T} (Cert : LedgerCert S T C)

/-- **The infertile step.**  One level.  Below the top chain point the free level is
worth a full unit of potential and the spend is charged at `1/ĝ`; above it the step is
priced by the top-bucket chord and the top-bucket Lipschitz constant instead, which is
what makes `λ` small. -/
theorem step_infertile {f : ℕ → ℝ} {start d : ℕ} (hbound : IsFootprintBound S B start f)
    (hd : start ≤ d) (hmem : f d ∈ Icc (0 : ℝ) 1) (hbase : C.x 0 ≤ f d)
    (hgain : 0 ≤ S.gainD (f d)) (hinf : f d ≤ S.pi) :
    1 + C.psi f (d + 1) - C.psi f d
      ≤ (if S.pi ≤ f (d + 1) then Cert.loss else 0)
        + Cert.lam * B.spend (d + 1) / T.ghat := by
  have hs : 0 ≤ B.spend (d + 1) := B.spend_nonneg _
  have hif0 : (0 : ℝ) ≤ (if S.pi ≤ f (d + 1) then Cert.loss else 0) := by
    split_ifs
    · exact Cert.loss_nonneg
    · exact le_rfl
  have hge : S.betaD (f d) - B.spend (d + 1) ≤ f (d + 1) := by
    rw [hbound d hd]; exact le_max_right _ _
  by_cases hsat : C.refPot (f d) ≤ (C.m : ℝ) - 1
  · -- unsaturated: one free level is worth a whole unit
    have hlevel := C.refPot_level hbound hd hmem hbase hgain
    rw [min_eq_left (by linarith)] at hlevel
    have hlam : B.spend (d + 1) / T.ghat ≤ Cert.lam * B.spend (d + 1) / T.ghat := by
      rw [div_le_div_iff_of_pos_right T.ghat_pos]
      nlinarith [Cert.one_le_lam]
    simp only [RefChain.psi]
    linarith
  · -- saturating: the step carries a loss `θ`, and the chord prices it
    push Not at hsat
    set θ : ℝ := C.refPot (f d) - ((C.m : ℝ) - 1) with hθdef
    have hθ0 : 0 ≤ θ := by simp only [hθdef]; linarith
    have hθloss : θ ≤ Cert.loss := Cert.loss_ge _ hbase hinf
    have hmcast : ((C.m - 1 : ℕ) : ℝ) = (C.m : ℝ) - 1 := by
      have := C.m_pos
      push_cast [Nat.cast_sub (by omega : 1 ≤ C.m)]
      ring
    have hxm1 : C.x (C.m - 1) ≤ f d := by
      by_contra hcon
      push Not at hcon
      have hmono := C.refPot_mono hcon.le
      rw [C.refPot_x (by omega), hmcast] at hmono
      simp only [hθdef] at hθ0
      linarith
    have hchord := Cert.chord (f d) hxm1 hinf
    by_cases hbig : C.x C.m ≤ f (d + 1)
    · -- the step overshoots the top chain point: it costs only the loss it carried
      have hfert : S.pi ≤ f (d + 1) := le_trans C.top hbig
      have hmax : C.refPot (f (d + 1)) = (C.m : ℝ) := C.refPot_eq_m hbig
      have hpos : 0 ≤ Cert.lam * B.spend (d + 1) / T.ghat :=
        div_nonneg (mul_nonneg (by linarith [Cert.one_le_lam]) hs) T.ghat_pos.le
      simp only [RefChain.psi, hfert, if_true, hmax, hθdef] at *
      linarith
    · push Not at hbig
      have hdrop : (C.m : ℝ) - C.refPot (f (d + 1)) ≤ (C.x C.m - f (d + 1)) / Cert.wtop := by
        have h := Cert.topLip (C.x C.m) (f (d + 1)) le_rfl hbig.le
        rwa [C.refPot_x le_rfl] at h
      have hgap : C.x C.m - f (d + 1) ≤ B.spend (d + 1) - Cert.kappa * θ := by
        simp only [hθdef] at hchord ⊢; linarith
      have hdiv : (C.x C.m - f (d + 1)) / Cert.wtop
          ≤ (B.spend (d + 1) - Cert.kappa * θ) / Cert.wtop := by
        rw [div_le_div_iff_of_pos_right Cert.wtop_pos]; exact hgap
      have hkey : 1 + C.psi f (d + 1) - C.psi f d
          ≤ θ + (B.spend (d + 1) - Cert.kappa * θ) / Cert.wtop := by
        simp only [RefChain.psi, hθdef]
        linarith
      by_cases hfert : S.pi ≤ f (d + 1)
      · -- lands fertile: the released allowance covers `θ`
        have hw : (B.spend (d + 1) - Cert.kappa * θ) / Cert.wtop
            ≤ Cert.lam * B.spend (d + 1) / T.ghat := by
          have h1 : (B.spend (d + 1) - Cert.kappa * θ) / Cert.wtop
              ≤ B.spend (d + 1) / Cert.wtop := by
            rw [div_le_div_iff_of_pos_right Cert.wtop_pos]
            nlinarith [Cert.kappa_nonneg, hθ0]
          have h2 : B.spend (d + 1) / Cert.wtop ≤ Cert.lam * B.spend (d + 1) / T.ghat := by
            rw [div_le_div_iff₀ Cert.wtop_pos T.ghat_pos]
            nlinarith [Cert.ghat_le_lam_wtop, hs]
          linarith
        simp only [hfert, if_true]
        linarith
      · -- stays infertile: the chord forces the spend, and `inf_rate` prices it
        push Not at hfert
        have hspend : (C.x C.m - S.pi) + Cert.kappa * θ ≤ B.spend (d + 1) := by
          simp only [hθdef] at hchord ⊢; linarith
        have := Cert.inf_rate θ (B.spend (d + 1)) hθ0 hθloss hs hspend
        simp only [hfert.not_ge, if_false]
        linarith

/-- **The blocked step.**  A blocked range of `k + 1` levels below a fertile depth is
paid for by the spend that witnesses the block: it needs more than `(k + cs) ĝ`, and the
range's own first free level puts its endpoint above `β_δ π - x`, so the potential it can
destroy is `blockDrop`, not the whole Lipschitz drop. -/
theorem step_blocked {f : ℕ → ℝ} {start p k : ℕ} (hbound : IsFootprintBound S B start f)
    (hp : start ≤ p) (hk : 1 ≤ k) (hfert : S.pi ≤ f p) (hmemp : f p ∈ Icc (0 : ℝ) 1)
    (hgains : ∀ i, i < k → 0 ≤ S.gainD (f (p + i)))
    (hmem : f (p + k) ∈ Icc (0 : ℝ) 1) (hbase : C.x 0 ≤ f (p + k))
    (hgain : 0 ≤ S.gainD (f (p + k)))
    (hwitness : ((k : ℝ) + Cert.cs) * T.ghat
      < ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d) :
    ((k : ℝ) + 1) + C.psi f (p + k + 1) - C.psi f p
      ≤ (if S.pi ≤ f (p + k + 1) then Cert.loss else 0) - Cert.loss
        + Cert.lam * (∑ d ∈ Finset.Ico (p + 1) (p + k + 2), B.spend d) / T.ghat := by
  classical
  set sw : ℝ := ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d with hsw
  set sq : ℝ := B.spend (p + k + 1) with hsq
  have hsqnn : 0 ≤ sq := B.spend_nonneg _
  have hswρ : sw ≤ S.ρ := B.sum_Ico_le _ _
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlow : (1 + Cert.cs) * T.ghat ≤ sw := by
    nlinarith [T.ghat_pos, hwitness, hkR]
  have hstot : ∑ d ∈ Finset.Ico (p + 1) (p + k + 2), B.spend d = sw + sq := by
    rw [hsw, hsq, show p + k + 2 = (p + k + 1) + 1 from by omega,
      Finset.sum_Ico_succ_top (by omega)]
  -- the range's own first free level: its endpoint stays above `β_δ π - sw`
  have hdrop : S.betaD S.pi - sw ≤ f (p + k) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hid := hbound.sum_le hp (j + 1)
    have hshift : ∑ m ∈ Finset.range (j + 1), B.spend (p + m + 1) = sw := by
      rw [hsw]; exact B.sum_shift p (j + 1)
    rw [hshift] at hid
    have hsplit : ∑ i ∈ Finset.range (j + 1), S.gainD (f (p + i))
        = (∑ i ∈ Finset.range j, S.gainD (f (p + (i + 1)))) + S.gainD (f (p + 0)) :=
      Finset.sum_range_succ' _ j
    have htail : 0 ≤ ∑ i ∈ Finset.range j, S.gainD (f (p + (i + 1))) :=
      Finset.sum_nonneg fun i hi => hgains (i + 1) (by
        simpa using Nat.succ_lt_succ (Finset.mem_range.mp hi))
    have hbeta : S.betaD S.pi ≤ S.betaD (f p) :=
      S.betaD_strictMonoOn.monotoneOn S.pi_mem_Icc hmemp hfert
    simp only [Setting.betaD_eq] at hbeta ⊢
    simp only [Nat.add_zero] at hsplit
    linarith
  -- the potential the range can destroy
  have hΦ : (C.m : ℝ) - C.refPot (f (p + k)) ≤ Cert.a2 * sw + Cert.b2 := by
    have hmono := C.refPot_mono hdrop
    have := Cert.blockDrop sw hlow hswρ
    linarith
  have hone := Cert.blockDrop_one sw hlow
  -- one more free level, at the depth the search resumes from
  have hlevel := C.refPot_level hbound (show start ≤ p + k from by omega) hmem hbase hgain
  rw [← hsq] at hlevel
  have hminle : (C.m : ℝ) - min (C.refPot (f (p + k)) + 1) (C.m : ℝ)
      ≤ Cert.a2 * sw + Cert.b2 - 1 := by
    rcases le_total (C.refPot (f (p + k)) + 1) (C.m : ℝ) with hc | hc
    · rw [min_eq_left hc]; linarith
    · rw [min_eq_right hc]; linarith
  -- the level count the witness pays for
  have hq : ((k : ℝ) + 1) ≤ sw / T.ghat - Cert.cs + 1 := by
    have h : (k : ℝ) + Cert.cs ≤ sw / T.ghat := by
      rw [le_div_iff₀ T.ghat_pos]; linarith [hwitness]
    linarith
  have hrate := Cert.blk_rate sw sq hlow hswρ hsqnn
  have hcap := C.refPot_le_m (f p)
  have hif0 : (0 : ℝ) ≤ (if S.pi ≤ f (p + k + 1) then Cert.loss else 0) := by
    split_ifs
    · exact Cert.loss_nonneg
    · exact le_rfl
  rw [hstot]
  simp only [RefChain.psi]
  linarith

/-!
### The search

`Search.lean`'s search is run unchanged; only its accounting is replaced.  At an
infertile position it advances one level, at a fertile one it is blockable and jumps the
witnessed range, and the two step lemmas above are exactly the two cases.
-/

/--
**The potential ledger.**

Search forward from `t` for a depth that is both fertile and `ĝ`-expandable.  Within
`Ψ t + loss + λ X / ĝ` levels the search reaches one, or passes `ℓ`; here `X` is the
spend strictly below `t` down to the depth reached.

The hypotheses are the no-break ones: the tracked footprint stays above the tracking
floor and below `α_δ^max` at *every* depth below `t`.  That is what the no-break regime
supplies, and it is the regime in which the joint entry of `Ledger.zMin` is claimed.
-/
theorem search_ledger {f : ℕ → ℝ} {t ℓ : ℕ}
    (hbound : IsFootprintBound S B t f)
    (hfloor : ∀ d, t ≤ d → T.lam ≤ f d)
    (hmax : ∀ d, t ≤ d → f d ≤ S.αmax) :
    ∃ t2, t ≤ t2 ∧ (f t < S.pi → t < ℓ → t < t2) ∧
      (ℓ ≤ t2 ∨ (S.pi ≤ f t2 ∧ Expandable B T.ghat t2 Cert.cs)) ∧
      ((t2 - t : ℕ) : ℝ) ≤ C.psi f t + Cert.loss
        + Cert.lam * (∑ d ∈ Finset.Ico (t + 1) (t2 + 1), B.spend d) / T.ghat := by
  classical
  have hgainall : ∀ d, t ≤ d → 0 ≤ S.gainD (f d) := fun d hd =>
    S.gainD_nonneg ⟨le_of_lt (lt_of_lt_of_le T.αmin_lt_lam (hfloor d hd)), hmax d hd⟩
  have hmemall : ∀ d, t ≤ d → f d ∈ Icc (0 : ℝ) 1 := fun d hd =>
    ⟨le_trans S.αmin_nonneg (le_of_lt (lt_of_lt_of_le T.αmin_lt_lam (hfloor d hd))),
      le_trans (hmax d hd) S.αmax_le_one⟩
  have hbaseall : ∀ d, t ≤ d → C.x 0 ≤ f d := fun d hd => le_trans C.base (hfloor d hd)
  set Fert : ℕ → Prop := fun d => S.pi ≤ f d with hFert
  have hex : ∃ j, (Fert (searchPos B T.ghat Cert.cs Fert t j) ∧
      Expandable B T.ghat (searchPos B T.ghat Cert.cs Fert t j) Cert.cs) ∨
      ℓ ≤ searchPos B T.ghat Cert.cs Fert t j := by
    refine ⟨ℓ, Or.inr ?_⟩
    have := le_searchPos (B := B) (g := T.ghat) (cs := Cert.cs) (Fert := Fert) (t := t) ℓ
    omega
  set J := Nat.find hex with hJ
  set t2 := searchPos B T.ghat Cert.cs Fert t J with ht2
  have hJspec : (Fert t2 ∧ Expandable B T.ghat t2 Cert.cs) ∨ ℓ ≤ t2 := Nat.find_spec hex
  have hbad : ∀ j, j < J →
      ¬(Fert (searchPos B T.ghat Cert.cs Fert t j) ∧
        Expandable B T.ghat (searchPos B T.ghat Cert.cs Fert t j) Cert.cs) := by
    intro j hj hcon
    exact (Nat.find_min hex hj) (Or.inl hcon)
  -- the ledger invariant, carried along the search
  have hinv : ∀ j, j ≤ J →
      ((searchPos B T.ghat Cert.cs Fert t j - t : ℕ) : ℝ)
          + C.psi f (searchPos B T.ghat Cert.cs Fert t j)
        ≤ C.psi f t
          + (if S.pi ≤ f (searchPos B T.ghat Cert.cs Fert t j) then Cert.loss else 0)
          + Cert.lam
              * (∑ d ∈ Finset.Ico (t + 1) (searchPos B T.ghat Cert.cs Fert t j + 1), B.spend d)
              / T.ghat := by
    intro j
    induction j with
    | zero =>
        intro _
        have h0 : searchPos B T.ghat Cert.cs Fert t 0 = t := searchPos_zero
        have hif : (0 : ℝ) ≤ (if S.pi ≤ f t then Cert.loss else 0) := by
          split_ifs
          · exact Cert.loss_nonneg
          · exact le_rfl
        rw [h0]
        simp only [Nat.sub_self, Nat.cast_zero, Finset.Ico_self, Finset.sum_empty,
          mul_zero, zero_div, zero_add, add_zero]
        linarith
    | succ j ih =>
        intro hj
        have hjJ : j < J := by omega
        have ihj := ih (by omega)
        set p := searchPos B T.ghat Cert.cs Fert t j with hp
        have hpt : t ≤ p := base_le_searchPos j
        have hsplit : ∀ b : ℕ, p + 1 ≤ b →
            ∑ d ∈ Finset.Ico (t + 1) b, B.spend d
              = (∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d)
                + ∑ d ∈ Finset.Ico (p + 1) b, B.spend d := by
          intro b hb
          rw [Finset.sum_Ico_consecutive _ (by omega) hb]
        by_cases hF : Fert p
        · -- fertile, hence blockable: jump the witnessed range
          have hblock : Blockable B T.ghat p Cert.cs :=
            (not_expandable_iff_blockable B T.ghat p Cert.cs).mp fun hexp => hbad j hjJ ⟨hF, hexp⟩
          obtain ⟨hk1, hkspend⟩ := blockLen_spec hblock
          set k := blockLen B T.ghat p Cert.cs with hk
          have hnext : searchPos B T.ghat Cert.cs Fert t (j + 1) = p + k + 1 := by
            rw [searchPos_succ]; simp only [← hp, hF, if_true, ← hk]
          have hshift : ∑ m ∈ Finset.range k, B.spend (p + m + 1)
              = ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d := B.sum_shift p k
          have hwit : ((k : ℝ) + Cert.cs) * T.ghat
              < ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d := by
            rw [← hshift]; exact hkspend
          have hstep := Cert.step_blocked (f := f) (start := t) (p := p) (k := k)
            hbound hpt hk1 (by simpa only [hFert] using hF) (hmemall p hpt)
            (fun i _ => hgainall (p + i) (by omega))
            (hmemall (p + k) (by omega)) (hbaseall (p + k) (by omega))
            (hgainall (p + k) (by omega)) hwit
          have hcast : ((p + k + 1 - t : ℕ) : ℝ)
              = ((p - t : ℕ) : ℝ) + ((k : ℝ) + 1) := by
            have : p + k + 1 - t = (p - t) + (k + 1) := by omega
            rw [this]; push_cast; ring
          have hfp : (if S.pi ≤ f p then Cert.loss else 0) = Cert.loss := by
            simp only [hFert] at hF
            simp only [hF, if_true]
          rw [hnext, hcast]
          rw [hsplit (p + k + 2) (by omega)]
          rw [hfp] at ihj
          have hdiv : Cert.lam * ((∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d)
                + ∑ d ∈ Finset.Ico (p + 1) (p + k + 2), B.spend d) / T.ghat
              = Cert.lam * (∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d) / T.ghat
                + Cert.lam * (∑ d ∈ Finset.Ico (p + 1) (p + k + 2), B.spend d)
                  / T.ghat := by
            field_simp
          rw [hdiv]
          linarith
        · -- infertile: advance one level
          have hnext : searchPos B T.ghat Cert.cs Fert t (j + 1) = p + 1 := by
            rw [searchPos_succ]; simp only [← hp, hF, if_false]
          have hinf : f p ≤ S.pi := by
            simp only [hFert, not_le] at hF
            exact hF.le
          have hstep := Cert.step_infertile (f := f) (start := t) (d := p) hbound hpt
            (hmemall p hpt) (hbaseall p hpt) (hgainall p hpt) hinf
          have hcast : ((p + 1 - t : ℕ) : ℝ) = ((p - t : ℕ) : ℝ) + 1 := by
            have : p + 1 - t = (p - t) + 1 := by omega
            rw [this]; push_cast; ring
          have hfp : (if S.pi ≤ f p then Cert.loss else 0) = 0 := by
            simp only [hFert, not_le] at hF
            simp only [not_le.mpr hF, if_false]
          have hsum : ∑ d ∈ Finset.Ico (t + 1) (p + 1 + 1), B.spend d
              = (∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d) + B.spend (p + 1) := by
            rw [Finset.sum_Ico_succ_top (by omega)]
          rw [hnext, hcast, hsum]
          rw [hfp] at ihj
          have hdiv : Cert.lam * ((∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d)
                + B.spend (p + 1)) / T.ghat
              = Cert.lam * (∑ d ∈ Finset.Ico (t + 1) (p + 1), B.spend d) / T.ghat
                + Cert.lam * B.spend (p + 1) / T.ghat := by
            field_simp
          rw [hdiv]
          linarith
  have hstrict : f t < S.pi → t < ℓ → t < t2 := by
    intro hlow hlt
    rcases Nat.eq_or_lt_of_le (base_le_searchPos (B := B) (g := T.ghat) (Fert := Fert)
      (t := t) J) with heq | h
    · exfalso
      have heq' : t2 = t := by rw [ht2]; exact heq.symm
      rcases hJspec with ⟨hf, _⟩ | hl
      · rw [heq'] at hf
        simp only [hFert] at hf
        linarith
      · rw [heq'] at hl
        omega
    · exact h
  refine ⟨t2, base_le_searchPos J, hstrict, hJspec.symm, ?_⟩
  have hfin := hinv J le_rfl
  have hpsi := C.psi_nonneg f t2
  have hif : (if S.pi ≤ f t2 then Cert.loss else 0) ≤ Cert.loss := by
    split_ifs
    · exact le_rfl
    · exact Cert.loss_nonneg
  rw [← ht2] at hfin
  linarith

/-! ### From the ledger to a chain -/

/-- **The per-link span of the potential ledger.**  A fresh source of weight `σ` starts
with `m - refPot σ` of potential to burn, and one saturation allowance is released at
the fertile depth the search stops at.  This is the potential ledger's replacement for
`Chain.h₁`, and it is what fixes the certified slope. -/
noncomputable def potSpan (C : RefChain S T) (Cert : LedgerCert S T C) : ℝ :=
  ((C.m : ℝ) - C.refPot T.σ) + Cert.loss

theorem potSpan_nonneg (C : RefChain S T) (Cert : LedgerCert S T C) :
    0 ≤ potSpan C Cert := by
  have := C.refPot_le_m T.σ
  have := Cert.loss_nonneg
  simp only [potSpan]
  linarith

/-! ### The head, and the chain length it feeds -/

/-- **The head of the potential ledger**: the potential the challenge footprint starts
with, plus one saturation allowance.  It replaces `Chain.searchHead` together with the
`blockedCap` half of `sCap`; the ledger charges both to the same budget. -/
noncomputable def potHead (C : RefChain S T) (Cert : LedgerCert S T C) : ℝ :=
  ((C.m : ℝ) - C.refPot S.ζδ) + Cert.loss

/-- The initial search, priced by the ledger.  The spend it is charged is the whole
prefix `[0, b]`, including the challenge level itself, so it composes with
`potential_links` without charging any level twice. -/
theorem search_head {C : RefChain S T} (Cert : LedgerCert S T C)
    (Ch : ChallengeBound S B) (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (ℓ : ℕ) :
    ∃ b, (ℓ ≤ b ∨ (S.pi ≤ Ch.f b ∧ Expandable B T.ghat b Cert.cs)) ∧
      (b : ℝ) ≤ potHead C Cert
        + Cert.lam * (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) / T.ghat := by
  obtain ⟨b, _, _, hout, hspan⟩ :=
    Cert.search_ledger (C := C) (f := Ch.f) (t := 0) (ℓ := ℓ) Ch.bound
      (fun d _ => le_trans T.lam_le_piBar (Ch.piBar_lt hζmax hentry d).le)
      (fun d _ => Ch.le_αmax hζmax hentry d)
  refine ⟨b, hout, ?_⟩
  have hspend0 := B.spend_nonneg 0
  -- the challenge level's own spend is the only gap between `ζ_δ` and `f 0`
  have hlip : C.refPot S.ζδ - C.refPot (Ch.f 0) ≤ B.spend 0 / T.ghat := by
    refine le_trans (C.refPot_lipschitz Ch.init_le) ?_
    rw [div_le_div_iff_of_pos_right T.ghat_pos]
    linarith [Ch.init_ge]
  have hpsi : C.psi Ch.f 0 ≤ ((C.m : ℝ) - C.refPot S.ζδ) + B.spend 0 / T.ghat := by
    simp only [RefChain.psi]
    linarith
  have hsplit : (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d)
      = B.spend 0 + ∑ d ∈ Finset.Ico 1 (b + 1), B.spend d := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 1) (by omega : 1 ≤ b + 1)]
    simp
  have hcast : ((b - 0 : ℕ) : ℝ) = (b : ℝ) := by simp
  rw [hcast] at hspan
  have hsum0 : 0 ≤ ∑ d ∈ Finset.Ico 1 (b + 1), B.spend d :=
    Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hdiv : Cert.lam * (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) / T.ghat
      = Cert.lam * B.spend 0 / T.ghat
        + Cert.lam * (∑ d ∈ Finset.Ico 1 (b + 1), B.spend d) / T.ghat := by
    rw [hsplit]
    field_simp
  have hlam0 : B.spend 0 / T.ghat ≤ Cert.lam * B.spend 0 / T.ghat := by
    rw [div_le_div_iff_of_pos_right T.ghat_pos]
    nlinarith [Cert.one_le_lam]
  simp only [potHead]
  rw [hdiv]
  linarith



namespace ChainSystem

variable {cs : ℝ} {ℓ : ℕ} {Realizes : ℕ → Prop}

/--
**Chain length from the potential ledger.**

Running `search_ledger` from a link produces the next one, and the windows of successive
runs are disjoint, so the whole construction is charged the budget once.  A chain of
`j + 1` links therefore exists as soon as `j` spans plus the one-time budget charge fit
below the first link.

Only the no-break hypotheses are used, because that is all `search_ledger` needs; the
break-aware accounting of `Ledger.lean` is untouched.
-/
theorem potential_links {C : RefChain S T} (Cert : LedgerCert S T C)
    (CS : ChainSystem.{u} S B T Cert.cs ℓ Realizes)
    (hfloor : ∀ (L : CS.Link) d, CS.depth L ≤ d → T.lam ≤ CS.wt L d)
    (hmax : ∀ (L : CS.Link) d, CS.depth L ≤ d → CS.wt L d ≤ S.αmax)
    (L0 : CS.Link) :
    ∀ j : ℕ,
      ((CS.depth L0 : ℝ) + (j : ℝ) * potSpan C Cert
        + Cert.lam * (S.ρ - ∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d) / T.ghat
          < (ℓ : ℝ)) →
      ∃ L : CS.Link, CS.count L0 + j ≤ CS.count L ∧ CS.depth L0 ≤ CS.depth L ∧
        (CS.depth L : ℝ) ≤ (CS.depth L0 : ℝ) + (j : ℝ) * potSpan C Cert
          + Cert.lam
              * (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (CS.depth L + 1), B.spend d)
              / T.ghat := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨L0, by omega, le_rfl, ?_⟩
      simp
  | succ j ih =>
      intro hfit
      have hspan := potSpan_nonneg C Cert
      have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      have hfitj : (CS.depth L0 : ℝ) + (j : ℝ) * potSpan C Cert
          + Cert.lam * (S.ρ - ∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d) / T.ghat
            < (ℓ : ℝ) := by
        rw [← hcast] at hfit
        nlinarith
      obtain ⟨L, hcount, hdle, hdepth⟩ := ih hfitj
      -- run the ledger from `L`
      obtain ⟨t2, ht2, hstrict, hout, hspan'⟩ :=
        Cert.search_ledger (C := C) (f := CS.wt L) (t := CS.depth L) (ℓ := ℓ)
          (CS.bound L) (hfloor L) (hmax L)
      have hinit : CS.wt L (CS.depth L) = T.σ := CS.init L
      have hpsi : C.psi (CS.wt L) (CS.depth L) = (C.m : ℝ) - C.refPot T.σ := by
        simp only [RefChain.psi, hinit]
      have hlt : CS.depth L < t2 := hstrict (by rw [hinit]; exact T.σ_lt) (CS.inside L)
      -- the two windows are consecutive, so their spends add
      have hVW : (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (CS.depth L + 1), B.spend d)
            + ∑ d ∈ Finset.Ico (CS.depth L + 1) (t2 + 1), B.spend d
          = ∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d := by
        refine Finset.sum_Ico_consecutive _ ?_ ?_ <;> omega
      have hcastsub : ((t2 - CS.depth L : ℕ) : ℝ) = (t2 : ℝ) - (CS.depth L : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hpsi, hcastsub] at hspan'
      have hlamdiv : Cert.lam
            * (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (CS.depth L + 1), B.spend d) / T.ghat
          + Cert.lam * (∑ d ∈ Finset.Ico (CS.depth L + 1) (t2 + 1), B.spend d) / T.ghat
          = Cert.lam
              * (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d) / T.ghat := by
        rw [← hVW]
        field_simp
      have ht2bound : (t2 : ℝ) ≤ (CS.depth L0 : ℝ) + ((j : ℝ) + 1) * potSpan C Cert
          + Cert.lam
              * (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d) / T.ghat := by
        rw [← hlamdiv]
        simp only [potSpan] at hdepth ⊢
        linarith
      -- the graph cannot end first
      have hnotpast : ¬ (ℓ ≤ t2) := by
        intro hpast
        have hsplit0 : (∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d)
              + ∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d
            = ∑ d ∈ Finset.Ico 0 (t2 + 1), B.spend d := by
          refine Finset.sum_Ico_consecutive _ ?_ ?_ <;> omega
        have hρ : (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d)
            ≤ S.ρ - ∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d := by
          have := B.sum_Ico_le 0 (t2 + 1)
          linarith [hsplit0]
        have hmono : Cert.lam
              * (∑ d ∈ Finset.Ico (CS.depth L0 + 1) (t2 + 1), B.spend d) / T.ghat
            ≤ Cert.lam
              * (S.ρ - ∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d) / T.ghat := by
          rw [div_le_div_iff_of_pos_right T.ghat_pos]
          nlinarith [Cert.one_le_lam]
        have hcastℓ : ((ℓ : ℕ) : ℝ) ≤ (t2 : ℝ) := by exact_mod_cast hpast
        rw [← hcast] at hfit
        linarith
      rcases hout with hpast | ⟨hfert, hexp⟩
      · exact absurd hpast hnotpast
      · have ht2ℓ : t2 < ℓ := by omega
        obtain ⟨L', hdepth', hcount'⟩ := CS.extend L t2 hlt ht2ℓ hfert hexp
          (fun d hd _ => ⟨T.αmin_lt_lam.le.trans (hfloor L d hd), hmax L d hd⟩)
        refine ⟨L', by omega, by omega, ?_⟩
        rw [hdepth', ← hcast]
        exact ht2bound

/--
**The potential ledger's chain-length bound.**

The head and the links are charged against disjoint prefixes of the same budget, so the
whole construction pays `λ ρ / ĝ` once.
-/
theorem potential_count {C : RefChain S T} (Cert : LedgerCert S T C)
    (CS : ChainSystem.{u} S B T Cert.cs ℓ Realizes) (Ch : ChallengeBound S B)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (hfloor : ∀ (L : CS.Link) d, CS.depth L ≤ d → T.lam ≤ CS.wt L d)
    (hmax : ∀ (L : CS.Link) d, CS.depth L ≤ d → CS.wt L d ≤ S.αmax)
    (restart : ∀ b : ℕ, b < ℓ → S.pi ≤ Ch.f b → Expandable B T.ghat b Cert.cs →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1)
    {z : ℕ} (hz1 : 1 ≤ z)
    (hz : potHead C Cert + ((z : ℝ) - 1) * potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ)) :
    ∃ L : CS.Link, z ≤ CS.count L := by
  obtain ⟨b, hout, hb⟩ := Cert.search_head Ch hζmax hentry ℓ
  have hspan := potSpan_nonneg C Cert
  have hzcast : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hY : (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) ≤ S.ρ := B.sum_Ico_le _ _
  have hYlam : Cert.lam * (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) / T.ghat
      ≤ Cert.lam * S.ρ / T.ghat := by
    rw [div_le_div_iff_of_pos_right T.ghat_pos]
    nlinarith [Cert.one_le_lam, Finset.sum_nonneg
      (fun d (_ : d ∈ Finset.Ico 0 (b + 1)) => B.spend_nonneg d)]
  have hblt : b < ℓ := by
    by_contra hcon
    push Not at hcon
    have : (ℓ : ℝ) ≤ (b : ℝ) := by exact_mod_cast hcon
    nlinarith
  rcases hout with hpast | ⟨hfert, hexp⟩
  · omega
  obtain ⟨L0, hdepth0, hcount0⟩ := restart b hblt hfert hexp
  have hfit : (CS.depth L0 : ℝ) + ((z - 1 : ℕ) : ℝ) * potSpan C Cert
      + Cert.lam * (S.ρ - ∑ d ∈ Finset.Ico 0 (CS.depth L0 + 1), B.spend d) / T.ghat
        < (ℓ : ℝ) := by
    have hsub : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
      rw [Nat.cast_sub hz1]; norm_num
    have hdiv : Cert.lam * (S.ρ - ∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) / T.ghat
        = Cert.lam * S.ρ / T.ghat
          - Cert.lam * (∑ d ∈ Finset.Ico 0 (b + 1), B.spend d) / T.ghat := by
      field_simp
    rw [hdepth0, hsub, hdiv]
    linarith
  obtain ⟨L, hcount, _, _⟩ := potential_links Cert CS hfloor hmax L0 (z - 1) hfit
  exact ⟨L, by omega⟩


end ChainSystem

end LedgerCert

end ProofOfSpace

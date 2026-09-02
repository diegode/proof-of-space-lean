/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungFilecoin

/-!
# The Chung-8 latency bound over the certified parameter window

`ChungFilecoin.lean` runs the potential ledger at one parameter tuple.  Nothing in the
curve analysis depends on the black budget `ρ`, the challenge weight `ζ_δ`, or the source
weight `σ`: `Setting` constrains `ρ` and `ζ_δ` only by `ρ ≥ 0`, and `σ` enters the
tracking constants only through `ĝ = min{g_π, gain_δ(σ)/2}` and `π̂ = min{π̄, σ, 1-β(σ)}`,
both of which are *constant* on the window

    `0.1184 ≤ σ ≤ 0.6`,

because `gain_δ(σ) ≥ 2 g_π` holds there by concavity between the two certified endpoints.

So the whole ledger — chain, certificate, and the prices it feeds `latency_potential` —
is available with `ρ`, `ζ_δ` and `σ` left symbolic, and the level threshold becomes an
inequality one can evaluate at other parameters:

    `(0.43 + 6.46·(0.89 - ζ_δ)_+) + (z - 1) · 3.822 + 11.87 · ρ < ℓ`.

The first term is the initial search: `refPot` climbs at the top-bucket rate `6.46` per
unit of weight, so a thinner challenge set pays for itself here rather than being ruled
out by a hypothesis.  At the Filecoin point its left side is `13.928 < 14`; at `ρ = 7/10`
two links fit in `ℓ = 13`, and a challenge weight of `0.75` with half the space fits two
links in `ℓ = 12`.
-/

namespace ProofOfSpace
namespace ChungCurve

open Set

variable {ρ ζδ σ : ℝ}

/-! ### The setting with a symbolic budget and challenge weight -/

/-- The Chung-8 setting with the black budget `ρ` and the adjusted challenge weight `ζ_δ`
left symbolic.  Every analytic field is inherited unchanged: no `Setting` axiom mentions
either parameter. -/
noncomputable def chung8SettingAt (ρ ζδ : ℝ) (hρ : 0 ≤ ρ) : Setting :=
  { chung8Setting with ρ := ρ, ζδ := ζδ, ρ_nonneg := hρ }

@[simp] theorem chung8SettingAt_β {hρ : 0 ≤ ρ} : (chung8SettingAt ρ ζδ hρ).β = chungBeta8 := rfl

@[simp] theorem chung8SettingAt_delta {hρ : 0 ≤ ρ} :
    (chung8SettingAt ρ ζδ hρ).δ = (189 : ℝ) / 5000 := rfl

@[simp] theorem chung8SettingAt_pi {hρ : 0 ≤ ρ} : (chung8SettingAt ρ ζδ hρ).pi = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8SettingAt_rho {hρ : 0 ≤ ρ} : (chung8SettingAt ρ ζδ hρ).ρ = ρ := rfl

@[simp] theorem chung8SettingAt_zetaDelta {hρ : 0 ≤ ρ} : (chung8SettingAt ρ ζδ hρ).ζδ = ζδ := rfl

@[simp] theorem chung8SettingAt_alphaMax {hρ : 0 ≤ ρ} :
    (chung8SettingAt ρ ζδ hρ).αmax = filecoinAlphaMax := rfl

theorem chung8SettingAt_gpi {hρ : 0 ≤ ρ} : (chung8SettingAt ρ ζδ hρ).gpi = gpi8 := rfl

theorem chung8SettingAt_gainD {hρ : 0 ≤ ρ} (t : ℝ) :
    (chung8SettingAt ρ ζδ hρ).gainD t = gainD8 t := rfl

/-- `π̄ = 1 - β(π) = 0.05089`, exactly. -/
theorem chung8SettingAt_piBar {hρ : 0 ≤ ρ} :
    (chung8SettingAt ρ ζδ hρ).piBar = (5089 : ℝ) / 100000 := by
  simp only [Setting.piBar, chung8SettingAt_β, chung8SettingAt_pi, beta8_pi_eq]
  norm_num

/-- `β_δ(π) = 0.91131`, exactly. -/
theorem chung8SettingAt_betaD_pi {hρ : 0 ≤ ρ} :
    (chung8SettingAt ρ ζδ hρ).betaD ((4 : ℝ) / 5) = (91131 : ℝ) / 100000 := by
  simp only [Setting.betaD, chung8SettingAt_β, chung8SettingAt_delta, beta8_pi_eq]
  norm_num

@[simp] theorem chung8SettingAt_alphaMin {hρ : 0 ≤ ρ} :
    (chung8SettingAt ρ ζδ hρ).αmin = filecoinAlphaMin := rfl

/-! ### The source window

`gain_δ(σ) ≥ 2 g_π` is certified at `σ = 0.1184` and at `σ̃ = 0.6`; concavity carries it
across the whole segment between them.  That is the only place `σ` touches the analysis,
so every constant below is the one `ChungFilecoin.lean` computes. -/

/-- **The source condition on the whole window `[0.1184, 0.6]`.** -/
theorem chung8_condB_window {hρ : 0 ≤ ρ} (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    2 * (chung8SettingAt ρ ζδ hρ).gpi ≤ (chung8SettingAt ρ ζδ hρ).gainD σ := by
  have hlo : 2 * (chung8SettingAt ρ ζδ hρ).gpi
      ≤ (chung8SettingAt ρ ζδ hρ).gainD ((74 : ℝ) / 625) := by
    rw [chung8SettingAt_gpi, chung8SettingAt_gainD]
    exact condB_holds_at_1184
  have hhi : 2 * (chung8SettingAt ρ ζδ hρ).gpi
      ≤ (chung8SettingAt ρ ζδ hρ).gainD ((3 : ℝ) / 5) := by
    rw [chung8SettingAt_gpi, chung8SettingAt_gainD]
    exact two_gpi_le_gainD8_06
  have hmin := (chung8SettingAt ρ ζδ hρ).gainD_concaveOn.min_le_of_mem_Icc
    (x := (74 : ℝ) / 625) (y := (3 : ℝ) / 5) (by norm_num) (by norm_num) ⟨h1, h2⟩
  exact le_trans (le_min hlo hhi) hmin

/-! ### Tracking, chain and certificate at a symbolic source weight -/

/-- The tracked source at any weight of the certified window. -/
noncomputable def chung8TrackingAt (hρ : 0 ≤ ρ)
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    Tracking (chung8SettingAt ρ ζδ hρ) where
  σ := σ
  σ_gt := by
    have : (chung8SettingAt ρ ζδ hρ).αmin < (74 : ℝ) / 625 := by
      rw [chung8SettingAt_alphaMin, filecoinAlphaMin]; norm_num
    linarith
  σ_lt := by rw [chung8SettingAt_pi]; linarith
  mid := 3 / 5
  mid_ge := h2
  mid_le := by rw [chung8SettingAt_pi]; norm_num
  mid_gain := by
    have hmin : min (chung8SettingAt ρ ζδ hρ).gpi
        ((chung8SettingAt ρ ζδ hρ).gainD σ / 2) ≤ (chung8SettingAt ρ ζδ hρ).gpi :=
      min_le_left _ _
    have hcert : 2 * (chung8SettingAt ρ ζδ hρ).gpi
        ≤ (chung8SettingAt ρ ζδ hρ).gainD (3 / 5) := by
      rw [chung8SettingAt_gpi, chung8SettingAt_gainD]
      exact two_gpi_le_gainD8_06
    linarith

@[simp] theorem chung8TrackingAt_sigma {hρ : 0 ≤ ρ}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).σ = σ := rfl

/-- `ĝ = g_π` throughout the window. -/
theorem chung8TrackingAt_ghat {hρ : 0 ≤ ρ} (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).ghat = gpi8 := by
  rw [(chung8TrackingAt (ζδ := ζδ) hρ h1 h2).ghat_eq_gpi
    (chung8_condB_window h1 h2), chung8SettingAt_gpi]

/-- `π̂ = π̄ = x₀` throughout the window. -/
theorem chung8TrackingAt_lam {hρ : 0 ≤ ρ} (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).lam = chainX 0 := by
  rw [(chung8TrackingAt (ζδ := ζδ) hρ h1 h2).lam_eq_piBar (chung8_condB_window h1 h2)]
  simp only [Setting.piBar, chung8SettingAt_β, chung8SettingAt_pi, chainX_zero]

/-- **The reference chain, at any budget, challenge weight and source weight of the
window.**  The chain points are those of `ChungFilecoin.lean`: the tracking constants they
are certified against, `ĝ` and `π̂`, do not move. -/
noncomputable def chung8RefChainAt (hρ : 0 ≤ ρ)
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    RefChain (chung8SettingAt ρ ζδ hρ) (chung8TrackingAt hρ h1 h2) where
  m := 4
  x := chainX
  m_pos := by norm_num
  base := by rw [chung8TrackingAt_lam]
  width := by
    intro k hk
    have h := chung8RefChain.width k hk
    rw [chung8_ghat_eq] at h
    rw [chung8TrackingAt_ghat]
    exact h
  step := chung8RefChain.step
  mem := chung8RefChain.mem
  top := chung8RefChain.top

@[simp] theorem chung8RefChainAt_x {hρ : 0 ≤ ρ} (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).x = chainX := rfl

@[simp] theorem chung8RefChainAt_m {hρ : 0 ≤ ρ} (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).m = 4 := rfl

/-- **The ledger certificate, at any budget of the window.**  Its blocked-range clauses
quantify over spends bounded by `ρ`, so a smaller budget only weakens them. -/
noncomputable def chung8LedgerCertAt (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 4 / 5)
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    LedgerCert (chung8SettingAt ρ ζδ hρ) (chung8TrackingAt hρ h1 h2)
      (chung8RefChainAt hρ h1 h2) where
  lam := 33 / 25
  loss := 331 / 774
  cs := 8 / 5
  wtop := 387 / 2500
  kappa := 447 / 10000
  a2 := 819 / 200
  b2 := 91 / 500
  one_le_lam := by norm_num
  loss_nonneg := by norm_num
  one_le_cs := by norm_num
  wtop_pos := by norm_num
  kappa_nonneg := by norm_num
  loss_ge := chung8LedgerCert.loss_ge
  topLip := chung8LedgerCert.topLip
  chord := chung8LedgerCert.chord
  ghat_le_lam_wtop := by
    rw [chung8TrackingAt_ghat, gpi8_eq]; norm_num
  inf_rate := by
    intro θ s hθ0 hθloss hs hspend
    rw [chung8TrackingAt_ghat, gpi8_eq]
    have h := chung8LedgerCert.inf_rate θ s hθ0 hθloss hs hspend
    rw [chung8_ghat_eq, gpi8_eq] at h
    exact h
  blockDrop := by
    intro x hx hxρ
    rw [chung8TrackingAt_ghat] at hx
    have h := chung8LedgerCert.blockDrop x (by rw [chung8_ghat_eq]; exact hx)
      (by rw [chung8Setting_rho]; rw [chung8SettingAt_rho] at hxρ; linarith)
    exact h
  blockDrop_one := by
    intro x hx
    rw [chung8TrackingAt_ghat] at hx
    exact chung8LedgerCert.blockDrop_one x (by rw [chung8_ghat_eq]; exact hx)
  blk_rate := by
    intro x y hx hxρ hy
    rw [chung8TrackingAt_ghat] at hx ⊢
    have h := chung8LedgerCert.blk_rate x y (by rw [chung8_ghat_eq]; exact hx)
      (by rw [chung8Setting_rho]; rw [chung8SettingAt_rho] at hxρ; linarith) hy
    rw [chung8_ghat_eq] at h
    exact h

@[simp] theorem chung8LedgerCertAt_lam {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).lam = 33 / 25 := rfl

@[simp] theorem chung8LedgerCertAt_loss {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).loss = 331 / 774 := rfl

@[simp] theorem chung8LedgerCertAt_cs {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).cs = 8 / 5 := rfl

/-! ### The three prices of the ledger

`potHead` and `potSpan` are decreasing in the challenge and source weights, so on the
window they are bounded by their values at the low ends, and the budget charge is linear
in `ρ`.  Rounded upwards, the prices are `0.6`, `3.822` and `11.87 ρ`. -/

/-- **The search price as a function of the challenge weight.**  `potHead` is
`m - refPot(ζ_δ) + loss`, and `refPot` climbs at the top-bucket rate `1/0.1548 = 6.46`
per unit of weight up to the chain top, so a challenge weight `w` below `0.89` pays
`6.46` levels per unit it is missing, and above it pays only the saturation allowance.
Unlike a constant head this leaves `ζ` free: it is what lets the theorem answer what a
thinner challenge set costs. -/
theorem chung8_searchCost_le {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    LedgerCert.potHead (chung8RefChainAt (ζδ := ζδ) hρ h1 h2)
      (chung8LedgerCertAt hρ hρmax h1 h2)
      ≤ 43 / 100 + 646 / 100 * max 0 (89 / 100 - ζδ) := by
  have hmax : (89 : ℝ) / 100 - ζδ ≤ max 0 (89 / 100 - ζδ) := le_max_right _ _
  have hmax0 : (0 : ℝ) ≤ max 0 (89 / 100 - ζδ) := le_max_left _ _
  simp only [LedgerCert.potHead, chung8SettingAt_zetaDelta, chung8RefChainAt_m,
    chung8LedgerCertAt_loss]
  push_cast
  rcases le_total ζδ ((4443 : ℝ) / 5000) with hle | hge
  · have h : (4 : ℝ) - (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot ζδ
        ≤ (4443 / 5000 - ζδ) / (387 / 2500) := chainPot_topLip_le hle
    have hlin := (le_div_iff₀ (by norm_num : (0:ℝ) < 387 / 2500)).mp h
    linarith [hlin, hmax, hmax0]
  · have h : (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot ζδ = 4 := chainPot_sat hge
    rw [h]
    linarith

/-- The per-link span of the ledger: at most `3.822` levels, for every source weight of
the window. -/
theorem chung8_potSpan_le {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    LedgerCert.potSpan (chung8RefChainAt (ζδ := ζδ) hρ h1 h2)
      (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2) ≤ 1911 / 500 := by
  have hbase : (675 : ℝ) / 1113
      < (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot ((74 : ℝ) / 625) :=
    chainPot_sigma_gt
  have hmono : (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot ((74 : ℝ) / 625)
      ≤ (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot σ :=
    (chung8RefChainAt (ζδ := ζδ) hρ h1 h2).refPot_mono h1
  simp only [LedgerCert.potSpan, chung8TrackingAt_sigma, chung8RefChainAt_m,
    chung8LedgerCertAt_loss]
  push_cast
  linarith

/-- The budget charge of the ledger: `λ/ĝ ≤ 11.87` levels per unit of black weight. -/
theorem chung8_ledgerCharge_le {hρ : 0 ≤ ρ} {hρmax : ρ ≤ 4 / 5}
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) :
    (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).lam * (chung8SettingAt ρ ζδ hρ).ρ
        / (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).ghat ≤ 1187 / 100 * ρ := by
  rw [chung8LedgerCertAt_lam, chung8SettingAt_rho, chung8TrackingAt_ghat, gpi8_eq]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 11131 / 100000)]
  nlinarith [hρ]

/-! ### The latency bound over the window -/

/-- **The Chung-8 latency bound at any parameters of the certified window.**

The proof is `latency_potential` at the chain and certificate above; the only Filecoin
input is the window itself.  The level condition is the ledger's, with its three prices
rounded upwards, so it can be evaluated at other budgets and link counts directly. -/
theorem chung8_latency_window {V : Type u} {ℓ n z : ℕ}
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 4 / 5)
    (hζhi : ζδ ≤ (14155 : ℝ) / 14911)
    (hentry : (5089 : ℝ) / 100000 + ρ < ζδ)
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5)
    (hz1 : 1 ≤ z)
    (hlevels : 43 / 100 + 646 / 100 * max 0 (89 / 100 - ζδ)
      + ((z : ℝ) - 1) * (1911 / 500) + 1187 / 100 * ρ < (ℓ : ℝ))
    (G : Concrete.LayeredGraph V (chung8SettingAt ρ ζδ hρ) ℓ n)
    (P : Concrete.Pebbling G) (hn : 0 < n)
    (hσαpi : σ < G.αpi) (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0) (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A (latencyLength G.αpi σ n z) := by
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hσapi : (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).σ < G.αpi := by
    rw [chung8TrackingAt_sigma]; exact hσαpi
  have hζmax : (chung8SettingAt ρ ζδ hρ).ζδ ≤ (chung8SettingAt ρ ζδ hρ).αmax := by
    rw [chung8SettingAt_zetaDelta, chung8SettingAt_alphaMax, filecoinAlphaMax]
    linarith
  have hentry' : (chung8SettingAt ρ ζδ hρ).piBar
      < (chung8SettingAt ρ ζδ hρ).ζδ - (chung8SettingAt ρ ζδ hρ).ρ := by
    rw [chung8SettingAt_piBar, chung8SettingAt_zetaDelta, chung8SettingAt_rho]
    exact lt_sub_iff_add_lt.mpr hentry
  have hnobreak : (chung8SettingAt ρ ζδ hρ).ρ
      < (chung8SettingAt ρ ζδ hρ).betaD (chung8SettingAt ρ ζδ hρ).pi
        - (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).lam := by
    rw [chung8SettingAt_rho, chung8SettingAt_pi, chung8SettingAt_betaD_pi,
      chung8TrackingAt_lam, chainX_zero_eq]
    linarith
  have hslack : (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).lam
      + ((chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).cs - 1)
        * (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).ghat
      ≤ (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).σ := by
    rw [chung8TrackingAt_lam, chainX_zero_eq, chung8TrackingAt_ghat, gpi8_eq,
      chung8TrackingAt_sigma, chung8LedgerCertAt_cs]
    linarith
  have hz : LedgerCert.potHead (chung8RefChainAt (ζδ := ζδ) hρ h1 h2)
        (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2)
      + ((z : ℝ) - 1) * LedgerCert.potSpan (chung8RefChainAt (ζδ := ζδ) hρ h1 h2)
        (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2)
      + (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2).lam * (chung8SettingAt ρ ζδ hρ).ρ
        / (chung8TrackingAt (ζδ := ζδ) hρ h1 h2).ghat < (ℓ : ℝ) := by
    have hhead := chung8_searchCost_le (ζδ := ζδ) (hρ := hρ) (hρmax := hρmax) h1 h2
    have hspan := chung8_potSpan_le (ζδ := ζδ) (hρ := hρ) (hρmax := hρmax) h1 h2
    have hcharge := chung8_ledgerCharge_le (ζδ := ζδ) (hρ := hρ) (hρmax := hρmax) h1 h2
    have hspan' : ((z : ℝ) - 1)
        * LedgerCert.potSpan (chung8RefChainAt (ζδ := ζδ) hρ h1 h2)
          (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2)
        ≤ ((z : ℝ) - 1) * (1911 / 500) :=
      mul_le_mul_of_nonneg_left hspan (by linarith)
    linarith
  have h := latency_potential G P (chung8TrackingAt hρ h1 h2)
    (chung8LedgerCertAt (ζδ := ζδ) hρ hρmax h1 h2) hn hσapi hDepth hζmax hentry'
    hnobreak hslack hz1 hz A hA hred (by rw [chung8SettingAt_zetaDelta]; exact hweight)
  rwa [chung8TrackingAt_sigma] at h

/-! ### Reading the level condition

`(0.43 + 6.46·(0.89 - ζ_δ)_+) + (z - 1)·3.822 + 11.87·ρ < ℓ` is the whole trade-off: the
initial search costs `6.46` layers per unit of missing challenge weight, each chain link
past the first costs `3.822`, and each unit of black weight costs `11.87`.  Five points,
checked by `norm_num`. -/

/-- Two links at the Filecoin parameters need fourteen layers: `13.928 < 14`. -/
example : 43 / 100 + 646 / 100 * max 0 (89 / 100 - (4311 : ℝ) / 5000)
    + (2 - 1) * (1911 / 500) + 1187 / 100 * (4 / 5) < 14 := by
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 89 / 100 - (4311 : ℝ) / 5000)]; norm_num

/-- Taking a tenth of the space back buys a layer: at `ρ = 0.7`, `12.741 < 13`. -/
example : 43 / 100 + 646 / 100 * max 0 (89 / 100 - (4311 : ℝ) / 5000)
    + (2 - 1) * (1911 / 500) + 1187 / 100 * (7 / 10) < 13 := by
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 89 / 100 - (4311 : ℝ) / 5000)]; norm_num

/-- A thinner challenge set is paid for by the search, not forbidden: challenge weight
`0.75` against half the space still gives two links in twelve layers, `11.336 < 12`. -/
example : 43 / 100 + 646 / 100 * max 0 (89 / 100 - ((3 : ℝ) / 4 - 189 / 5000))
    + (2 - 1) * (1911 / 500) + 1187 / 100 * (1 / 2) < 12 := by
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 89 / 100 - ((3 : ℝ) / 4 - 189 / 5000))]
  norm_num

/-- A third link at the Filecoin budget needs eighteen layers: `17.750 < 18`. -/
example : 43 / 100 + 646 / 100 * max 0 (89 / 100 - (4311 : ℝ) / 5000)
    + (3 - 1) * (1911 / 500) + 1187 / 100 * (4 / 5) < 18 := by
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 89 / 100 - (4311 : ℝ) / 5000)]; norm_num

/-- Asymptotically one link per `3.822` layers: six links at `ℓ = 30`. -/
example : 43 / 100 + 646 / 100 * max 0 (89 / 100 - (4311 : ℝ) / 5000)
    + (6 - 1) * (1911 / 500) + 1187 / 100 * (4 / 5) < 30 := by
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 89 / 100 - (4311 : ℝ) / 5000)]; norm_num


end ChungCurve
end ProofOfSpace

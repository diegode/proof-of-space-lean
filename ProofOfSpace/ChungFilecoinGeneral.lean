/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungFilecoin

/-!
# The Chung-8 ledger at a symbolic budget, challenge weight and source weight

`ChungFilecoin.lean` builds the reference chain and its certificate at one parameter
tuple.  Nothing in that construction depends on the black budget `ρ` or the challenge
weight `ζ_δ` — no `Setting` axiom mentions either — and `σ` reaches it only through the
tracking constants `ĝ = min{g_π, gain_δ(σ)/2}` and `π̂ = min{π̄, σ, 1-β(σ)}`, which are
*constant* on the window

    `0.1184 ≤ σ ≤ 0.6`,

because `gain_δ(σ) ≥ 2 g_π` holds there by concavity between the two certified endpoints.

So the chain and the certificate are available with all three left symbolic, which is what
lets `Solution.lean` expose a level budget for the public statement at any source weight
of the window rather than at one point.
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

end ChungCurve
end ProofOfSpace

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungFilecoin

/-!
# The raised-threshold Chung-8 certificate

`FullSources.lean` buys a whole `α_π n` per chain link instead of `(α_π - σ) n`, at the
price of depth robustness at `S.pi - T.σ` rather than at `S.pi`.  `ChungFilecoin.lean`
pays that price by lowering the robustness threshold from `4/5` to `0.6816`, which changes
the graph assumption.  This file pays it the other way, and keeps `4/5`: the *fertility*
threshold is raised to

  `π' = 4443/5000 = 0.8886`,   `σ' = 443/5000 = 0.0886`,

so that `π' - σ' = 4/5` exactly.  A footprint of weight `π'` then contains `σ' n` nodes
that each begin a whole `α_π n` path, using nothing but depth robustness at the Filecoin
threshold `4/5`.

## The mirrored chain

Raising `π` moves everything the ledger prices, so the whole certificate is rebuilt.  What
makes that cheap is the reversal symmetry `β(1 - β x) = 1 - x` of the polygon: the `β_δ`
orbit of the new tracking floor `π̄' = 1 - β(π')` is the old chain's list of `β`-values
read backwards, and every one of its points is already a certified breakpoint.

| `k`    | 0            | 1        | 2        | 3         | 4     | 5         |
|--------|--------------|----------|----------|-----------|-------|-----------|
| `x k`  | `0.02834573` | `0.0736` | `0.2284` | `0.5337`  | `0.8` | `0.91131` |

`π' = 0.8886` sits in the top bucket, and `x 5 = β_δ(4/5)` is the same
`91131/100000` the fourteen-layer analysis already uses.  As in `ChungFilecoin.lean` the
first bucket is exactly `ĝ` wide — here `ĝ = g_{π'} = 0.04525427` — which is where the
modulus certificate is tight.

## What it costs

`g_{π'} = 0.04525` against `g_π = 0.11131`, so the ledger's charge for the whole black
budget rises from `9.49` layers to `19.89`, and the per-link span from `3.8212` to
`4.6991`.  Against that, the payoff per link rises from `0.0816 n` to `0.2 n`, so the
certified slope goes from `0.02135` to `0.04256` — nearly double, at the Filecoin
robustness parameters unchanged.
-/

namespace ProofOfSpace
namespace ChungCurve

open Set

/-! ### The raised-threshold setting and tracking -/

/-- The Chung-8 setting at the raised fertility threshold `π' = 0.8886`.  Only `pi`
differs from `chung8Setting`; `β`, `δ`, `ρ` and `ζ_δ` are the Filecoin values. -/
noncomputable def chung8SettingHi : Setting where
  β := chungBeta8
  αg := filecoinAlphaG
  δ := 189 / 5000
  pi := 4443 / 5000
  ρ := 4 / 5
  ζδ := 4311 / 5000
  αmin := FiniteSizeProfile.αmin
  αmax := FiniteSizeProfile.αmax
  β_maps := fun _ hx => chungBeta8_maps hx
  β_zero := chungBeta8_zero
  β_strictMonoOn := chungBeta8_strictMonoOn
  β_concaveOn := filecoinBeta_concaveOn
  β_expands := fun _ hx => chungBeta8_expands hx
  β_reversal := fun _ hx => chungBeta8_reversal hx
  αg_mem := filecoinAlphaG_mem
  αg_max := fun _ hx hne => filecoinAlphaG_max hx hne
  δ_nonneg := by norm_num
  ρ_nonneg := by norm_num
  pi_mem := by norm_num
  αg_lt_pi := by norm_num [filecoinAlphaG]
  gpi_pos := by norm_num [chungBeta8]
  αmin_mem := FiniteSizeProfile.αmin_mem
  αmax_mem := FiniteSizeProfile.αmax_mem
  gainD_αmin := FiniteSizeProfile.gainD_αmin
  gainD_αmax := FiniteSizeProfile.gainD_αmax

@[simp] theorem chung8SettingHi_β : chung8SettingHi.β = chungBeta8 := rfl

@[simp] theorem chung8SettingHi_pi : chung8SettingHi.pi = (4443 : ℝ) / 5000 := rfl

@[simp] theorem chung8SettingHi_rho : chung8SettingHi.ρ = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8SettingHi_delta : chung8SettingHi.δ = (189 : ℝ) / 5000 := rfl

@[simp] theorem chung8SettingHi_zetaDelta :
    chung8SettingHi.ζδ = (4311 : ℝ) / 5000 := rfl

/-- `g_{π'} = 0.04525427`, the gain at the raised threshold. -/
theorem chung8Hi_gpi : chung8SettingHi.gpi = 4525427 / 100000000 := by
  norm_num [Setting.gpi, Setting.gainD, chung8SettingHi, chungBeta8]

/-- `π̄' = 1 - β(π') = 0.02834573`, the head of the mirrored chain. -/
theorem chung8Hi_piBar : chung8SettingHi.piBar = 2834573 / 100000000 := by
  norm_num [Setting.piBar, chung8SettingHi, chungBeta8]

/-- `β_δ(π') = 0.93385427`: one free level from the raised threshold. -/
theorem chung8Hi_betaD_pi :
    chung8SettingHi.betaD (4443 / 5000) = 93385427 / 100000000 := by
  norm_num [Setting.betaD, chung8SettingHi, chungBeta8]

/-- The tracked source weight at the raised threshold.  `σ' = π' - 4/5` exactly: it is
the surplus the full-length path-source lemma converts into sources. -/
noncomputable def chung8TrackingHi : Tracking chung8SettingHi where
  σ := 443 / 5000
  σ_gt := by norm_num [chung8SettingHi, FiniteSizeProfile.αmin, filecoinAlphaMin]
  σ_lt := by norm_num [chung8SettingHi]
  mid := 3 / 5
  mid_ge := by norm_num
  mid_le := by norm_num [chung8SettingHi]
  mid_gain := by
    refine le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) ?_
    rw [chung8Hi_gpi]
    have h2 : chung8SettingHi.gainD (3 / 5) = 1171517 / 1345000 - 189 / 5000 - 3 / 5 := by
      norm_num [Setting.gainD, chung8SettingHi, chungBeta8]
    rw [h2]; norm_num

@[simp] theorem chung8TrackingHi_sigma : chung8TrackingHi.σ = (443 : ℝ) / 5000 := rfl

/-- `ĝ' = g_{π'}`: the source gain is more than twice the fertile gain, so the tracking
gain is the fertile one. -/
theorem chung8Hi_ghat : chung8TrackingHi.ghat = 4525427 / 100000000 := by
  rw [Tracking.ghat, chung8Hi_gpi, min_eq_left]
  have h : chung8SettingHi.gainD chung8TrackingHi.σ = 1590633 / 8960000 := by
    norm_num [Setting.gainD, chung8SettingHi, chung8TrackingHi, chungBeta8]
  rw [h]; norm_num

/-- `π̂' = π̄'`: the floor is the mirror weight, as at the Filecoin threshold. -/
theorem chung8Hi_lam : chung8TrackingHi.lam = 2834573 / 100000000 := by
  rw [Tracking.lam, chung8Hi_piBar, min_eq_left]
  rw [Tracking.sigmaHat, le_min_iff]
  constructor
  · norm_num [chung8TrackingHi]
  · have h : chung8SettingHi.β chung8TrackingHi.σ = 2723177 / 8960000 := by
      norm_num [chung8SettingHi, chung8TrackingHi, chungBeta8]
    rw [h]; norm_num

/-! ### The scalar side conditions -/

theorem chung8Hi_entry : chung8SettingHi.piBar < chung8SettingHi.ζδ - chung8SettingHi.ρ := by
  rw [chung8Hi_piBar]; norm_num [chung8SettingHi]

theorem chung8Hi_zeta_le : chung8SettingHi.ζδ ≤ chung8SettingHi.αmax := by
  norm_num [chung8SettingHi, FiniteSizeProfile.αmax, filecoinAlphaMax]

theorem chung8Hi_nobreak :
    chung8SettingHi.ρ < chung8SettingHi.betaD chung8SettingHi.pi - chung8TrackingHi.lam := by
  rw [chung8SettingHi_pi, chung8Hi_betaD_pi, chung8Hi_lam]
  norm_num [chung8SettingHi]

/-! ### The mirrored reference chain -/

/-- The chain points: the `β_δ` orbit of `π̄' = 1 - β(0.8886)`.  Every point is a
breakpoint of the certified polygon, read backwards. -/
noncomputable def chainXHi : ℕ → ℝ
  | 0 => 2834573 / 100000000
  | 1 => 46 / 625
  | 2 => 571 / 2500
  | 3 => 5337 / 10000
  | 4 => 4 / 5
  | _ => 91131 / 100000

@[simp] theorem chainXHi_zero : chainXHi 0 = 2834573 / 100000000 := rfl
@[simp] theorem chainXHi_one : chainXHi 1 = 46 / 625 := rfl
@[simp] theorem chainXHi_two : chainXHi 2 = 571 / 2500 := rfl
@[simp] theorem chainXHi_three : chainXHi 3 = 5337 / 10000 := rfl
@[simp] theorem chainXHi_four : chainXHi 4 = 4 / 5 := rfl
@[simp] theorem chainXHi_five : chainXHi 5 = 91131 / 100000 := rfl

/-- Every step of the mirrored chain is a *whole* free level, with no rounding: the
polygon's reversal symmetry makes `β_δ` map each breakpoint exactly onto the next. -/
theorem chainXHi_step_eq :
    ∀ k, k < 5 → chainXHi (k + 1) = chung8SettingHi.betaD (chainXHi k) := by
  intro k hk
  interval_cases k <;>
    norm_num [Setting.betaD, chung8SettingHi, chungBeta8, chainXHi]

noncomputable def chung8RefChainHi : RefChain chung8SettingHi chung8TrackingHi where
  m := 5
  x := chainXHi
  m_pos := by norm_num
  base := by rw [chung8Hi_lam]; norm_num
  width := by
    intro k hk
    have hg : chung8TrackingHi.ghat = 4525427 / 100000000 := chung8Hi_ghat
    rw [hg]
    interval_cases k <;> norm_num [chainXHi]
  step := fun k hk => le_of_eq (chainXHi_step_eq k hk)
  mem := by intro k hk; interval_cases k <;> norm_num [chainXHi]
  top := by rw [chung8SettingHi_pi]; norm_num [chainXHi]

@[simp] theorem chung8RefChainHi_m : chung8RefChainHi.m = 5 := rfl

@[simp] theorem chung8RefChainHi_x : chung8RefChainHi.x = chainXHi := rfl

/-! ### The potential, bucket by bucket

`refPot` is affine on each bucket, so every certificate below is a finite case analysis
on which bucket a weight lies in. -/

theorem chainPotHi_b0 {t : ℝ}
    (h1 : (2834573 : ℝ) / 100000000 ≤ t) (h2 : t ≤ (46 : ℝ) / 625) :
    chung8RefChainHi.refPot t = (t - 2834573 / 100000000) / (4525427 / 100000000) := by
  have h := chung8RefChainHi.refPot_eq_of_mem (j := 0) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]; norm_num

theorem chainPotHi_b1 {t : ℝ}
    (h1 : (46 : ℝ) / 625 ≤ t) (h2 : t ≤ (571 : ℝ) / 2500) :
    chung8RefChainHi.refPot t = 1 + (t - 46 / 625) / (387 / 2500) := by
  have h := chung8RefChainHi.refPot_eq_of_mem (j := 1) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]; norm_num

theorem chainPotHi_b2 {t : ℝ}
    (h1 : (571 : ℝ) / 2500 ≤ t) (h2 : t ≤ (5337 : ℝ) / 10000) :
    chung8RefChainHi.refPot t = 2 + (t - 571 / 2500) / (3053 / 10000) := by
  have h := chung8RefChainHi.refPot_eq_of_mem (j := 2) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]; norm_num

theorem chainPotHi_b3 {t : ℝ}
    (h1 : (5337 : ℝ) / 10000 ≤ t) (h2 : t ≤ (4 : ℝ) / 5) :
    chung8RefChainHi.refPot t = 3 + (t - 5337 / 10000) / (2663 / 10000) := by
  have h := chung8RefChainHi.refPot_eq_of_mem (j := 3) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]; norm_num

theorem chainPotHi_b4 {t : ℝ}
    (h1 : (4 : ℝ) / 5 ≤ t) (h2 : t ≤ (91131 : ℝ) / 100000) :
    chung8RefChainHi.refPot t = 4 + (t - 4 / 5) / (11131 / 100000) := by
  have h := chung8RefChainHi.refPot_eq_of_mem (j := 4) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]; norm_num

theorem chainPotHi_sat {t : ℝ} (h : (91131 : ℝ) / 100000 ≤ t) :
    chung8RefChainHi.refPot t = 5 := by
  have h' := chung8RefChainHi.refPot_eq_m (v := t) (by simpa using h)
  simpa using h'

/-- The saturation loss at the raised threshold: `π'` sits `0.79598` of the way up the
top bucket. -/
theorem chainPotHi_pi : chung8RefChainHi.refPot (4443 / 5000) = 4 + 8860 / 11131 := by
  rw [chainPotHi_b4 (by norm_num) (by norm_num)]; norm_num

/-- The source weight sits `25/258` of the way up the second bucket. -/
theorem chainPotHi_sigma : chung8RefChainHi.refPot (443 / 5000) = 1 + 25 / 258 := by
  rw [chainPotHi_b1 (by norm_num) (by norm_num)]; norm_num

/-- The red-free challenge weight sits `0.55879` of the way up the top bucket. -/
theorem chainPotHi_zeta : chung8RefChainHi.refPot (4311 / 5000) = 4 + 6220 / 11131 := by
  rw [chainPotHi_b4 (by norm_num) (by norm_num)]; norm_num

/-! ### The certificate inequalities -/

/-- **The top-bucket Lipschitz certificate.**  Measured down from `x₅`, the potential
falls at rate `1/(x₅ - x₄) = 8.98`; below the top bucket the wider buckets leave room. -/
theorem chainPotHi_topLip_le {v : ℝ} (hv : v ≤ (91131 : ℝ) / 100000) :
    (5 : ℝ) - chung8RefChainHi.refPot v ≤ (91131 / 100000 - v) / (11131 / 100000) := by
  rcases le_total ((4 : ℝ) / 5) v with h4 | h4
  · rw [chainPotHi_b4 h4 hv]; linarith
  rcases le_total ((5337 : ℝ) / 10000) v with h3 | h3
  · rw [chainPotHi_b3 h3 h4]; linarith
  rcases le_total ((571 : ℝ) / 2500) v with h2 | h2
  · rw [chainPotHi_b2 h2 h3]; linarith
  rcases le_total ((46 : ℝ) / 625) v with h1 | h1
  · rw [chainPotHi_b1 h1 h2]; linarith
  · have := chung8RefChainHi.refPot_nonneg v
    linarith

/-- **The blocked-range drop certificate.**  A blocked range below a fertile depth begins
with its own free level, so its endpoint is at least `β_δ(π') - y`; the potential it can
destroy is affine in its own spend, at slope `4` and offset `1/2`. -/
theorem chainPotHi_blockDrop {y : ℝ}
    (hlo : (1506967191 : ℝ) / 10000000000 ≤ y) (hhi : y ≤ 4 / 5) :
    (5 : ℝ) - chung8RefChainHi.refPot (93385427 / 100000000 - y) ≤ 4 * y + 1 / 2 := by
  rcases le_total ((5337 : ℝ) / 10000) (93385427 / 100000000 - y) with h3 | h3
  · rw [chainPotHi_b3 h3 (by linarith)]; linarith
  rcases le_total ((571 : ℝ) / 2500) (93385427 / 100000000 - y) with h2 | h2
  · rw [chainPotHi_b2 h2 h3]; linarith
  · rw [chainPotHi_b1 (by linarith) h2]; linarith

/--
**The raised-threshold ledger certificate**, at charge rate `λ = 9/8`, expandability
slack `cs = 2.33` and saturation loss `loss = 8860/11131 = 0.79598`.

`cs = 2.33` is what `π̂' = 0.02834573` leaves below `σ' = 0.0886`: the search may run at
`(i + 2.33) ĝ`, which shortens every blocked range by `1.33` of a level and is what keeps
`λ` down to `9/8`.  `blockDrop` is `chainPotHi_blockDrop`; `topLip` is
`chainPotHi_topLip_le`; `chord` is the polygon's top piece, whose slope `0.25445` beats
`κ / wtop = 0.254245`.
-/
noncomputable def chung8LedgerCertHi :
    LedgerCert chung8SettingHi chung8TrackingHi chung8RefChainHi where
  lam := 9 / 8
  loss := 8860 / 11131
  cs := 233 / 100
  wtop := 11131 / 100000
  kappa := 283 / 10000
  a2 := 4
  b2 := 1 / 2
  one_le_lam := by norm_num
  loss_nonneg := by norm_num
  one_le_cs := by norm_num
  wtop_pos := by norm_num
  kappa_nonneg := by norm_num
  loss_ge := by
    intro v _ hv
    rw [chung8SettingHi_pi] at hv
    have hm : ((chung8RefChainHi).m : ℝ) - 1 = 4 := by norm_num [chung8RefChainHi_m]
    rw [hm]
    have hmono : chung8RefChainHi.refPot v ≤ chung8RefChainHi.refPot (4443 / 5000) :=
      chung8RefChainHi.refPot_mono hv
    rw [chainPotHi_pi] at hmono
    linarith
  topLip := by
    intro u v hu hv
    have hu' : (91131 : ℝ) / 100000 ≤ u := by simpa using hu
    have hsat : chung8RefChainHi.refPot u = 5 := chainPotHi_sat hu'
    rcases le_total ((91131 : ℝ) / 100000) v with hv5 | hv5
    · rw [hsat, chainPotHi_sat hv5]
      have : (0 : ℝ) ≤ (u - v) / (11131 / 100000) := by positivity
      linarith
    · have hkey := chainPotHi_topLip_le hv5
      have hmono : (91131 / 100000 - v) / ((11131 : ℝ) / 100000)
          ≤ (u - v) / (11131 / 100000) := by
        rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
      rw [hsat]; linarith
  chord := by
    intro v hv4 hv
    rw [chung8SettingHi_pi] at hv
    have hv4' : (4 : ℝ) / 5 ≤ v := by simpa using hv4
    have hm : ((chung8RefChainHi).m : ℝ) - 1 = 4 := by norm_num [chung8RefChainHi_m]
    have hxm : chung8RefChainHi.x chung8RefChainHi.m = (91131 : ℝ) / 100000 := by
      simp [chung8RefChainHi_m]
    have hpot : chung8RefChainHi.refPot v - 4 = (100000 / 11131) * (v - 4 / 5) := by
      rw [chainPotHi_b4 hv4' (by linarith)]; ring
    have hbeta : chung8SettingHi.betaD v
        = 91131 / 100000 + 5089 / 20000 * (v - 4 / 5) := by
      have h : chung8SettingHi.β v = 94911 / 100000 + 5089 / 20000 * (v - 4 / 5) := by
        change filecoinBeta v = _
        exact filecoinBeta_top hv4' (by linarith)
      rw [Setting.betaD, h, chung8SettingHi_delta]; ring
    rw [hxm, hm, hpot, hbeta]
    linarith
  ghat_le_lam_wtop := by rw [chung8Hi_ghat]; norm_num
  inf_rate := by
    intro θ s hθ0 hθloss hs hspend
    rw [chung8Hi_ghat]
    have hxm : chung8RefChainHi.x chung8RefChainHi.m = (91131 : ℝ) / 100000 := by
      simp [chung8RefChainHi_m]
    rw [hxm, chung8SettingHi_pi] at hspend
    linarith
  blockDrop := by
    intro y hy hyρ
    rw [chung8SettingHi_rho] at hyρ
    rw [chung8Hi_ghat] at hy
    rw [chung8SettingHi_pi, chung8Hi_betaD_pi]
    have hm : ((chung8RefChainHi).m : ℝ) = 5 := by norm_num [chung8RefChainHi_m]
    rw [hm]
    exact chainPotHi_blockDrop (by linarith) hyρ
  blockDrop_one := by
    intro y hy
    rw [chung8Hi_ghat] at hy
    linarith
  blk_rate := by
    intro y w hy hyρ hw
    rw [chung8SettingHi_rho] at hyρ
    rw [chung8Hi_ghat] at hy ⊢
    linarith

@[simp] theorem chung8LedgerCertHi_lam : chung8LedgerCertHi.lam = 9 / 8 := rfl
@[simp] theorem chung8LedgerCertHi_loss : chung8LedgerCertHi.loss = 8860 / 11131 := rfl
@[simp] theorem chung8LedgerCertHi_cs : chung8LedgerCertHi.cs = 233 / 100 := rfl

/-! ### The three prices

The level condition is `potHead + (z-1) potSpan + λ ρ / ĝ < ℓ`, and at the raised
threshold each term evaluates exactly.  Against the fourteen-layer certificate the span
grows from `3.8212` to `4.6991` and the budget charge from `9.4870` to `19.8876`; the
payoff per link grows from `(α_π - σ) n = 0.0816 n` to `α_π n = 0.2 n`. -/

/-- `potSpan = 4.69908`: a fresh source of weight `σ' = 0.0886` starts `3.9031` levels
below saturation, and one saturation allowance `0.79598` is released at the fertile
depth. -/
theorem chung8Hi_potSpan_eq :
    LedgerCert.potSpan chung8RefChainHi chung8LedgerCertHi
      = 4 - 25 / 258 + 8860 / 11131 := by
  simp only [LedgerCert.potSpan, chung8LedgerCertHi_loss, chung8RefChainHi_m]
  rw [show (chung8TrackingHi).σ = (443 : ℝ) / 5000 from rfl, chainPotHi_sigma]
  push_cast
  ring

theorem chung8Hi_potSpan_pos :
    0 < LedgerCert.potSpan chung8RefChainHi chung8LedgerCertHi := by
  rw [chung8Hi_potSpan_eq]; norm_num

theorem chung8Hi_potSpan_lt :
    LedgerCert.potSpan chung8RefChainHi chung8LedgerCertHi < 4699076 / 1000000 := by
  rw [chung8Hi_potSpan_eq]; norm_num

/-- `potHead = 1.23718`: the potential the challenge footprint of weight `ζ_δ = 0.8622`
starts with, plus one saturation allowance. -/
theorem chung8Hi_potHead_eq :
    LedgerCert.potHead chung8RefChainHi chung8LedgerCertHi = 1 + 2640 / 11131 := by
  simp only [LedgerCert.potHead, chung8LedgerCertHi_loss, chung8RefChainHi_m]
  rw [show (chung8SettingHi).ζδ = (4311 : ℝ) / 5000 from rfl, chainPotHi_zeta]
  push_cast
  ring

/-- `λ ρ / ĝ = 19.88763`: the whole black budget, priced in layers.  This is where the
raised threshold is paid for — `ĝ` fell from `0.11131` to `0.04525`. -/
theorem chung8Hi_ledgerCharge_eq :
    chung8LedgerCertHi.lam * chung8SettingHi.ρ / chung8TrackingHi.ghat
      = 90000000 / 4525427 := by
  rw [chung8LedgerCertHi_lam, chung8SettingHi_rho, chung8Hi_ghat]
  norm_num

/-- The head of the asymptotic bound: the initial search plus the whole black budget,
`1.23718 + 19.88763 < 21.2` layers. -/
theorem chung8Hi_head_lt :
    LedgerCert.potHead chung8RefChainHi chung8LedgerCertHi
      + chung8LedgerCertHi.lam * chung8SettingHi.ρ / chung8TrackingHi.ghat < 106 / 5 := by
  rw [chung8Hi_potHead_eq, chung8Hi_ledgerCharge_eq]; norm_num

/-- The expandability slack the search runs at fits under the source weight, with
`0.08853391 ≤ 0.0886` to spare. -/
theorem chung8Hi_cs_slack :
    chung8TrackingHi.lam + (chung8LedgerCertHi.cs - 1) * chung8TrackingHi.ghat
      ≤ chung8TrackingHi.σ := by
  rw [chung8Hi_lam, chung8LedgerCertHi_cs, chung8Hi_ghat, chung8TrackingHi_sigma]
  norm_num

end ChungCurve
end ProofOfSpace

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungNumerics
import ProofOfSpace.Latency
import Mathlib.Analysis.Convex.Continuous

/-!
# The Chung-8 Filecoin specialization

This file instantiates the latency analysis with the rational degree-eight profile from
`ChungFilecoinCurve.lean`. Concavity, reversal, and the unique gain maximizer are proved
algebraically, so the specialization has no analytic typeclass assumption.

The last section exhibits the reference chain of `Potential.lean` for these parameters —
the `β_δ` orbit of the tracking floor, rationalized downwards — together with its
`LedgerCert`, and evaluates the potential ledger's constants. That is what
`chung8_latency_14_deterministic` runs on. The chain is data supplied here, not a hypothesis of
anything upstream.
-/

namespace ProofOfSpace
namespace ChungCurve

open Set

/-! ### Degree-eight finite-size profile -/

/-- The rational profile certified for the finite-size Filecoin calculation. -/
noncomputable def chungBeta8 (x : ℝ) : ℝ := filecoinBeta x

@[simp] theorem chungBeta8_zero : chungBeta8 0 = 0 := by
  simp [chungBeta8]

theorem chungBeta8_maps {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    chungBeta8 x ∈ Icc (0 : ℝ) 1 := by
  exact filecoinBeta_maps hx

theorem chungBeta8_expands {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < chungBeta8 x := by
  exact filecoinBeta_expands hx

theorem chungBeta8_reversal {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chungBeta8 (1 - chungBeta8 x) = 1 - x := by
  exact filecoinBeta_reversal hx

theorem chungBeta8_strictMonoOn :
    StrictMonoOn chungBeta8 (Icc (0 : ℝ) 1) := by
  exact filecoinBeta_strictMonoOn

namespace FiniteSizeProfile

/-- The adjusted gain before the `Setting` is packaged. -/
noncomputable def gd (x : ℝ) : ℝ := chungBeta8 x - 189 / 5000 - x

theorem gd_concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) gd := by
  have h : gd = chungBeta8 - fun x : ℝ => x + 189 / 5000 := by
    funext x
    simp only [gd, Pi.sub_apply]
    ring
  rw [h]
  exact filecoinBeta_concaveOn.sub (convexOn_add_const (convex_Icc 0 1) (189 / 5000))

noncomputable def αmin : ℝ := filecoinAlphaMin
noncomputable def αmax : ℝ := filecoinAlphaMax

theorem αmin_mem : αmin ∈ Icc (0 : ℝ) filecoinAlphaG := by
  norm_num [αmin, filecoinAlphaMin, filecoinAlphaG]

theorem αmax_mem : αmax ∈ Icc filecoinAlphaG 1 := by
  norm_num [αmax, filecoinAlphaMax, filecoinAlphaG]

theorem gainD_αmin : chungBeta8 αmin - (189 : ℝ) / 5000 - αmin = 0 := by
  change filecoinBeta filecoinAlphaMin - (189 : ℝ) / 5000 - filecoinAlphaMin = 0
  rw [filecoinBeta_alphaMin]
  norm_num [filecoinAlphaMin]

theorem gainD_αmax : chungBeta8 αmax - (189 : ℝ) / 5000 - αmax = 0 := by
  change filecoinBeta filecoinAlphaMax - (189 : ℝ) / 5000 - filecoinAlphaMax = 0
  rw [filecoinBeta_alphaMax]
  norm_num [filecoinAlphaMax]

end FiniteSizeProfile

/-- The exact gain maximizer lies below Filecoin's `π = 4/5`. -/
theorem chung8_αg_lt_pi : filecoinAlphaG < (4 : ℝ) / 5 := by
  norm_num [filecoinAlphaG]

/-! ### Exact Chung-8 `Setting` and Filecoin bundles -/

/-- The development's unconditional finite-size Chung-8 setting. -/
noncomputable def chung8Setting : Setting where
  β := chungBeta8
  αg := filecoinAlphaG
  δ := 189 / 5000
  pi := 4 / 5
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
  αg_lt_pi := chung8_αg_lt_pi
  gpi_pos := by norm_num [chungBeta8]
  αmin_mem := FiniteSizeProfile.αmin_mem
  αmax_mem := FiniteSizeProfile.αmax_mem
  gainD_αmin := FiniteSizeProfile.gainD_αmin
  gainD_αmax := FiniteSizeProfile.gainD_αmax

@[simp] theorem chung8Setting_β :
    chung8Setting.β = chungBeta8 := rfl


@[simp] theorem chung8Setting_delta :
    chung8Setting.δ = (189 : ℝ) / 5000 := rfl

@[simp] theorem chung8Setting_pi :
    chung8Setting.pi = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_rho :
    chung8Setting.ρ = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_zetaDelta :
    chung8Setting.ζδ = (4311 : ℝ) / 5000 := rfl

/-- The abstract `Setting.gpi` is exactly the `gpi8` computed from the constructed
degree-eight Chung threshold. -/
theorem chung8Setting_gpi :
    (chung8Setting).gpi = gpi8 := by
  rfl

/-- The abstract `Setting.gainD` at the mid-point `σ̃ = 3/5`, in terms of the
constructed degree-eight Chung threshold. -/
theorem chung8Setting_gainD_06 :
    (chung8Setting).gainD (3/5) = gainD8 (3/5) := by
  rfl

/-- Filecoin's tracked source weight for the Chung-8 setting. -/
noncomputable def chung8Tracking :
    Tracking (chung8Setting) where
  σ := 74 / 625
  σ_gt := by
    have hpositive : 0 < (chung8Setting).gainD ((74 : ℝ) / 625) := by
      norm_num [Setting.gainD, chungBeta8]
    by_contra hcon
    push Not at hcon
    have hnonpos := (chung8Setting).gainD_nonpos_of_le_αmin
      (by norm_num : (74 / 625 : ℝ) ∈ Icc 0 1) hcon
    linarith
  σ_lt := by norm_num
  mid := 3 / 5
  mid_ge := by norm_num
  mid_le := by norm_num
  mid_gain := by
    have hmin : min (chung8Setting).gpi ((chung8Setting).gainD (74 / 625) / 2)
        ≤ (chung8Setting).gpi := min_le_left _ _
    have hcert : 2 * (chung8Setting).gpi ≤ (chung8Setting).gainD (3 / 5) := by
      rw [chung8Setting_gainD_06, chung8Setting_gpi]
      exact two_gpi_le_gainD8_06
    linarith

@[simp] theorem chung8Tracking_sigma :
    (chung8Tracking).σ = (74 : ℝ) / 625 := rfl

/-! ### Scalar facts for the Filecoin parameters

These are the inequalities needed directly by the general and potential latency proofs. -/

/-- `π̄ < ζ_δ - ρ`: the challenge floor stays above the tracking floor. -/
theorem chung8_entry :
    (chung8Setting).piBar < (chung8Setting).ζδ - (chung8Setting).ρ := by
    norm_num [Setting.piBar, chungBeta8]

/-- `ζ_δ ≤ α_δ^max`: the challenge weight is inside the positive-gain interval. -/
theorem chung8_zeta_le :
    (chung8Setting).ζδ ≤ (chung8Setting).αmax := by
    norm_num [chung8Setting, FiniteSizeProfile.αmax, filecoinAlphaMax]

/-- `gain_δ(σ) ≥ 2 g_π` at `σ = 0.1184`, with `0.22268… ≥ 0.22262…` of little room. -/
theorem chung8_condB :
    2 * (chung8Setting).gpi ≤ (chung8Setting).gainD (chung8Tracking).σ := by
    simpa [Setting.gpi, Setting.gainD, chung8Setting, chung8Tracking,
      chungBeta8, gpi8, gainD8] using condB_holds_at_1184

/-- `ρ < β_δ(π) - π̄`: the whole budget cannot pay for one chain break. -/
theorem chung8_condC :
    (chung8Setting).ρ <
      (chung8Setting).pi + (chung8Setting).gpi - (chung8Setting).piBar := by
    norm_num [Setting.piBar, Setting.gpi, Setting.gainD, chungBeta8]

/-- The no-break condition `ρ < β_δ(π) - π̂` at the Filecoin parameters. -/
theorem chung8_nobreak :
    (chung8Setting).ρ
      < (chung8Setting).betaD (chung8Setting).pi - (chung8Tracking).lam := by
  have hb : (chung8Setting).betaD (chung8Setting).pi
      = (chung8Setting).pi + (chung8Setting).gpi := by
    simp only [Setting.betaD_eq]; rfl
  rw [(chung8Tracking).lam_eq_piBar (chung8_condB), hb]
  linarith [chung8_condC]

/-! ### The Chung-8 reference chain

`Potential.lean`'s reference chain for these parameters is the `β_δ` orbit of the
tracking floor `π̂ = π̄`, rationalized downwards so that every step is a `ChungNumerics`
bracket:

| `k` | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| `x k` | `π̄` | `0.1622` | `0.4285` | `0.7338` | `0.8886` |

The head of the chain is exact rather than numeric: the mirror law `β(π̄) = 1 - π` gives
`β_δ(x₀) = 1 - π - δ = 811/5000 = x₁` on the nose, and the same identity makes the first
bucket width `x₁ - x₀` equal to `g_π = ĝ` with no rounding at all.  That is what lets the
narrowest bucket be exactly `ĝ` wide, which is where the modulus certificate is tight.
-/

/-- The chain points of the Chung-8 reference chain. -/
noncomputable def chainX : ℕ → ℝ
  | 0 => 1 - chungBeta8 (4 / 5)
  | 1 => 811 / 5000
  | 2 => 857 / 2000
  | 3 => 3669 / 5000
  | _ => 4443 / 5000

@[simp] theorem chainX_zero : chainX 0 = 1 - chungBeta8 (4 / 5) := rfl
@[simp] theorem chainX_one : chainX 1 = 811 / 5000 := rfl
@[simp] theorem chainX_two : chainX 2 = 857 / 2000 := rfl
@[simp] theorem chainX_three : chainX 3 = 3669 / 5000 := rfl
@[simp] theorem chainX_four : chainX 4 = 4443 / 5000 := rfl

/-- The chord extension point `x_top` of the top bucket, used only by the `t1`
certificate. -/
noncomputable def chainTop : ℝ := 9333 / 10000

/-- The finite-size profile at `π`, exactly. -/
theorem beta8_pi_eq : chungBeta8 (4 / 5) = 94911 / 100000 := by
  norm_num [chungBeta8]

theorem beta8_pi_bounds :
    (9491 : ℝ) / 10000 < chungBeta8 (4 / 5) ∧
      chungBeta8 (4 / 5) < (2966 : ℝ) / 3125 := by
  rw [beta8_pi_eq]
  norm_num

/-- The first bucket width is *exactly* `g_π`. -/
theorem chainX_one_sub_zero : chainX 1 - chainX 0 = gpi8 := by
  norm_num [chainX, gpi8, gainD8, chungBeta8]

theorem chung8_ghat_eq :
    (chung8Tracking).ghat = gpi8 := by
  rw [(chung8Tracking).ghat_eq_gpi chung8_condB, chung8Setting_gpi]

theorem chung8_lam_eq :
    (chung8Tracking).lam = chainX 0 := by
  rw [(chung8Tracking).lam_eq_piBar (chung8_condB)]
  simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi, chainX_zero]

theorem chung8_betaD_eq (t : ℝ) :
    (chung8Setting).betaD t = chungBeta8 t - 189 / 5000 := by
  simp only [Setting.betaD, chung8Setting_β, chung8Setting_delta]

/-- `β_δ(x₀) = x₁`, exactly: the mirror law, not a bracket. -/
theorem chung8_betaD_chainX_zero :
    (chung8Setting).betaD (chainX 0) = chainX 1 := by
  rw [chung8_betaD_eq, chainX_zero, chainX_one,
    chungBeta8_reversal (by norm_num : ((4 : ℝ) / 5) ∈ Ioo (0 : ℝ) 1)]
  norm_num

/-- **The Chung-8 reference chain.**  Every field is a theorem about the constructed
degree-eight curve: the head from the mirror law, the four steps from the brackets of
`ChungNumerics.lean`, and the widths from `g_π < 0.1114`. -/
noncomputable def chung8RefChain :
    RefChain (chung8Setting) (chung8Tracking) where
  m := 4
  x := chainX
  m_pos := by norm_num
  base := by rw [chung8_lam_eq]
  width := by
    intro k hk
    rw [chung8_ghat_eq]
    interval_cases k
    · rw [chainX_one_sub_zero]
    · change gpi8 ≤ chainX 2 - chainX 1
      simp only [chainX_two, chainX_one]; linarith [gpi8_bounds.2]
    · change gpi8 ≤ chainX 3 - chainX 2
      simp only [chainX_three, chainX_two]; linarith [gpi8_bounds.2]
    · change gpi8 ≤ chainX 4 - chainX 3
      simp only [chainX_four, chainX_three]; linarith [gpi8_bounds.2]
  step := by
    intro k hk
    interval_cases k
    · rw [chung8_betaD_chainX_zero]
    · change chainX 2 ≤ _
      norm_num [Setting.gainD, chung8Setting, chainX, chungBeta8]
    · change chainX 3 ≤ _
      norm_num [Setting.gainD, chung8Setting, chainX, chungBeta8]
    · change chainX 4 ≤ _
      norm_num [Setting.gainD, chung8Setting, chainX, chungBeta8]
  mem := by
    intro k hk
    interval_cases k
    · rw [chainX_zero]
      constructor <;> linarith [beta8_pi_bounds.1, beta8_pi_bounds.2]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  top := by simp only [chung8Setting_pi, chainX_four]; norm_num

@[simp] theorem chung8RefChain_x :
    (chung8RefChain).x = chainX := rfl

@[simp] theorem chung8RefChain_m :
    (chung8RefChain).m = 4 := rfl

/-- `β_δ(x₄) ≥ x_top`: the chord extension point of the top bucket. -/
theorem chung8_chainTop_le :
    chainTop ≤ (chung8Setting).betaD (chainX 4) := by
  norm_num [Setting.betaD, chung8Setting, chainX, chainTop, chungBeta8]

/-! ### Evaluating the reference potential

`refPot` is affine on each bucket, so every certificate below is a finite case analysis
on which bucket a value lies in.  Only the first bucket has an irrational width — it is
exactly `ĝ = g_π` — and the two lemmas that touch it, `chainPot_ge_one_lip` and
`chainPot_low`, go through `refPot_lipschitz` rather than through an evaluation.
-/

theorem chainPot_one :
    (chung8RefChain).refPot (811 / 5000) = 1 := by
  have h := (chung8RefChain).refPot_x (j := 1) (by norm_num)
  simpa using h

theorem chainPot_three :
    (chung8RefChain).refPot (3669 / 5000) = 3 := by
  have h := (chung8RefChain).refPot_x (j := 3) (by norm_num)
  simpa using h

theorem chainPot_sat {t : ℝ} (ht : (4443 : ℝ) / 5000 ≤ t) :
    (chung8RefChain).refPot t = 4 := by
  have h := (chung8RefChain).refPot_eq_m (by simpa using ht)
  simpa using h

theorem chainPot_b1 {t : ℝ}
    (h1 : (811 : ℝ) / 5000 ≤ t) (h2 : t ≤ (857 : ℝ) / 2000) :
    (chung8RefChain).refPot t = 1 + (t - 811 / 5000) / (2663 / 10000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 1) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

theorem chainPot_b2 {t : ℝ}
    (h1 : (857 : ℝ) / 2000 ≤ t) (h2 : t ≤ (3669 : ℝ) / 5000) :
    (chung8RefChain).refPot t = 2 + (t - 857 / 2000) / (3053 / 10000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 2) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

theorem chainPot_b3 {t : ℝ}
    (h1 : (3669 : ℝ) / 5000 ≤ t) (h2 : t ≤ (4443 : ℝ) / 5000) :
    (chung8RefChain).refPot t = 3 + (t - 3669 / 5000) / (774 / 5000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 3) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

/-- The Lipschitz bound at the certificate's rational rate `1/ĝ < 10000/1113`. -/
theorem chainPot_lip {u v : ℝ} (huv : v ≤ u) :
    (chung8RefChain).refPot u - (chung8RefChain).refPot v
      ≤ (10000 / 1113) * (u - v) := by
  have hlip := (chung8RefChain).refPot_lipschitz huv
  rw [chung8_ghat_eq] at hlip
  have hstep : (u - v) / gpi8 ≤ (u - v) / (1113 / 10000) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) gpi8_bounds.1.le
  have hval : (u - v) / (1113 / 10000 : ℝ) = (10000 / 1113) * (u - v) := by ring
  linarith [hval ▸ hstep]

/-! ### The five scalar certificates

Write `A = 2250/557` for the rational charge rate `(λ-1)/ĝ` obtained from `ĝ < 0.1114`,
and `Φ` for `refPot`.  The modulus certificate needs an upper bound for `Φ - A·t` and a
lower bound for it on `[x₁, x₄]` (`chainPot_hi_ub`, `chainPot_hi_lb`), the statement that
`Φ` gains no more than `A` per unit up to `t = 0.85` (`chainPot_up_zero`), and two bounds
below `x₁` (`chainPot_down`, `chainPot_low`).  The first bucket is where the certificate
is tight: `A · ĝ + (1 - loss) = 1.022`, only `2%` above the single level that bucket
carries.
-/

/-- `Φ(t) - A t` is largest at the top chain point. -/
theorem chainPot_hi_ub {t : ℝ} (ht : (811 : ℝ) / 5000 ≤ t) :
    (chung8RefChain).refPot t - (2250 / 557) * t
      ≤ 4 - (2250 / 557) * (4443 / 5000) := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 h h2]; linarith
  rcases le_total t ((4443 : ℝ) / 5000) with h3 | h3
  · rw [chainPot_b3 h2 h3]; linarith
  · rw [chainPot_sat h3]; linarith

/-- …and, on `[x₁, x₄]`, smallest at `x₃`. -/
theorem chainPot_hi_lb {t : ℝ}
    (ht : (811 : ℝ) / 5000 ≤ t) (ht4 : t ≤ (4443 : ℝ) / 5000) :
    3 - (2250 / 557) * (3669 / 5000)
      ≤ (chung8RefChain).refPot t - (2250 / 557) * t := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 h h2]; linarith
  · rw [chainPot_b3 h2 ht4]; linarith

/-- Up to `t = 0.85` the potential has still not gained more than `A` per unit since
`x₁`.  The crossing point is `0.8614`, so `0.85` leaves room on both sides of the
modulus argument. -/
theorem chainPot_up_zero {t : ℝ}
    (ht : (811 : ℝ) / 5000 ≤ t) (ht2 : t ≤ 17 / 20) :
    (chung8RefChain).refPot t - 1 ≤ (2250 / 557) * (t - 811 / 5000) := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 h h2]; linarith
  · rw [chainPot_b3 h2 (by linarith)]; linarith

/-- Below `x₁` the potential is at most `10000/1113` per unit short of `1`. -/
theorem chainPot_down {t : ℝ} (ht : t ≤ (811 : ℝ) / 5000) :
    1 - (chung8RefChain).refPot t ≤ (10000 / 1113) * (811 / 5000 - t) := by
  have h := chainPot_lip ht
  rw [chainPot_one] at h
  linarith

/-- The same bound at the charge rate `A`, with the first bucket's own allowance
`1 - A ĝ ≤ 12263/22280`.  This is the tight certificate: the bucket is exactly `ĝ` wide
and carries exactly one level. -/
theorem chainPot_down_A {t : ℝ} (ht : t ≤ (811 : ℝ) / 5000) :
    1 - (chung8RefChain).refPot t
      ≤ (2250 / 557) * (811 / 5000 - t) + 12263 / 22280 := by
  rcases le_total ((811 : ℝ) / 5000 - t) (1113 / 10000) with h | h
  · have := chainPot_down ht
    linarith
  · have := (chung8RefChain).refPot_nonneg t
    linarith

/-- The modulus, inside the first bucket. -/
theorem chainPot_low {u v : ℝ} (huv : v ≤ u)
    (hu : u ≤ (811 : ℝ) / 5000) :
    (chung8RefChain).refPot u - (chung8RefChain).refPot v
      ≤ (2250 / 557) * (u - v) + 12263 / 22280 := by
  rcases le_total (u - v) ((1113 : ℝ) / 10000) with h | h
  · have := chainPot_lip huv
    linarith
  · have h1 : (chung8RefChain).refPot u ≤ 1 := by
      rw [← chainPot_one]
      exact (chung8RefChain).refPot_mono hu
    have h2 := (chung8RefChain).refPot_nonneg v
    linarith

/-- The first bucket, whose width is exactly `ĝ`. -/
theorem chainPot_b0 {t : ℝ}
    (h1 : chainX 0 ≤ t) (h2 : t ≤ (811 : ℝ) / 5000) :
    (chung8RefChain).refPot t = (t - chainX 0) / gpi8 := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 0) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  have e1 : (chung8RefChain).x (0 + 1) - (chung8RefChain).x 0 = gpi8 :=
    chainX_one_sub_zero
  have e0 : (chung8RefChain).x 0 = chainX 0 := rfl
  rw [h, e1, e0]
  norm_num

/-! ### The ledger certificate -/

/-- `g_π` exactly.  `gpi8_bounds` brackets it; the polygon actually evaluates. -/
theorem gpi8_eq : gpi8 = 11131 / 100000 := by
  norm_num [gpi8, gainD8]

/-- `x₀ = π̄` exactly. -/
theorem chainX_zero_eq : chainX 0 = 5089 / 100000 := by
  rw [chainX_zero, beta8_pi_eq]; norm_num

/-- `β_δ(π)` exactly: one free level from the fertility threshold. -/
theorem chung8_betaD_pi : (chung8Setting).betaD (4 / 5) = 91131 / 100000 := by
  rw [chung8_betaD_eq, beta8_pi_eq]; norm_num

/-- **The top-bucket Lipschitz certificate.**  Measured down from the top chain point,
the potential falls at rate `1/(x₄ - x₃) = 6.46`, not at the global rate `1/ĝ = 8.98`.
Equality holds on the top bucket; below it the shallower buckets leave room. -/
theorem chainPot_topLip_le {v : ℝ} (hv : v ≤ (4443 : ℝ) / 5000) :
    (4 : ℝ) - (chung8RefChain).refPot v ≤ (4443 / 5000 - v) / (387 / 2500) := by
  rcases le_total ((3669 : ℝ) / 5000) v with h3 | h3
  · rw [chainPot_b3 h3 hv]; linarith
  rcases le_total ((857 : ℝ) / 2000) v with h2 | h2
  · rw [chainPot_b2 h2 h3]; linarith
  rcases le_total ((811 : ℝ) / 5000) v with h1 | h1
  · rw [chainPot_b1 h1 h2]; linarith
  · have := (chung8RefChain).refPot_nonneg v
    linarith

/-- **The blocked-range drop certificate.**  A blocked range below a fertile depth has its
own first free level, so its endpoint is at least `β_δ(π) - x`; the potential it can
destroy is affine in its own spend.  The bound is tight at both ends of the window. -/
theorem chainPot_blockDrop {x : ℝ} (hlo : (144703 : ℝ) / 500000 ≤ x) (hhi : x ≤ 4 / 5) :
    (4 : ℝ) - (chung8RefChain).refPot (91131 / 100000 - x) ≤ 819 / 200 * x + 91 / 500 := by
  set v : ℝ := 91131 / 100000 - x with hvdef
  have hvlo : (11131 : ℝ) / 100000 ≤ v := by simp only [hvdef]; linarith
  have hvhi : v ≤ (38869 : ℝ) / 62500 := by simp only [hvdef]; linarith
  have hx : x = 91131 / 100000 - v := by simp only [hvdef]; ring
  rw [hx]
  rcases le_total ((857 : ℝ) / 2000) v with h2 | h2
  · rw [chainPot_b2 h2 (by linarith)]; linarith
  rcases le_total ((811 : ℝ) / 5000) v with h1 | h1
  · rw [chainPot_b1 h1 h2]; linarith
  · rw [chainPot_b0 (by rw [chainX_zero_eq]; linarith) h1, gpi8_eq, chainX_zero_eq]
    linarith

/--
**The Chung-8 ledger certificate**, at charge rate `λ = 1.32`, expandability slack
`cs = 8/5` and saturation loss `loss = 331/774 = 0.4276`.

* `cs = 8/5` is free: `mirror_floor` proves the tracked footprint stays above `σ`, and
  only `π̂` is needed, so the search may run at `(i + 8/5) ĝ` instead of `(i + 1) ĝ`.
  That shortens every blocked range by three fifths of a level.
* `topLip` is `chainPot_topLip_le`, `chord` is the top-bucket chord of
  `RefChain.betaD_chord` with the extension point `x_top = 0.9333`;
* `blockDrop` is `chainPot_blockDrop`, and the two rate conditions are linear arithmetic
  in `g_π = 0.11131`.
-/
noncomputable def chung8LedgerCert :
    LedgerCert (chung8Setting) (chung8Tracking) (chung8RefChain) where
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
  loss_ge := by
    intro v _ hv
    rw [chung8Setting_pi] at hv
    have hm : ((chung8RefChain).m : ℝ) - 1 = 3 := by norm_num [chung8RefChain_m]
    rw [hm]
    have hpi : (chung8RefChain).refPot (4 / 5) = 3 + 331 / 774 := by
      rw [chainPot_b3 (t := 4 / 5) (by norm_num) (by norm_num)]; norm_num
    have hmono : (chung8RefChain).refPot v ≤ (chung8RefChain).refPot (4 / 5) :=
      (chung8RefChain).refPot_mono hv
    rw [hpi] at hmono
    linarith
  topLip := by
    intro u v hu hv
    have hu' : (4443 : ℝ) / 5000 ≤ u := by simpa using hu
    have hsat : (chung8RefChain).refPot u = 4 := by
      have := chainPot_sat hu'
      simpa using this
    rcases le_total ((4443 : ℝ) / 5000) v with hv4 | hv4
    · rw [hsat, chainPot_sat hv4]
      have h : (0 : ℝ) ≤ u - v := by linarith
      have : (0 : ℝ) ≤ (u - v) / (387 / 2500) := by positivity
      linarith
    · have hkey := chainPot_topLip_le hv4
      have hmono : (4443 / 5000 - v) / ((387 : ℝ) / 2500) ≤ (u - v) / (387 / 2500) := by
        rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
      rw [hsat]; linarith
  chord := by
    intro v hv3 hv
    rw [chung8Setting_pi] at hv
    have hv3' : (3669 : ℝ) / 5000 ≤ v := by simpa using hv3
    have hv4 : v ≤ (4443 : ℝ) / 5000 := by linarith
    have hm : ((chung8RefChain).m : ℝ) - 1 = 3 := by norm_num [chung8RefChain_m]
    have hxm : (chung8RefChain).x (chung8RefChain).m = (4443 : ℝ) / 5000 := by
      simp [chung8RefChain_m]
    have hpot : (chung8RefChain).refPot v - 3 = (5000 / 774) * (v - 3669 / 5000) := by
      rw [chainPot_b3 hv3' hv4]; ring
    have hchord : (4443 : ℝ) / 5000 + (149 / 516) * (v - 3669 / 5000)
        ≤ (chung8Setting).betaD v := by
      have h := (chung8RefChain).betaD_chord (k := 3) (by norm_num)
        (chung8_chainTop_le) (show (chung8RefChain).x 3 ≤ v by simpa using hv3')
        (show v ≤ (chung8RefChain).x (3 + 1) by simpa using hv4)
      have e1 : (chung8RefChain).x 3 = (3669 : ℝ) / 5000 := rfl
      have e2 : (chung8RefChain).x (3 + 1) = (4443 : ℝ) / 5000 := rfl
      rw [e1, e2] at h
      simp only [chainTop] at h
      calc (4443 : ℝ) / 5000 + (149 / 516) * (v - 3669 / 5000)
          = (4443 : ℝ) / 5000 + (v - 3669 / 5000) / ((4443 : ℝ) / 5000 - 3669 / 5000)
              * ((9333 : ℝ) / 10000 - 4443 / 5000) := by ring
        _ ≤ (chung8Setting).betaD v := h
    rw [hxm, hm, hpot]
    linarith
  ghat_le_lam_wtop := by
    rw [chung8_ghat_eq, gpi8_eq]; norm_num
  inf_rate := by
    intro θ s hθ0 hθloss hs hspend
    rw [chung8_ghat_eq, gpi8_eq]
    have hxm : (chung8RefChain).x (chung8RefChain).m = (4443 : ℝ) / 5000 := by
      simp [chung8RefChain_m]
    rw [hxm, chung8Setting_pi] at hspend
    linarith
  blockDrop := by
    intro x hx hxρ
    rw [chung8Setting_rho] at hxρ
    rw [chung8_ghat_eq, gpi8_eq] at hx
    rw [chung8Setting_pi, chung8_betaD_pi]
    have hm : ((chung8RefChain).m : ℝ) = 4 := by norm_num [chung8RefChain_m]
    rw [hm]
    exact chainPot_blockDrop (by linarith) hxρ
  blockDrop_one := by
    intro x hx
    rw [chung8_ghat_eq, gpi8_eq] at hx
    linarith
  blk_rate := by
    intro x y hx hxρ hy
    rw [chung8Setting_rho] at hxρ
    rw [chung8_ghat_eq, gpi8_eq] at hx ⊢
    linarith

/-! ### The two-link threshold at `ℓ = 14`

The potential ledger's chain-length condition is

  `potHead + (z - 1) potSpan + λ ρ / ĝ < ℓ`,

and at the Chung-8 Filecoin parameters its three terms are `0.5982`, `3.8212` and
`9.4870`.  Their sum `13.9064` is below `14`, so `ℓ = 14` certifies two links.  The
source weight is `σ = 74/625`, so two links give payoff `0.2816 n`.

The budget charge is what moved: `λ` fell from `1.45` to `1.32` because the infertile
step is now priced by the top-bucket Lipschitz constant `1/(x₄ - x₃) = 6.46` rather than
by `1/ĝ = 8.98`, and because a blocked range keeps its own first free level.  The
expandability slack `cs = 8/5` shortens every blocked range by `3/5` of a level.
-/

@[simp] theorem chung8LedgerCert_lam :
    (chung8LedgerCert).lam = 33 / 25 := rfl

@[simp] theorem chung8LedgerCert_cs :
    (chung8LedgerCert).cs = 8 / 5 := rfl

@[simp] theorem chung8LedgerCert_loss :
    (chung8LedgerCert).loss = 331 / 774 := rfl

/-- `refPot σ > 0.60646`: the source starts a fifth of the way up the first bucket, and
that is the only place the potential of the growth phase is charged. -/
theorem chainPot_sigma_gt :
    (675 : ℝ) / 1113 < (chung8RefChain).refPot (74 / 625) := by
  have hx0 : chainX 0 = 811 / 5000 - gpi8 := by
    have h := chainX_one_sub_zero
    simp only [chainX_one] at h
    linarith
  have hlo : chainX 0 ≤ (74 : ℝ) / 625 := by
    rw [chainX_zero]
    linarith [beta8_pi_bounds.1]
  rw [chainPot_b0 hlo (by norm_num), hx0]
  rw [lt_div_iff₀ (by linarith [gpi8_bounds.1] : (0 : ℝ) < gpi8)]
  linarith [gpi8_bounds.1]

theorem chung8_potHead_eq :
    LedgerCert.potHead (chung8RefChain) (chung8LedgerCert) = 463 / 774 := by
  have hζ : (chung8RefChain).refPot (4311 / 5000) = 3 + 642 / 774 := by
    rw [chainPot_b3 (t := 4311 / 5000) (by norm_num) (by norm_num)]; norm_num
  simp only [LedgerCert.potHead, chung8Setting_zetaDelta, chung8RefChain_m,
    chung8LedgerCert_loss, hζ]
  norm_num

theorem chung8_potSpan_lt :
    LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert)
      < 4 - 675 / 1113 + 331 / 774 := by
  have h := chainPot_sigma_gt
  simp only [LedgerCert.potSpan, chung8Tracking_sigma, chung8RefChain_m,
    chung8LedgerCert_loss]
  norm_num
  linarith

theorem chung8_ledgerCharge_eq :
    (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat
      = 105600 / 11131 := by
  rw [chung8LedgerCert_lam, chung8Setting_rho, chung8_ghat_eq, gpi8_eq]
  norm_num

/-- **The two-link threshold of the potential ledger, evaluated.**  `14.8417 < 15`. -/
theorem chung8_potential_threshold {ℓ : ℕ} (hℓ : 14 ≤ ℓ) :
    LedgerCert.potHead (chung8RefChain) (chung8LedgerCert)
        + (((2 : ℕ) : ℝ) - 1) * LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert)
        + (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat
      < ((ℓ : ℕ) : ℝ) := by
  have h1 := chung8_potHead_eq
  have h2 := chung8_potSpan_lt
  have h3 := chung8_ledgerCharge_eq
  have hℓ' : (14 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  push_cast
  linarith

/-- The slack `mirror_floor` has to spare at `cs = 8/5`: the tracked footprint may fall
`(cs - 1) ĝ = 0.0668` below `σ` and still clear the tracking floor `π̂ = 0.05089`. -/
theorem chung8_cs_slack :
    (chung8Tracking).lam + ((chung8LedgerCert).cs - 1) * (chung8Tracking).ghat
      ≤ (chung8Tracking).σ := by
  rw [chung8_lam_eq, chainX_zero_eq, chung8LedgerCert_cs, chung8_ghat_eq, gpi8_eq,
    chung8Tracking_sigma]
  norm_num

/--
**Two chain links at `ℓ = 14`, at the full `0.2816 n` payoff.**

No reference chain appears among the theorem's hypotheses; it is supplied here, and its
conditions are the `ChungNumerics` brackets for the constructed curve.  The potential
ledger charges the black budget once at `λ/ĝ`, with `λ = 1.32`, and has per-link span
`potSpan = 3.82`.  The source weight is `σ = 74/625`.
-/
theorem chung8_latency_deterministic
    {V : Type u} {ℓ n : ℕ} (hℓ : 14 ≤ ℓ)
    (G : Concrete.LayeredGraph V (chung8Setting) ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) := by
  have hσapi : (chung8Tracking).σ < G.αpi := by
    rw [chung8Tracking_sigma, hαpi]; norm_num
  have h := latency_potential G P (chung8Tracking) (chung8LedgerCert) hn hσapi hDepth
    (chung8_zeta_le) (chung8_entry) (chung8_nobreak) (chung8_cs_slack) (z := 2) (by norm_num)
    (chung8_potential_threshold hℓ) A hA hred hweight
  have hlen : latencyLength G.αpi (chung8Tracking).σ n 2
      = (1 : ℝ) / 5 * n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n := by
    simp only [latencyLength, hαpi, chung8Tracking_sigma]
    push_cast
    ring
  rwa [hlen] at h

/-- **The 14-layer instance.** -/
theorem chung8_latency_14_deterministic
    {V : Type u} {n : ℕ}
    (G : Concrete.LayeredGraph V (chung8Setting) 14 n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) :=
  chung8_latency_deterministic (by norm_num) G P hn hαpi hDepth A hA hred hweight

end ChungCurve
end ProofOfSpace

/-
# The Chung-8 Filecoin specialization

This file instantiates the degree-parametric Chung curve from `ChungCurve.lean` at
degree eight. The generic class `ChungAnalyticHypotheses d` exposes the two conditional
global shape facts used here: concavity on `[0,1]` and uniqueness of the gain maximizer.
Every declaration that depends on those facts carries an explicit
`[ChungAnalyticHypotheses 8]` parameter.

The last section exhibits the reference chain of `Potential.lean` for these parameters —
the `β_δ` orbit of the tracking floor, rationalized downwards — together with its
`LedgerCert`, and evaluates the potential ledger's constants.  That is what
`chung8_latency_15` runs on.  The chain is data supplied here, not a hypothesis of
anything upstream.
-/
import ProofOfSpace.ChungNumerics
import ProofOfSpace.Latency
import ProofOfSpace.Ledger
import Mathlib.Analysis.Convex.Continuous

namespace ProofOfSpace
namespace ChungCurve

open Set

/-! ### Degree-eight notation for the generic closed profile -/

/-- The degree-eight Chung threshold on `(0,1)`, extended by `β(0)=0` and
`β(1)=1`.  Values outside `[0,1]` are irrelevant to `Setting`; the chosen clamped
extension makes the definition total. -/
noncomputable def chungBeta8 (x : ℝ) : ℝ := chungBetaProfile 8 x

@[simp] theorem chungBeta8_zero : chungBeta8 0 = 0 := by
  simp [chungBeta8]

@[simp] theorem chungBeta8_one : chungBeta8 1 = 1 := by
  simp [chungBeta8]

theorem chungBeta8_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chungBeta8 x = chungBeta 8 x := by
  exact chungBetaProfile_eq hx

theorem chungBeta8_maps {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    chungBeta8 x ∈ Icc (0 : ℝ) 1 := by
  exact chungBetaProfile_maps (by norm_num) hx

theorem chungBeta8_expands {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < chungBeta8 x := by
  exact chungBetaProfile_expands (by norm_num) hx

theorem chungBeta8_reversal {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chungBeta8 (1 - chungBeta8 x) = 1 - x := by
  exact chungBetaProfile_reversal (by norm_num) hx

theorem chungBeta8_strictMonoOn :
    StrictMonoOn chungBeta8 (Icc (0 : ℝ) 1) := by
  exact chungBetaProfile_strictMonoOn 8 (by norm_num)

namespace ChungAnalyticHypotheses

/-! #### The adjusted gain of the constructed curve

`gain_δ` does not mention `H`: `chung8Setting` fixes `β := chungBeta8` and
`δ := 189/5000` outright.  The three signs below are pure `ChungNumerics` facts, and they
are what turn the two zeros of `gain_δ` from assumptions into consequences. -/

/-- The adjusted gain of the constructed curve, available before any `Setting` exists. -/
noncomputable def gd (x : ℝ) : ℝ := chungBeta8 x - 189 / 5000 - x

theorem gd_pi_pos : 0 < gd ((4 : ℝ)/5) := by
  rw [gd, chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
  linarith [beta_08_lower]

theorem gd_1184_pos : 0 < gd ((74 : ℝ)/625) := by
  rw [gd, chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
  have hcond := condB_holds_at_1184
  have hgpi := gpi8_bounds.1
  simp only [gpi8, gainD8] at hcond hgpi
  linarith

theorem gd_1_256_neg : gd ((1 : ℝ)/256) < 0 := by
  rw [gd, chungBeta8_eq (by norm_num : (1 / 256 : ℝ) ∈ Ioo 0 1)]
  have h := gainD8_neg_at_1_256
  simp only [gainD8] at h
  linarith

theorem gd_concaveOn [H : ChungAnalyticHypotheses (8 : ℝ)] :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) gd := by
  have h : gd = chungBeta8 - fun x : ℝ => x + 189 / 5000 := by
    funext x; simp only [gd, Pi.sub_apply]; ring
  rw [h]
  exact H.concaveOn.sub (convexOn_add_const (convex_Icc 0 1) (189 / 5000))

theorem beta_αg_mem [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chungBeta8 H.αg ∈ Ioo (0 : ℝ) 1 := by
  have hαg := H.αg_mem
  have hβ := chungBeta8_maps ⟨hαg.1.le, hαg.2.le⟩
  refine ⟨hαg.1.trans (chungBeta8_expands hαg), ?_⟩
  rcases eq_or_lt_of_le hβ.2 with hone | hlt
  · have hstrict := chungBeta8_strictMonoOn
      ⟨hαg.1.le, hαg.2.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hαg.2
    rw [hone, chungBeta8_one] at hstrict
    exact False.elim (lt_irrefl 1 hstrict)
  · exact hlt

/-- For the constructed curve: the decreasing mirror map `x ↦ 1 - β(x)`
fixes the maximizer.  This is the `Setting.mirror_αg` argument, run before the `Setting`
exists. -/
theorem mirror_αg [H : ChungAnalyticHypotheses (8 : ℝ)] :
    1 - chungBeta8 H.αg = H.αg := by
  have hαg := H.αg_mem
  have hβopen := beta_αg_mem (H := H)
  have hm : (1 - chungBeta8 H.αg) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hβopen.2], by linarith [hβopen.1]⟩
  have hgain : chungBeta8 (1 - chungBeta8 H.αg) - (1 - chungBeta8 H.αg)
      = chungBeta8 H.αg - H.αg := by
    rw [chungBeta8_reversal hαg]; ring
  by_contra hne
  have hmax : chungBeta8 (1 - chungBeta8 H.αg) - (1 - chungBeta8 H.αg)
      < chungBeta8 H.αg - H.αg := by
    simpa [chungBeta8] using H.αg_max ⟨hm.1.le, hm.2.le⟩ hne
  linarith

/-- The maximizer is its own mirror, so it lies below `1/2` and a fortiori below `π`. -/
theorem αg_lt_pi [H : ChungAnalyticHypotheses (8 : ℝ)] : H.αg < (4 : ℝ)/5 := by
  have hexp := chungBeta8_expands H.αg_mem
  have hfix := mirror_αg (H := H)
  linarith

/-- The gain at the maximizer dominates the gain at `π`, which is positive. -/
theorem gd_αg_pos [H : ChungAnalyticHypotheses (8 : ℝ)] : 0 < gd H.αg := by
  have hmax : chungBeta8 ((4 : ℝ) / 5) - (4 : ℝ) / 5
      < chungBeta8 H.αg - H.αg := by
    simpa [chungBeta8] using H.αg_max
      (by norm_num : ((4 : ℝ) / 5) ∈ Icc (0 : ℝ) 1)
      (ne_of_gt (αg_lt_pi (H := H)))
  have hpi := gd_pi_pos
  simp only [gd] at hpi ⊢
  linarith

/-- Concavity gives continuity on the open interval, which is all the intermediate value
theorem needs. -/
theorem gd_continuousOn [H : ChungAnalyticHypotheses (8 : ℝ)] :
    ContinuousOn gd (Ioo (0 : ℝ) 1) := by
  have h := (gd_concaveOn (H := H)).continuousOn_interior
  rwa [interior_Icc] at h

/-- **The left zero of `gain_δ` exists.**  `gain_δ` is negative at `1/256`
(`gainD8_neg_at_1_256`) and positive at `0.1184` (`condB_holds_at_1184`), and concavity
supplies continuity in between.  The statement does not mention `H`. -/
theorem exists_left_root [H : ChungAnalyticHypotheses (8 : ℝ)] :
    ∃ r ∈ Icc ((1 : ℝ)/256) ((74 : ℝ)/625), gd r = 0 := by
  have hsub : Icc ((1 : ℝ)/256) ((74 : ℝ)/625) ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcont := (gd_continuousOn (H := H)).mono hsub
  have hmem : (0 : ℝ) ∈ Icc (gd ((1 : ℝ)/256)) (gd ((74 : ℝ)/625)) :=
    ⟨gd_1_256_neg.le, gd_1184_pos.le⟩
  exact intermediate_value_Icc (by norm_num : ((1 : ℝ)/256) ≤ (74 : ℝ)/625) hcont hmem

/-- `α_δ^min`, the left zero of the adjusted gain. -/
noncomputable def αmin [H : ChungAnalyticHypotheses (8 : ℝ)] : ℝ :=
  Classical.choose (exists_left_root (H := H))

theorem αmin_mem_bracket [H : ChungAnalyticHypotheses (8 : ℝ)] :
    αmin ∈ Icc ((1 : ℝ)/256) ((74 : ℝ)/625) :=
  (Classical.choose_spec (exists_left_root (H := H))).1

theorem gainD_αmin [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chungBeta8 αmin - (189 : ℝ) / 5000 - αmin = 0 :=
  (Classical.choose_spec (exists_left_root (H := H))).2

theorem αmin_pos [H : ChungAnalyticHypotheses (8 : ℝ)] : 0 < αmin :=
  lt_of_lt_of_le (by norm_num) (αmin_mem_bracket (H := H)).1

theorem αmin_lt_pi [H : ChungAnalyticHypotheses (8 : ℝ)] : αmin < (4 : ℝ)/5 :=
  lt_of_le_of_lt (αmin_mem_bracket (H := H)).2 (by norm_num)

theorem αmin_mem_Ioo [H : ChungAnalyticHypotheses (8 : ℝ)] : αmin ∈ Ioo (0 : ℝ) 1 :=
  ⟨αmin_pos (H := H), (αmin_lt_pi (H := H)).trans (by norm_num)⟩

/-- The left zero lies at or below the maximizer: if it lay strictly above, the chord from
`αg` to `π` — both points where `gain_δ` is positive — would force it positive. -/
theorem αmin_mem [H : ChungAnalyticHypotheses (8 : ℝ)] : αmin ∈ Icc (0 : ℝ) H.αg := by
  refine ⟨(αmin_pos (H := H)).le, ?_⟩
  by_contra hcon
  push Not at hcon
  have hchord := concaveOn_chord_le (gd_concaveOn (H := H))
    ⟨H.αg_mem.1.le, H.αg_mem.2.le⟩
    (by norm_num : ((4 : ℝ)/5) ∈ Icc (0 : ℝ) 1) hcon (αmin_lt_pi (H := H))
  have hzero : gd αmin = 0 := gainD_αmin (H := H)
  rw [hzero] at hchord
  have h1 : 0 < ((4 : ℝ)/5 - αmin) / ((4 : ℝ)/5 - H.αg) :=
    div_pos (by linarith [αmin_lt_pi (H := H)]) (by linarith [αg_lt_pi (H := H)])
  have h2 : 0 < (αmin - H.αg) / ((4 : ℝ)/5 - H.αg) :=
    div_pos (by linarith) (by linarith [αg_lt_pi (H := H)])
  nlinarith [gd_αg_pos (H := H), gd_pi_pos]

/-- **The right root is the mirror of the left one.**  The mirror identity of
`reversal identity` says the map
`x ↦ 1 - β(x)` preserves the gain, so it carries one zero of `gain_δ` to the other.  The
right root therefore does not have to be assumed: it is `1 - β(α_min)`. -/
noncomputable def αmax [H : ChungAnalyticHypotheses (8 : ℝ)] : ℝ :=
  1 - chungBeta8 αmin

theorem gainD_αmax [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chungBeta8 αmax - (189 : ℝ) / 5000 - αmax = 0 := by
  have hrev := chungBeta8_reversal (αmin_mem_Ioo (H := H))
  have hroot := gainD_αmin (H := H)
  change chungBeta8 (1 - chungBeta8 αmin) - (189 : ℝ) / 5000
      - (1 - chungBeta8 αmin) = 0
  rw [hrev]
  linarith

theorem αmax_mem [H : ChungAnalyticHypotheses (8 : ℝ)] : αmax ∈ Icc H.αg 1 := by
  constructor
  · have hmono : chungBeta8 αmin ≤ chungBeta8 H.αg := by
      rcases eq_or_lt_of_le (αmin_mem (H := H)).2 with heq | hlt
      · rw [heq]
      · exact (chungBeta8_strictMonoOn ⟨(αmin_mem (H := H)).1,
          (αmin_mem_Ioo (H := H)).2.le⟩
          ⟨H.αg_mem.1.le, H.αg_mem.2.le⟩ hlt).le
    have := mirror_αg (H := H)
    change H.αg ≤ 1 - chungBeta8 αmin
    linarith
  · have := (chungBeta8_maps ⟨(αmin_mem (H := H)).1,
      (αmin_mem_Ioo (H := H)).2.le⟩).1
    change 1 - chungBeta8 αmin ≤ 1
    linarith

end ChungAnalyticHypotheses

/-- The unique gain maximizer is fixed by the mirror involution, hence lies below `1/2`
(and therefore below Filecoin's `π = 4/5`). -/
theorem chung8_αg_lt_pi [H : ChungAnalyticHypotheses (8 : ℝ)] : H.αg < (4 : ℝ) / 5 :=
  ChungAnalyticHypotheses.αg_lt_pi (H := H)

/-! ### Exact Chung-8 `Setting` and Filecoin bundles -/

/-- The development's parameter setting with the *actual constructed Chung-8 curve* as `β`. -/
noncomputable def chung8Setting [H : ChungAnalyticHypotheses (8 : ℝ)] : Setting where
  β := chungBeta8
  αg := H.αg
  δ := 189 / 5000
  pi := 4 / 5
  ρ := 4 / 5
  ζδ := 4311 / 5000
  αmin := ChungAnalyticHypotheses.αmin
  αmax := ChungAnalyticHypotheses.αmax
  β_maps := fun _ hx => chungBeta8_maps hx
  β_zero := chungBeta8_zero
  β_strictMonoOn := chungBeta8_strictMonoOn
  β_concaveOn := H.concaveOn
  β_expands := fun _ hx => chungBeta8_expands hx
  β_reversal := fun _ hx => chungBeta8_reversal hx
  αg_mem := H.αg_mem
  αg_max := fun _ hx hne => H.αg_max hx hne
  δ_nonneg := by norm_num
  ρ_nonneg := by norm_num
  pi_mem := by norm_num
  αg_lt_pi := chung8_αg_lt_pi (H := H)
  gpi_pos := by
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower]
  αmin_mem := ChungAnalyticHypotheses.αmin_mem (H := H)
  αmax_mem := ChungAnalyticHypotheses.αmax_mem (H := H)
  gainD_αmin := ChungAnalyticHypotheses.gainD_αmin (H := H)
  gainD_αmax := ChungAnalyticHypotheses.gainD_αmax (H := H)

@[simp] theorem chung8Setting_β [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chung8Setting.β = chungBeta8 := rfl


@[simp] theorem chung8Setting_delta [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chung8Setting.δ = (189 : ℝ) / 5000 := rfl

@[simp] theorem chung8Setting_pi [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chung8Setting.pi = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_rho [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chung8Setting.ρ = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_zetaDelta [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chung8Setting.ζδ = (4311 : ℝ) / 5000 := rfl

/-- The abstract `Setting.gpi` is exactly the `gpi8` computed from the constructed
degree-eight Chung threshold. -/
theorem chung8Setting_gpi [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).gpi = gpi8 := by
  simp only [Setting.gpi, Setting.gainD, chung8Setting_β, chung8Setting_delta,
    chung8Setting_pi, gpi8, gainD8]
  rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]

/-- The abstract `Setting.gainD` at the mid-point `σ̃ = 3/5`, in terms of the
constructed degree-eight Chung threshold. -/
theorem chung8Setting_gainD_06 [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).gainD (3/5) = gainD8 (3/5) := by
  simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta, gainD8]
  rw [chungBeta8_eq (by norm_num : (3 / 5 : ℝ) ∈ Ioo 0 1)]

/-- Filecoin's tracked source weight for the Chung-8 setting. -/
noncomputable def chung8Tracking [H : ChungAnalyticHypotheses (8 : ℝ)] :
    Tracking (chung8Setting) where
  σ := 74 / 625
  σ_gt := by
    have hpositive : 0 < (chung8Setting).gainD ((74 : ℝ) / 625) := by
      simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta]
      rw [chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
      have hcond := condB_holds_at_1184
      have hgpi := gpi8_bounds.1
      simp only [gpi8, gainD8] at hcond hgpi
      linarith
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

@[simp] theorem chung8Tracking_mid [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Tracking).mid = (3 : ℝ) / 5 := rfl

@[simp] theorem chung8Tracking_sigma [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Tracking).σ = (74 : ℝ) / 625 := rfl

/-! ### Scalar facts for the Filecoin parameters

These facts are proved for the constructed curve and packaged by `chung8Filecoin`.
They are the inequalities `no-break parameter conditions` of `Filecoin specialization`. -/

/-- `π̄ < ζ_δ - ρ`: the challenge floor stays above the tracking floor. -/
theorem chung8_entry [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).piBar < (chung8Setting).ζδ - (chung8Setting).ρ := by
    simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi,
      chung8Setting_zetaDelta, chung8Setting_rho]
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower]

/-- `ζ_δ ≤ α_δ^max`: the challenge weight is inside the positive-gain interval. -/
theorem chung8_zeta_le [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).ζδ ≤ (chung8Setting).αmax := by
    have hpi : (4 / 5 : ℝ) ∈ Icc 0 1 := by norm_num
    have hzeta : (4311 / 5000 : ℝ) ∈ Icc 0 1 := by norm_num
    have hmono := chungBeta8_strictMonoOn hpi hzeta (by norm_num)
    have hpositive : 0 < (chung8Setting).gainD ((4311 : ℝ) / 5000) := by
      simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta]
      rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)] at hmono
      linarith [hmono, beta_08_lower]
    by_contra hcon
    push Not at hcon
    have hnonpos := (chung8Setting).gainD_nonpos_of_αmax_le hzeta hcon.le
    linarith

/-- `gain_δ(σ) ≥ 2 g_π` at `σ = 0.1184`, with `0.22268… ≥ 0.22262…` of little room. -/
theorem chung8_condB [H : ChungAnalyticHypotheses (8 : ℝ)] :
    2 * (chung8Setting).gpi ≤ (chung8Setting).gainD (chung8Tracking).σ := by
    rw [chung8Setting_gpi]
    simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta,
      chung8Tracking_sigma]
    rw [chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
    exact condB_holds_at_1184

/-- `ρ < β_δ(π) - π̄`: the whole budget cannot pay for one chain break. -/
theorem chung8_condC [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).ρ <
      (chung8Setting).pi + (chung8Setting).gpi - (chung8Setting).piBar := by
    simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi,
      chung8Setting_rho]
    rw [chung8Setting_gpi]
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower, gpi8_bounds.1]

/-- The no-break condition `ρ < β_δ(π) - π̂` at the Filecoin parameters, which is what
makes `Ledger.bMax` vanish and what the potential ledger needs for the tracking floor. -/
theorem chung8_nobreak [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).ρ
      < (chung8Setting).betaD (chung8Setting).pi - (chung8Tracking).lam := by
  have hb : (chung8Setting).betaD (chung8Setting).pi
      = (chung8Setting).pi + (chung8Setting).gpi := by
    simp only [Setting.betaD_eq]; rfl
  rw [(chung8Tracking).lam_eq_piBar (chung8_condB (H := H)), hb]
  linarith [chung8_condC (H := H)]

theorem chung8Filecoin [H : ChungAnalyticHypotheses (8 : ℝ)] :
    FilecoinLatencyParameters (chung8Setting) (chung8Tracking) where
  pi_eq := rfl
  rho_eq := rfl
  zetaDelta_eq := rfl
  sigma_eq := rfl
  gpi_lower := by rw [chung8Setting_gpi]; exact gpi8_bounds.1
  gpi_upper := by rw [chung8Setting_gpi]; exact gpi8_bounds.2
  ghat_eq := (chung8Tracking).ghat_eq_gpi (chung8_condB (H := H))
  gtilde_eq :=
    gtilde_eq_gpi
      (by simp only [Setting.zetaFloor]; linarith [chung8_entry (H := H)])
      (by
        simp only [Setting.zetaFloor, chung8Setting_zetaDelta, chung8Setting_rho,
          chung8Setting_pi]
        norm_num)
  mid_eq := rfl
  bMax_eq := bMax_eq_zero (chung8_nobreak (H := H))

/-- The Filecoin setting satisfies `general scalar conditions`, so `latency_general` is not
vacuous here.  The entry condition follows from the stronger `chung8_entry`, since
`α_δ^min < π̄` always. -/
theorem chung8GeneralRegime [H : ChungAnalyticHypotheses (8 : ℝ)] :
    GeneralRegime (chung8Setting) where
  entry := by
    have h := chung8_entry (H := H)
    have hmin := (chung8Setting).αmin_lt_piBar
    simp only [Setting.zetaFloor]
    linarith
  zeta_le := chung8_zeta_le (H := H)

/-- The two bundles used by the public latency theorem are simultaneously satisfied by
the defined Chung-8 curve, conditional only on the development's explicitly isolated global
analytic profile assumptions. -/
theorem chung8_filecoin_bundles [H : ChungAnalyticHypotheses (8 : ℝ)] :
    FilecoinLatencyParameters (chung8Setting) (chung8Tracking) ∧
      GeneralRegime (chung8Setting) :=
  ⟨chung8Filecoin (H := H), chung8GeneralRegime (H := H)⟩

/-! ### Public latency corollaries specialized to the Chung curve -/

/-- `cor:filecoin`, with `Setting.β` definitionally equal to the constructed
Chung-8 threshold (up to its endpoint extension). -/
theorem chung8_latency_corollary [H : ChungAnalyticHypotheses (8 : ℝ)]
    {V : Type u} {ℓ n : ℕ}
    (G : Concrete.LayeredGraph V (chung8Setting) ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5) (hℓ : 14 < ℓ)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((FilecoinLatencyParameters.filecoinZMin (chung8Setting).gpi ℓ : ℝ) - 1) *
          ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) :=
  (chung8Filecoin (H := H)).latency_corollary G P (chung8GeneralRegime (H := H))
    hn hαpi hℓ hDepth A hA hred hweight

/-! ### The growth constant

The two-piece potential `ProofOfSpace.growthPot` supplies the level count
`Φ_{σ̃}(π) + 1`, charging `2 ĝ` per level on
`[σ, σ̃]`.  At the Filecoin Chung-8 parameters the mid-point `σ̃ = 3/5` is certified
by `two_gpi_le_gainD8_06`.

**This is wired into the ledger** through `chung8Tracking`'s mid-point field
`σ̃ = 3/5`: `growthConst` takes the minimum of the two, `h₁ = growthConst + 1` becomes
`5.957 < h₁ < 5.961`.  `FilecoinLatencyParameters.growthConst_eq` supplies this value
to the numerical bounds.
-/

/-- The mid-point certificate `2 ĝ ≤ gain_δ(3/5)`, transported to the abstract
`Setting`. -/
theorem chung8_midpoint [H : ChungAnalyticHypotheses (8 : ℝ)] :
    2 * (chung8Tracking).ghat ≤ (chung8Setting).gainD (3/5) := by
  rw [chung8Setting_gainD_06, (chung8Filecoin (H := H)).ghat_eq, chung8Setting_gpi]
  exact two_gpi_le_gainD8_06

/-- the source condition plus concavity spread the certificate over the whole segment
`[σ, 3/5]`, which is exactly the hypothesis `growthPot_window` needs. -/
theorem chung8_midpoint_seg [H : ChungAnalyticHypotheses (8 : ℝ)] :
    ∀ x, (chung8Tracking).σ ≤ x → x ≤ (3 : ℝ)/5 →
      2 * (chung8Tracking).ghat ≤ (chung8Setting).gainD x :=
  fun _ hx hxc =>
    two_ghat_le_gainD_of_mem (chung8_midpoint (H := H)) (by norm_num) hx hxc

/-- The two-piece level count at the Filecoin Chung-8 parameters is below `3.961`; the
window constant it produces is one more than this, `Φ_{3/5}(π) + 1 < 4.961`. -/
theorem chung8_growthPot_lt [H : ChungAnalyticHypotheses (8 : ℝ)] :
    growthPot (chung8Setting) (chung8Tracking) (3/5) ((chung8Setting).pi)
      < (3961 : ℝ)/1000 := by
  have hcπ : (3 : ℝ)/5 ≤ (chung8Setting).pi := by
    rw [chung8Setting_pi]; norm_num
  have hg : (chung8Tracking).ghat = (chung8Setting).gpi :=
    (chung8Filecoin (H := H)).ghat_eq
  have hlow : (1113 : ℝ)/10000 < (chung8Setting).gpi := by
    rw [chung8Setting_gpi]; exact gpi8_bounds.1
  have hpos : 0 < (chung8Tracking).ghat := (chung8Tracking).ghat_pos
  rw [growthPot_pi hcπ, chung8Setting_pi, hg]
  change ((3 : ℝ)/5 - (74 : ℝ)/625) / (2 * (chung8Setting).gpi)
      + ((4 : ℝ)/5 - (3 : ℝ)/5) / (chung8Setting).gpi < (3961 : ℝ)/1000
  rw [hg] at hpos
  rw [div_add_div _ _ (by positivity) (ne_of_gt hpos), div_lt_iff₀ (by positivity)]
  nlinarith [hlow, hpos]

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

/-- The genuine Chung-8 threshold at `π`, as a real number with a certified bracket. -/
theorem beta8_pi_eq : chungBeta8 (4 / 5) = chungBeta 8 (4 / 5) :=
  chungBeta8_eq (by norm_num)

theorem beta8_pi_bounds :
    (94911 : ℝ) / 100000 < chungBeta8 (4 / 5) ∧ chungBeta8 (4 / 5) < (2966 : ℝ) / 3125 := by
  rw [beta8_pi_eq]
  exact ⟨beta_08_lower, beta_08_upper⟩

/-- The first bucket width is *exactly* `g_π`. -/
theorem chainX_one_sub_zero : chainX 1 - chainX 0 = gpi8 := by
  simp only [chainX_one, chainX_zero, gpi8, gainD8, beta8_pi_eq]
  ring

theorem chung8_ghat_eq [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Tracking).ghat = gpi8 := by
  rw [(chung8Filecoin (H := H)).ghat_eq, chung8Setting_gpi]

theorem chung8_lam_eq [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Tracking).lam = chainX 0 := by
  rw [(chung8Tracking).lam_eq_piBar (chung8_condB (H := H))]
  simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi, chainX_zero]

theorem chung8_betaD_eq [_H : ChungAnalyticHypotheses (8 : ℝ)] (t : ℝ) :
    (chung8Setting).betaD t = chungBeta8 t - 189 / 5000 := by
  simp only [Setting.betaD, chung8Setting_β, chung8Setting_delta]

/-- `β_δ(x₀) = x₁`, exactly: the mirror law, not a bracket. -/
theorem chung8_betaD_chainX_zero [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8Setting).betaD (chainX 0) = chainX 1 := by
  rw [chung8_betaD_eq, chainX_zero, chainX_one,
    chungBeta8_reversal (by norm_num : ((4 : ℝ) / 5) ∈ Ioo (0 : ℝ) 1)]
  norm_num

/-- **The Chung-8 reference chain.**  Every field is a theorem about the constructed
degree-eight curve: the head from the mirror law, the four steps from the brackets of
`ChungNumerics.lean`, and the widths from `g_π < 0.1114`. -/
noncomputable def chung8RefChain [H : ChungAnalyticHypotheses (8 : ℝ)] :
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
    · show gpi8 ≤ chainX 2 - chainX 1
      simp only [chainX_two, chainX_one]; linarith [gpi8_bounds.2]
    · show gpi8 ≤ chainX 3 - chainX 2
      simp only [chainX_three, chainX_two]; linarith [gpi8_bounds.2]
    · show gpi8 ≤ chainX 4 - chainX 3
      simp only [chainX_four, chainX_three]; linarith [gpi8_bounds.2]
  step := by
    intro k hk
    interval_cases k
    · rw [chung8_betaD_chainX_zero]
    · show chainX 2 ≤ _
      rw [chung8_betaD_eq, chainX_one, chainX_two,
        chungBeta8_eq (by norm_num : ((811 : ℝ) / 5000) ∈ Ioo (0 : ℝ) 1)]
      linarith [beta_1622_lower]
    · show chainX 3 ≤ _
      rw [chung8_betaD_eq, chainX_two, chainX_three,
        chungBeta8_eq (by norm_num : ((857 : ℝ) / 2000) ∈ Ioo (0 : ℝ) 1)]
      linarith [beta_4285_lower]
    · show chainX 4 ≤ _
      rw [chung8_betaD_eq, chainX_three, chainX_four,
        chungBeta8_eq (by norm_num : ((3669 : ℝ) / 5000) ∈ Ioo (0 : ℝ) 1)]
      linarith [beta_7338_lower]
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

@[simp] theorem chung8RefChain_x [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8RefChain).x = chainX := rfl

@[simp] theorem chung8RefChain_m [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8RefChain).m = 4 := rfl

/-- `β_δ(x₄) ≥ x_top`: the chord extension point of the top bucket. -/
theorem chung8_chainTop_le [H : ChungAnalyticHypotheses (8 : ℝ)] :
    chainTop ≤ (chung8Setting).betaD (chainX 4) := by
  rw [chung8_betaD_eq, chainX_four, chainTop,
    chungBeta8_eq (by norm_num : ((4443 : ℝ) / 5000) ∈ Ioo (0 : ℝ) 1)]
  linarith [beta_8886_lower]

/-! ### Evaluating the reference potential

`refPot` is affine on each bucket, so every certificate below is a finite case analysis
on which bucket a value lies in.  Only the first bucket has an irrational width — it is
exactly `ĝ = g_π` — and the two lemmas that touch it, `chainPot_ge_one_lip` and
`chainPot_low`, go through `refPot_lipschitz` rather than through an evaluation.
-/

theorem chainPot_one [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8RefChain).refPot (811 / 5000) = 1 := by
  have h := (chung8RefChain).refPot_x (j := 1) (by norm_num)
  simpa using h

theorem chainPot_three [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8RefChain).refPot (3669 / 5000) = 3 := by
  have h := (chung8RefChain).refPot_x (j := 3) (by norm_num)
  simpa using h

theorem chainPot_sat [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ} (ht : (4443 : ℝ) / 5000 ≤ t) :
    (chung8RefChain).refPot t = 4 := by
  have h := (chung8RefChain).refPot_eq_m (by simpa using ht)
  simpa using h

theorem chainPot_b1 [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (h1 : (811 : ℝ) / 5000 ≤ t) (h2 : t ≤ (857 : ℝ) / 2000) :
    (chung8RefChain).refPot t = 1 + (t - 811 / 5000) / (2663 / 10000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 1) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

theorem chainPot_b2 [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (h1 : (857 : ℝ) / 2000 ≤ t) (h2 : t ≤ (3669 : ℝ) / 5000) :
    (chung8RefChain).refPot t = 2 + (t - 857 / 2000) / (3053 / 10000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 2) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

theorem chainPot_b3 [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (h1 : (3669 : ℝ) / 5000 ≤ t) (h2 : t ≤ (4443 : ℝ) / 5000) :
    (chung8RefChain).refPot t = 3 + (t - 3669 / 5000) / (774 / 5000) := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 3) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  rw [h]
  norm_num

/-- The Lipschitz bound at the certificate's rational rate `1/ĝ < 10000/1113`. -/
theorem chainPot_lip [H : ChungAnalyticHypotheses (8 : ℝ)] {u v : ℝ} (huv : v ≤ u) :
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
theorem chainPot_hi_ub [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ} (ht : (811 : ℝ) / 5000 ≤ t) :
    (chung8RefChain).refPot t - (2250 / 557) * t
      ≤ 4 - (2250 / 557) * (4443 / 5000) := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 (H := H) ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 (H := H) h h2]; linarith
  rcases le_total t ((4443 : ℝ) / 5000) with h3 | h3
  · rw [chainPot_b3 (H := H) h2 h3]; linarith
  · rw [chainPot_sat (H := H) h3]; linarith

/-- …and, on `[x₁, x₄]`, smallest at `x₃`. -/
theorem chainPot_hi_lb [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (ht : (811 : ℝ) / 5000 ≤ t) (ht4 : t ≤ (4443 : ℝ) / 5000) :
    3 - (2250 / 557) * (3669 / 5000)
      ≤ (chung8RefChain).refPot t - (2250 / 557) * t := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 (H := H) ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 (H := H) h h2]; linarith
  · rw [chainPot_b3 (H := H) h2 ht4]; linarith

/-- Up to `t = 0.85` the potential has still not gained more than `A` per unit since
`x₁`.  The crossing point is `0.8614`, so `0.85` leaves room on both sides of the
modulus argument. -/
theorem chainPot_up_zero [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (ht : (811 : ℝ) / 5000 ≤ t) (ht2 : t ≤ 17 / 20) :
    (chung8RefChain).refPot t - 1 ≤ (2250 / 557) * (t - 811 / 5000) := by
  rcases le_total t ((857 : ℝ) / 2000) with h | h
  · rw [chainPot_b1 (H := H) ht h]; linarith
  rcases le_total t ((3669 : ℝ) / 5000) with h2 | h2
  · rw [chainPot_b2 (H := H) h h2]; linarith
  · rw [chainPot_b3 (H := H) h2 (by linarith)]; linarith

/-- Below `x₁` the potential is at most `10000/1113` per unit short of `1`. -/
theorem chainPot_down [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ} (ht : t ≤ (811 : ℝ) / 5000) :
    1 - (chung8RefChain).refPot t ≤ (10000 / 1113) * (811 / 5000 - t) := by
  have h := chainPot_lip (H := H) ht
  rw [chainPot_one (H := H)] at h
  linarith

/-- The same bound at the charge rate `A`, with the first bucket's own allowance
`1 - A ĝ ≤ 12263/22280`.  This is the tight certificate: the bucket is exactly `ĝ` wide
and carries exactly one level. -/
theorem chainPot_down_A [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ} (ht : t ≤ (811 : ℝ) / 5000) :
    1 - (chung8RefChain).refPot t
      ≤ (2250 / 557) * (811 / 5000 - t) + 12263 / 22280 := by
  rcases le_total ((811 : ℝ) / 5000 - t) (1113 / 10000) with h | h
  · have := chainPot_down (H := H) ht
    linarith
  · have := (chung8RefChain).refPot_nonneg t
    linarith

/-- The modulus, inside the first bucket. -/
theorem chainPot_low [H : ChungAnalyticHypotheses (8 : ℝ)] {u v : ℝ} (huv : v ≤ u)
    (hu : u ≤ (811 : ℝ) / 5000) :
    (chung8RefChain).refPot u - (chung8RefChain).refPot v
      ≤ (2250 / 557) * (u - v) + 12263 / 22280 := by
  rcases le_total (u - v) ((1113 : ℝ) / 10000) with h | h
  · have := chainPot_lip (H := H) huv
    linarith
  · have h1 : (chung8RefChain).refPot u ≤ 1 := by
      rw [← chainPot_one (H := H)]
      exact (chung8RefChain).refPot_mono hu
    have h2 := (chung8RefChain).refPot_nonneg v
    linarith

/-! ### The ledger certificate -/

/--
**The Chung-8 ledger certificate**, at charge rate `λ = 1.45` and saturation loss
`loss = 331/774 = 0.4276`, the exact value of `refPot π - 3`.

* `loss_ge` is monotonicity plus the evaluation of `refPot` at `π`;
* `t1` is the top-bucket chord of `RefChain.betaD_chord` with the extension point
  `x_top = 0.9333`: a step that stays infertile must spend more than
  `0.0886 + 0.0447 θ`, and `θ ĝ ≤ 0.45 · that` because `θ ≤ 0.4276 < 0.4367`;
* `modulus` is the case analysis of the five certificates above;
* `block_base` is `0.4276 ≤ 0.9`.
-/
noncomputable def chung8LedgerCert [H : ChungAnalyticHypotheses (8 : ℝ)] :
    LedgerCert (chung8Setting) (chung8Tracking) (chung8RefChain) where
  lam := 29 / 20
  loss := 331 / 774
  one_le_lam := by norm_num
  loss_nonneg := by norm_num
  block_base := by norm_num
  loss_ge := by
    intro v _ hv
    rw [chung8Setting_pi] at hv
    have hm : ((chung8RefChain).m : ℝ) - 1 = 3 := by norm_num [chung8RefChain_m]
    rw [hm]
    have hpi : (chung8RefChain).refPot (4 / 5) = 3 + 331 / 774 := by
      rw [chainPot_b3 (H := H) (t := 4 / 5) (by norm_num) (by norm_num)]; norm_num
    have hmono : (chung8RefChain).refPot v ≤ (chung8RefChain).refPot (4 / 5) :=
      (chung8RefChain).refPot_mono hv
    rw [hpi] at hmono
    linarith
  t1 := by
    intro v s _ hv hs hbeta
    rw [chung8Setting_pi] at hv hbeta
    rw [chung8_ghat_eq]
    have hm : ((chung8RefChain).m : ℝ) - 1 = 3 := by norm_num [chung8RefChain_m]
    rw [hm]
    rcases le_total v ((3669 : ℝ) / 5000) with hlow | hhigh
    · have hmono : (chung8RefChain).refPot v ≤ 3 := by
        rw [← chainPot_three (H := H)]
        exact (chung8RefChain).refPot_mono hlow
      nlinarith [gpi8_bounds.1]
    · have hv4 : v ≤ (4443 : ℝ) / 5000 := by linarith
      have hpot : (chung8RefChain).refPot v - 3 = (5000 / 774) * (v - 3669 / 5000) := by
        rw [chainPot_b3 (H := H) hhigh hv4]; ring
      -- the top-bucket chord, extended to `x_top = 0.9333`
      have hchord : (4443 : ℝ) / 5000 + (149 / 516) * (v - 3669 / 5000)
          ≤ (chung8Setting).betaD v := by
        have h := (chung8RefChain).betaD_chord (k := 3) (by norm_num)
          (chung8_chainTop_le (H := H)) (show (chung8RefChain).x 3 ≤ v by simpa using hhigh)
          (show v ≤ (chung8RefChain).x (3 + 1) by simpa using hv4)
        have e1 : (chung8RefChain).x 3 = (3669 : ℝ) / 5000 := rfl
        have e2 : (chung8RefChain).x (3 + 1) = (4443 : ℝ) / 5000 := rfl
        rw [e1, e2] at h
        simp only [chainTop] at h
        calc (4443 : ℝ) / 5000 + (149 / 516) * (v - 3669 / 5000)
            = (4443 : ℝ) / 5000 + (v - 3669 / 5000) / ((4443 : ℝ) / 5000 - 3669 / 5000)
                * ((9333 : ℝ) / 10000 - 4443 / 5000) := by ring
          _ ≤ (chung8Setting).betaD v := h
      rw [hpot]
      have hprod : (5000 / 774 : ℝ) * (v - 3669 / 5000) * gpi8
          ≤ (5000 / 774 : ℝ) * (v - 3669 / 5000) * (557 / 5000) :=
        mul_le_mul_of_nonneg_left gpi8_bounds.2.le (by linarith)
      linarith
  modulus := by
    intro u v huv hρ
    rw [chung8Setting_rho] at hρ
    rw [chung8_ghat_eq]
    -- charge at the rational rate `A = 2250/557 ≤ (λ-1)/ĝ`
    have hArate : (2250 / 557 : ℝ) * (u - v) ≤ (29 / 20 - 1) * (u - v) / gpi8 := by
      have hnn : (0 : ℝ) ≤ (29 / 20 - 1) * (u - v) := by
        have : (0 : ℝ) ≤ u - v := by linarith
        nlinarith
      have hd : ((29 / 20 - 1) * (u - v)) / (557 / 5000 : ℝ)
          ≤ ((29 / 20 - 1) * (u - v)) / gpi8 :=
        div_le_div_of_nonneg_left hnn (by linarith [gpi8_bounds.1]) gpi8_bounds.2.le
      have hval : ((29 / 20 - 1) * (u - v)) / (557 / 5000 : ℝ)
          = (2250 / 557 : ℝ) * (u - v) := by ring
      linarith [hval ▸ hd]
    suffices hmain : (chung8RefChain).refPot u - (chung8RefChain).refPot v
        ≤ (2250 / 557) * (u - v) + (1 - 331 / 774) by
      have hgoal : (29 / 20 - 1) * (u - v) / gpi8 + (1 - 331 / 774)
          ≥ (2250 / 557) * (u - v) + (1 - 331 / 774) := by linarith
      linarith
    rcases le_total u ((811 : ℝ) / 5000) with hu1 | hu1
    · have := chainPot_low (H := H) huv hu1
      linarith
    rcases le_total ((811 : ℝ) / 5000) v with hv1 | hv1
    · -- both above `x₁`
      rcases le_total ((4443 : ℝ) / 5000) v with hv4 | hv4
      · rw [chainPot_sat (H := H) hv4, chainPot_sat (H := H) (le_trans hv4 huv)]
        linarith
      · have h1 := chainPot_hi_ub (H := H) (le_trans hv1 huv)
        have h2 := chainPot_hi_lb (H := H) hv1 hv4
        linarith
    · -- the crossing case
      have hdown := chainPot_down (H := H) hv1
      rcases le_total u ((17 : ℝ) / 20) with hu2 | hu2
      · have hup := chainPot_up_zero (H := H) hu1 hu2
        have hdA := chainPot_down_A (H := H) hv1
        linarith
      · rcases le_total ((4443 : ℝ) / 5000) u with hu4 | hu4
        · rw [chainPot_sat (H := H) hu4]
          linarith
        · rw [chainPot_b3 (H := H) (by linarith) hu4]
          linarith

/-! ### The two-link threshold at `ℓ = 15`

The potential ledger's chain-length condition is

  `potHead + (z - 1) potSpan + λ ρ / ĝ < ℓ`,

and at the Chung-8 Filecoin parameters its three terms are `0.5982`, `3.8212` and
`10.4223`.  Their sum `14.8417` is below `15`, so `ℓ = 15` certifies two links.  The
The source weight is `σ = 74/625`, so two links give payoff `0.2816 n`.
-/

@[simp] theorem chung8LedgerCert_lam [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8LedgerCert).lam = 29 / 20 := rfl

@[simp] theorem chung8LedgerCert_loss [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8LedgerCert).loss = 331 / 774 := rfl

/-- The first bucket, whose width is exactly `ĝ`. -/
theorem chainPot_b0 [H : ChungAnalyticHypotheses (8 : ℝ)] {t : ℝ}
    (h1 : chainX 0 ≤ t) (h2 : t ≤ (811 : ℝ) / 5000) :
    (chung8RefChain).refPot t = (t - chainX 0) / gpi8 := by
  have h := (chung8RefChain).refPot_eq_of_mem (j := 0) (by norm_num)
    (by simpa using h1) (by simpa using h2)
  have e1 : (chung8RefChain).x (0 + 1) - (chung8RefChain).x 0 = gpi8 :=
    chainX_one_sub_zero
  have e0 : (chung8RefChain).x 0 = chainX 0 := rfl
  rw [h, e1, e0]
  norm_num

/-- `refPot σ > 0.60646`: the source starts a fifth of the way up the first bucket, and
that is the only place the potential of the growth phase is charged. -/
theorem chainPot_sigma_gt [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (675 : ℝ) / 1113 < (chung8RefChain).refPot (74 / 625) := by
  have hx0 : chainX 0 = 811 / 5000 - gpi8 := by
    have h := chainX_one_sub_zero
    simp only [chainX_one] at h
    linarith
  have hlo : chainX 0 ≤ (74 : ℝ) / 625 := by
    rw [chainX_zero]
    linarith [beta8_pi_bounds.1]
  rw [chainPot_b0 (H := H) hlo (by norm_num), hx0]
  rw [lt_div_iff₀ (by linarith [gpi8_bounds.1] : (0 : ℝ) < gpi8)]
  linarith [gpi8_bounds.1]

theorem chung8_potHead_eq [H : ChungAnalyticHypotheses (8 : ℝ)] :
    LedgerCert.potHead (chung8RefChain) (chung8LedgerCert) = 463 / 774 := by
  have hζ : (chung8RefChain).refPot (4311 / 5000) = 3 + 642 / 774 := by
    rw [chainPot_b3 (H := H) (t := 4311 / 5000) (by norm_num) (by norm_num)]; norm_num
  simp only [LedgerCert.potHead, chung8Setting_zetaDelta, chung8RefChain_m,
    chung8LedgerCert_loss, hζ]
  norm_num

theorem chung8_potSpan_lt [H : ChungAnalyticHypotheses (8 : ℝ)] :
    LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert)
      < 4 - 675 / 1113 + 331 / 774 := by
  have h := chainPot_sigma_gt (H := H)
  simp only [LedgerCert.potSpan, chung8Tracking_sigma, chung8RefChain_m,
    chung8LedgerCert_loss]
  norm_num
  linarith

theorem chung8_ledgerCharge_lt [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat
      < 11600 / 1113 := by
  rw [chung8LedgerCert_lam, chung8Setting_rho, chung8_ghat_eq]
  rw [div_lt_iff₀ (by linarith [gpi8_bounds.1] : (0 : ℝ) < gpi8)]
  linarith [gpi8_bounds.1]

/-- **The two-link threshold of the potential ledger, evaluated.**  `14.8417 < 15`. -/
theorem chung8_potential_threshold [H : ChungAnalyticHypotheses (8 : ℝ)] :
    LedgerCert.potHead (chung8RefChain) (chung8LedgerCert)
        + (((2 : ℕ) : ℝ) - 1) * LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert)
        + (chung8LedgerCert).lam * (chung8Setting).ρ / (chung8Tracking).ghat
      < ((15 : ℕ) : ℝ) := by
  have h1 := chung8_potHead_eq (H := H)
  have h2 := chung8_potSpan_lt (H := H)
  have h3 := chung8_ledgerCharge_lt (H := H)
  push_cast
  linarith

/--
**Two chain links at `ℓ = 15`, at the full `0.2816 n` payoff.**

No reference chain appears among the theorem's hypotheses; it is supplied here, and its
conditions are the `ChungNumerics` brackets for the constructed curve.  The potential
ledger charges the black budget once at `λ/ĝ`, with `λ = 1.45`, and has per-link span
`potSpan = 3.82`.  The source weight is `σ = 74/625`.
-/
theorem chung8_latency_15 [H : ChungAnalyticHypotheses (8 : ℝ)]
    {V : Type u} {n : ℕ}
    (G : Concrete.LayeredGraph V (chung8Setting) 15 n)
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
    (chung8_zeta_le (H := H)) (chung8_entry (H := H)) (chung8_nobreak (H := H)) (z := 2) (by norm_num)
    (chung8_potential_threshold (H := H)) A hA hred hweight
  have hlen : latencyLength G.αpi (chung8Tracking).σ n 2
      = (1 : ℝ) / 5 * n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n := by
    simp only [latencyLength, hαpi, chung8Tracking_sigma]
    push_cast
    ring
  rwa [hlen] at h


/-! ### Potential-ledger constants

The potential ledger charges `potHead + λρ/ĝ = 11.02` levels once and
`potSpan = 3.82` per link.
-/

theorem chung8_potSpan_gt [H : ChungAnalyticHypotheses (8 : ℝ)] :
    4 - 338 / 557 + 331 / 774
      < LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) := by
  have hlo : chainX 0 ≤ (74 : ℝ) / 625 := by
    rw [chainX_zero]; linarith [beta8_pi_bounds.1]
  have hx0 : chainX 0 = 811 / 5000 - gpi8 := by
    have h := chainX_one_sub_zero
    simp only [chainX_one] at h
    linarith
  have hpot : (chung8RefChain).refPot (74 / 625) < 338 / 557 := by
    rw [chainPot_b0 (H := H) hlo (by norm_num), hx0]
    rw [div_lt_iff₀ (by linarith [gpi8_bounds.1] : (0 : ℝ) < gpi8)]
    linarith [gpi8_bounds.2]
  simp only [LedgerCert.potSpan, chung8Tracking_sigma, chung8RefChain_m,
    chung8LedgerCert_loss]
  norm_num
  linarith

theorem chung8_potSpan_pos [H : ChungAnalyticHypotheses (8 : ℝ)] :
    0 < LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) := by
  have := chung8_potSpan_gt (H := H)
  norm_num at this
  linarith

/-- **The per-link span, evaluated:** `3.8208 < potSpan < 3.8212`. -/
theorem chung8_potSpan_bounds [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (38208 : ℝ) / 10000 < LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) ∧
      LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) < (38212 : ℝ) / 10000 := by
  have h1 := chung8_potSpan_gt (H := H)
  have h2 := chung8_potSpan_lt (H := H)
  constructor <;> [linarith; linarith]

/-- **The certified asymptotic slope of the potential ledger**, one link per `potSpan`
levels: `(α_π - σ)/potSpan ∈ (0.02135, 0.02136)`. -/
theorem chung8_potential_slope_bounds [H : ChungAnalyticHypotheses (8 : ℝ)] :
    (2135 : ℝ) / 100000 <
        ((1 : ℝ) / 5 - (74 : ℝ) / 625)
          / LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert) ∧
      ((1 : ℝ) / 5 - (74 : ℝ) / 625)
          / LedgerCert.potSpan (chung8RefChain) (chung8LedgerCert)
        < (2136 : ℝ) / 100000 := by
  have hb := chung8_potSpan_bounds (H := H)
  have hpos := chung8_potSpan_pos (H := H)
  constructor
  · rw [lt_div_iff₀ hpos]; linarith [hb.2]
  · rw [div_lt_iff₀ hpos]; linarith [hb.1]

end ChungCurve
end ProofOfSpace

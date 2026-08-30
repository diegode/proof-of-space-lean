/-
# The tracking parameters `π̂` and `ĝ`

This file formalizes `eq:tracking` and the uniform bound `eq:tracking-gain` of
`docs/explanation.tex`:

  `π̂ := min {π̄, σ, 1 - β σ}`,  `ĝ := min {g_π, gain_δ(σ)/2}`,

`π̂` is built here in two steps, through the auxiliary `σ̂ := min {σ, 1 - β σ}`, so
that `π̂ = min {π̄, σ̂}`.  The explanatory note writes the three-way minimum directly;
`σ̂` has no separate name there.  The Lean declaration implementing `π̂` is
`Tracking.lam`.

together with

  `gain_δ(x) ≥ ĝ`   for `π̂ ≤ x ≤ π`.

The point of `σ̂` is that `1 - β σ` is the mirror partner of `σ`, so it carries the *same*
gain (the mirror identity of `eq:reversal`, proved in `Expansion.lean` from the
Chung reversal law of
`Chung.lean`).  Consequently the gain at `π̂` is bounded below without any assumption on
which side of the gain peak `σ` lies.

The last two results specialize under the source-gain inequality
`gain_δ(σ) ≥ 2 g_π` from `eq:no-break-conditions`: it forces `ĝ = g_π` and `π̂ = π̄`,
so that `ĝ`-expandability is
exactly the `g_π`-expandability of the base-case analysis.
-/
import ProofOfSpace.Footprint

namespace ProofOfSpace

open Set

/-- A source weight `σ` strictly inside the active interval and below the fertility
threshold, as fixed in `sec:footprint-proof`. -/
structure Tracking (S : Setting) where
  /-- The weight of the tracked source set. -/
  σ : ℝ
  /-- `σ > α_δ^min`. -/
  σ_gt : S.αmin < σ
  /-- `σ < π`. -/
  σ_lt : σ < S.pi
  /-- A *doubled-gain mid-point* `σ̃ ∈ [σ, π]`: a right endpoint up to which the source
  condition `gain_δ(σ) ≥ 2 ĝ` still holds.  Concavity then spreads it over the whole
  segment `[σ, σ̃]` (`two_ghat_le_gainD_of_mem`), and `growthPot` charges that segment at
  half price.  Taking `mid := σ` is always admissible and recovers the single-constant
  growth count, so this field is data the instantiation may leave trivial. -/
  mid : ℝ
  /-- `σ ≤ σ̃`. -/
  mid_ge : σ ≤ mid
  /-- `σ̃ ≤ π`. -/
  mid_le : mid ≤ S.pi
  /-- `2 ĝ ≤ gain_δ(σ̃)`, spelled out because `ĝ` is defined only after the structure. -/
  mid_gain : 2 * min S.gpi (S.gainD σ / 2) ≤ S.gainD mid

namespace Tracking

variable {S : Setting} (T : Tracking S)

/-- `σ̂ = min{σ, 1 - β(σ)}`: the smaller member of the equal-gain mirror pair. -/
noncomputable def sigmaHat : ℝ := min T.σ (1 - S.β T.σ)

/-- `π̂ = min{π̄, σ̂}`: the tracking floor of `lem:mirror-floor`. -/
noncomputable def lam : ℝ := min S.piBar T.sigmaHat

/-- `ĝ = min{g_π, gain_δ(σ)/2}`: the tracking gain. -/
noncomputable def ghat : ℝ := min S.gpi (S.gainD T.σ / 2)

theorem σ_pos : 0 < T.σ := lt_of_le_of_lt S.αmin_nonneg T.σ_gt

theorem σ_lt_one : T.σ < 1 := T.σ_lt.trans S.pi_mem.2

theorem σ_mem : T.σ ∈ Ioo (0:ℝ) 1 := ⟨T.σ_pos, T.σ_lt_one⟩

theorem σ_mem_Icc : T.σ ∈ Icc (0:ℝ) 1 := ⟨T.σ_pos.le, T.σ_lt_one.le⟩

theorem σ_lt_αmax : T.σ < S.αmax := T.σ_lt.trans S.pi_lt_αmax

/-- The tracked source has strictly positive gain: it lies strictly inside
`[α_δ^min, α_δ^max]`. -/
theorem gainD_σ_pos : 0 < S.gainD T.σ := S.gainD_pos ⟨T.σ_gt, T.σ_lt_αmax⟩

/-! ### `σ̂` -/

theorem sigmaHat_le_σ : T.sigmaHat ≤ T.σ := min_le_left _ _

theorem sigmaHat_pos : 0 < T.sigmaHat :=
  lt_min T.σ_pos (by have := S.β_lt_one T.σ_pos.le T.σ_lt_one; linarith)

theorem sigmaHat_lt_one : T.sigmaHat < 1 := lt_of_le_of_lt T.sigmaHat_le_σ T.σ_lt_one

theorem sigmaHat_mem_Icc : T.sigmaHat ∈ Icc (0:ℝ) 1 :=
  ⟨T.sigmaHat_pos.le, T.sigmaHat_lt_one.le⟩

/-- **The equal-gain property of the mirror pair.**  `σ̂` has the same gain as `σ`; this is
the mirror identity of `eq:reversal` applied to whichever of the two points realizes
the minimum. -/
theorem gainD_sigmaHat : S.gainD T.sigmaHat = S.gainD T.σ := by
  rcases min_cases T.σ (1 - S.β T.σ) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [sigmaHat, h]
  · rw [sigmaHat, h]; exact S.gainD_mirror T.σ_mem

/-! ### `ĝ` -/

theorem ghat_le_gpi : T.ghat ≤ S.gpi := min_le_left _ _

theorem two_ghat_le_gainD_σ : 2 * T.ghat ≤ S.gainD T.σ := by
  have : T.ghat ≤ S.gainD T.σ / 2 := min_le_right _ _
  linarith

theorem ghat_pos : 0 < T.ghat := lt_min S.gpi_pos (by linarith [T.gainD_σ_pos])

theorem ghat_nonneg : 0 ≤ T.ghat := T.ghat_pos.le

/-! ### the doubled-gain mid-point `σ̃` -/

/-- The mid-point certificate, in terms of `ĝ`.  This is `mid_gain`, whose statement
spells `ĝ` out because the structure cannot mention it. -/
theorem two_ghat_le_gainD_mid : 2 * T.ghat ≤ S.gainD T.mid := T.mid_gain

theorem σ_le_mid : T.σ ≤ T.mid := T.mid_ge

theorem mid_lt_one : T.mid < 1 := lt_of_le_of_lt T.mid_le S.pi_mem.2

theorem mid_mem_Icc : T.mid ∈ Icc (0:ℝ) 1 :=
  ⟨le_trans T.σ_pos.le T.mid_ge, T.mid_lt_one.le⟩

/-! ### `π̂` -/

theorem lam_le_piBar : T.lam ≤ S.piBar := min_le_left _ _

theorem lam_le_sigmaHat : T.lam ≤ T.sigmaHat := min_le_right _ _

theorem lam_le_σ : T.lam ≤ T.σ := T.lam_le_sigmaHat.trans T.sigmaHat_le_σ

theorem lam_pos : 0 < T.lam := lt_min S.piBar_pos T.sigmaHat_pos

theorem lam_lt_pi : T.lam < S.pi := lt_of_le_of_lt T.lam_le_piBar S.piBar_lt_pi

theorem lam_mem_Icc : T.lam ∈ Icc (0:ℝ) 1 :=
  ⟨T.lam_pos.le, le_of_lt (T.lam_lt_pi.trans S.pi_mem.2)⟩

theorem αmin_lt_sigmaHat : S.αmin < T.sigmaHat := by
  by_contra hcon
  push_neg at hcon
  have h := S.gainD_nonpos_of_le_αmin T.sigmaHat_mem_Icc hcon
  rw [T.gainD_sigmaHat] at h
  linarith [T.gainD_σ_pos]

theorem αmin_lt_lam : S.αmin < T.lam := lt_min S.αmin_lt_piBar T.αmin_lt_sigmaHat

/-- **`eq:tracking-gain`.**  The gain at the tracking floor is at least `ĝ`. -/
theorem ghat_le_gainD_lam : T.ghat ≤ S.gainD T.lam := by
  rcases min_cases S.piBar T.sigmaHat with ⟨h, _⟩ | ⟨h, _⟩
  · rw [lam, h, S.gainD_piBar]; exact T.ghat_le_gpi
  · rw [lam, h, T.gainD_sigmaHat]
    linarith [T.two_ghat_le_gainD_σ, T.ghat_nonneg]

/-- **`eq:tracking-gain`.**  `gain_δ ≥ ĝ` throughout `[π̂, π]`. -/
theorem ghat_le_gainD {x : ℝ} (hx : x ∈ Icc T.lam S.pi) : T.ghat ≤ S.gainD x := by
  have h := S.gainD_concaveOn.min_le_of_mem_Icc T.lam_mem_Icc S.pi_mem_Icc hx
  have hlam := T.ghat_le_gainD_lam
  have hpi : T.ghat ≤ S.gainD S.pi := T.ghat_le_gpi
  exact le_trans (le_min hlam hpi) h

/-! ### the source condition `gain_δ(σ) ≥ 2 g_π` -/

variable (hb : 2 * S.gpi ≤ S.gainD T.σ)

include hb in
/-- Under `gain_δ(σ) ≥ 2 g_π` the tracking gain is exactly `g_π`. -/
theorem ghat_eq_gpi : T.ghat = S.gpi := min_eq_left (by linarith)

include hb in
/-- Under `gain_δ(σ) ≥ 2 g_π` the equal-gain pair lies inside the `g_π` superlevel interval,
so the tracking floor is exactly `π̄`. -/
theorem lam_eq_piBar : T.lam = S.piBar := by
  refine min_eq_left ?_
  by_contra hcon
  push_neg at hcon
  have h1 : S.gainD T.sigmaHat ≤ S.gpi :=
    S.gainD_le_gpi_of_lt_piBar T.sigmaHat_mem_Icc hcon
  rw [T.gainD_sigmaHat] at h1
  linarith [S.gpi_pos']

end Tracking

end ProofOfSpace

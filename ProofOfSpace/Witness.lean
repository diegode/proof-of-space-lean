import ProofOfSpace.Latency

/-!
# A consistency witness for the hypothesis stack

This file is **not** the development's specialization; `ChungFilecoin.lean` is, on the genuine
degree-eight Chung curve.  What this file does is exhibit a closed model of the whole
hypothesis stack, so that the structures the development quantifies over are known to be
inhabited and its theorems are not vacuous.

It defines the Möbius expander

  `β(x) = 2916 x / (625 + 2291 x)`,

the member `((k+1)x)/(1+kx)` of the Möbius family at `k = 2291/625`, and proves every
field of `Setting`, `GeneralRegime`, and `FilecoinLatencyParameters` for it at
`σ = 0.1184`, ending in `wSetting`, `wGeneralRegime`, and `wFilecoin`.  Strict
concavity and the unique gain maximizer are theorems here, which is exactly why the
model closes. The finite-size Chung-8 specialization now proves those facts directly
for its rational polygon; for the exact Chung root at a general degree they remain
unproved, which is why no `Setting` is built from that root.

The Möbius family is the natural place to look for a model because the reversal law
`reversal identity` `β(1 - β x) = 1 - x` says exactly that `x ↦ 1 - β x` is an involution,
and `x ↦ (1-x)/(1+kx)` is one for every `k`.

This curve is not a profile the development claims for any construction: at `k = 2291/625` it
runs above the degree-eight Chung boundary, so the degree-eight union bound does not
certify it.  Read it as a consistency proof, never as an expansion certificate.
-/

namespace ProofOfSpace
namespace Witness

open Set

universe u

/-! ### The Möbius expansion function -/

/-- `β(x) = 2916 x / (625 + 2291 x)`, the Möbius expander with `k = 2291/625`. -/
noncomputable def mbeta (x : ℝ) : ℝ := 2916 * x / (625 + 2291 * x)

theorem den_pos {x : ℝ} (hx : 0 ≤ x) : (0 : ℝ) < 625 + 2291 * x := by linarith

theorem mbeta_maps {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : mbeta x ∈ Icc (0:ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hd := den_pos hx0
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [mbeta, div_le_one hd]; linarith

theorem mbeta_strictMonoOn : StrictMonoOn mbeta (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hdx := den_pos hx.1
  have hdy := den_pos hy.1
  rw [mbeta, mbeta, div_lt_div_iff₀ hdx hdy]
  nlinarith

/-- `β(x) - x = 2291 x (1 - x) / (625 + 2291 x)`. -/
theorem mbeta_sub_self {x : ℝ} (hx : 0 ≤ x) :
    mbeta x - x = 2291 * x * (1 - x) / (625 + 2291 * x) := by
  have hd := den_pos hx
  simp only [mbeta]
  field_simp
  ring

theorem mbeta_expands {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : x < mbeta x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hd := den_pos hx0.le
  have h : 0 < 2291 * x * (1 - x) / (625 + 2291 * x) := by
    apply div_pos _ hd; nlinarith
  have hsub := mbeta_sub_self hx0.le
  linarith

/-- `1 - β(x) = 625 (1 - x) / (625 + 2291 x)`, the mirror map. -/
theorem one_sub_mbeta {x : ℝ} (hx : 0 ≤ x) :
    1 - mbeta x = 625 * (1 - x) / (625 + 2291 * x) := by
  have hd := den_pos hx
  simp only [mbeta]
  field_simp
  ring

/-- **`reversal identity`**: `x ↦ 1 - β x` is an involution. -/
theorem mbeta_reversal {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    mbeta (1 - mbeta x) = 1 - x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hd := den_pos hx0.le
  have hmir := one_sub_mbeta hx0.le
  rw [hmir, mbeta]
  rw [div_eq_iff (by positivity)]
  field_simp
  ring

/-! ### Concavity -/

/-- One concavity step for the Möbius curve.  After clearing denominators the
inequality is exactly `1431875 · a b (x - y)² ≥ 0`. -/
theorem mobius_concave_step {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * mbeta x + b * mbeta y ≤ mbeta (a * x + b * y) := by
  have hu := den_pos hx
  have hv := den_pos hy
  have hxy : (0:ℝ) ≤ a * x + b * y := by
    have h1 := mul_nonneg ha hx
    have h2 := mul_nonneg hb hy
    linarith
  have hw := den_pos hxy
  have hb1 : b = 1 - a := by linarith
  subst hb1
  simp only [mbeta]
  rw [← mul_div_assoc, ← mul_div_assoc, div_add_div _ _ (ne_of_gt hu) (ne_of_gt hv),
    div_le_div_iff₀ (by positivity) hw]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y)),
    mul_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))) hx,
    mul_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))) hy]

theorem mbeta_concaveOn : ConcaveOn ℝ (Icc (0:ℝ) 1) mbeta := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [smul_eq_mul] using mobius_concave_step hx.1 hy.1 ha hb hab

/-- The Möbius profile is in fact strictly concave. -/
theorem mbeta_strictConcaveOn : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) mbeta := by
  refine LinearOrder.strictConcaveOn_of_lt (convex_Icc 0 1) ?_
  intro x hx y hy hxy a b ha hb hab
  have hdx := den_pos hx.1
  have hdy := den_pos hy.1
  have hxy0 : (0 : ℝ) ≤ a * x + b * y :=
    add_nonneg (mul_nonneg ha.le hx.1) (mul_nonneg hb.le hy.1)
  have hdxy := den_pos hxy0
  have hb1 : b = 1 - a := by linarith
  have hsq : 0 < (x - y) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hxy))
  subst hb1
  simp only [smul_eq_mul, mbeta]
  rw [← mul_div_assoc, ← mul_div_assoc,
    div_add_div _ _ (ne_of_gt hdx) (ne_of_gt hdy),
    div_lt_div_iff₀ (by positivity) hdxy]
  nlinarith [mul_pos (mul_pos ha hb) hsq,
    mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hsq.le) hx.1,
    mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) hsq.le) hy.1]

/-! ### The unique maximiser -/

theorem mbeta_alphag : mbeta (25 / 79) = 54 / 79 := by
  rw [mbeta]; norm_num

/-- The exact gain identity `gain(α_g) - gain(x) = k (x - α_g)² / (1 + k x)`. -/
theorem gain_gap {x : ℝ} (hx : 0 ≤ x) :
    29 / 79 - (mbeta x - x) = 2291 * (x - 25 / 79) ^ 2 / (625 + 2291 * x) := by
  have hd := den_pos hx
  simp only [mbeta]
  field_simp
  ring

theorem mbeta_alphag_max {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hne : x ≠ 25 / 79) :
    mbeta x - x < mbeta (25 / 79) - 25 / 79 := by
  have hd := den_pos hx.1
  have hne' : x - 25 / 79 ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (x - 25 / 79) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne'))
  have hpos : 0 < 2291 * (x - 25 / 79) ^ 2 / (625 + 2291 * x) := by
    apply div_pos _ hd; linarith
  have hgap := gain_gap hx.1
  have hval : mbeta (25 / 79) - 25 / 79 = 29 / 79 := by rw [mbeta_alphag]; norm_num
  rw [hval]
  linarith

/-! ### The roots of `gain_δ = 0`

`gain_δ(x) = 0` is, after clearing the denominator of `β`, the quadratic
`x² - (4811/5000) x + 189/18328 = 0`, whose discriminant is `disc`. -/

/-- `(4811/5000)² - 4 · 189/18328`. -/
noncomputable def disc : ℝ := 50664346811 / 57275000000

/-- `α_δ^min`, the smaller root. -/
noncomputable def amin : ℝ := (4811 / 5000 - Real.sqrt disc) / 2

/-- `α_δ^max`, the larger root. -/
noncomputable def amax : ℝ := (4811 / 5000 + Real.sqrt disc) / 2

theorem sqrt_disc_sq : Real.sqrt disc ^ 2 = 50664346811 / 57275000000 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ disc by norm_num [disc])
  simpa only [disc] using h

theorem sqrt_disc_le : Real.sqrt disc ≤ 4811 / 5000 := by
  have h : Real.sqrt disc ≤ Real.sqrt ((4811 / 5000 : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num [disc])
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4811 / 5000)] at h

theorem sqrt_disc_ge : (3811 : ℝ) / 5000 ≤ Real.sqrt disc := by
  have h : Real.sqrt ((3811 / 5000 : ℝ) ^ 2) ≤ Real.sqrt disc :=
    Real.sqrt_le_sqrt (by norm_num [disc])
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3811 / 5000)] at h

/-- A root of the quadratic is a zero of `gain_δ`. -/
theorem gainD_root {x : ℝ} (hx : 0 ≤ x)
    (h : x ^ 2 - (4811 / 5000) * x + 189 / 18328 = 0) :
    mbeta x - 189 / 5000 - x = 0 := by
  have hd := den_pos hx
  have key : mbeta x - 189 / 5000 - x
      = -2291 * (x ^ 2 - (4811 / 5000) * x + 189 / 18328) / (625 + 2291 * x) := by
    simp only [mbeta]; field_simp; ring
  rw [key, h]
  simp

theorem amin_root : amin ^ 2 - (4811 / 5000) * amin + 189 / 18328 = 0 := by
  simp only [amin]
  linear_combination (1 / 4 : ℝ) * sqrt_disc_sq

theorem amax_root : amax ^ 2 - (4811 / 5000) * amax + 189 / 18328 = 0 := by
  simp only [amax]
  linear_combination (1 / 4 : ℝ) * sqrt_disc_sq

theorem amin_nonneg : 0 ≤ amin := by
  simp only [amin]; linarith [sqrt_disc_le]

theorem amin_le_alphag : amin ≤ 25 / 79 := by
  simp only [amin]; linarith [sqrt_disc_ge]

theorem amin_lt_sigma : amin < 74 / 625 := by
  simp only [amin]; linarith [sqrt_disc_ge]

theorem alphag_le_amax : (25 : ℝ) / 79 ≤ amax := by
  simp only [amax]; linarith [sqrt_disc_ge]

theorem amax_le_one : amax ≤ 1 := by
  simp only [amax]; linarith [sqrt_disc_le]

theorem zeta_le_amax : (4311 : ℝ) / 5000 ≤ amax := by
  simp only [amax]; linarith [sqrt_disc_ge]

theorem amax_nonneg : 0 ≤ amax := le_trans (by norm_num) alphag_le_amax

/-! ### The witness `Setting` -/

/-- The Möbius `Setting` carrying the Filecoin numerical certificates. -/
noncomputable def wSetting : Setting where
  β := mbeta
  αg := 25 / 79
  δ := 189 / 5000
  pi := 4 / 5
  ρ := 4 / 5
  ζδ := 4311 / 5000
  αmin := amin
  αmax := amax
  β_maps := fun _ hx => mbeta_maps hx
  β_zero := by norm_num [mbeta]
  β_strictMonoOn := mbeta_strictMonoOn
  β_concaveOn := mbeta_concaveOn
  β_expands := fun _ hx => mbeta_expands hx
  β_reversal := fun _ hx => mbeta_reversal hx
  αg_mem := by norm_num
  αg_max := fun _ hx hne => mbeta_alphag_max hx hne
  δ_nonneg := by norm_num
  ρ_nonneg := by norm_num
  pi_mem := by norm_num
  αg_lt_pi := by norm_num
  gpi_pos := by norm_num [mbeta]
  αmin_mem := ⟨amin_nonneg, amin_le_alphag⟩
  αmax_mem := ⟨alphag_le_amax, amax_le_one⟩
  gainD_αmin := gainD_root amin_nonneg amin_root
  gainD_αmax := gainD_root amax_nonneg amax_root

@[simp] theorem wSetting_β : wSetting.β = mbeta := rfl
@[simp] theorem wSetting_δ : wSetting.δ = 189 / 5000 := rfl
@[simp] theorem wSetting_pi : wSetting.pi = 4 / 5 := rfl
@[simp] theorem wSetting_ρ : wSetting.ρ = 4 / 5 := rfl
@[simp] theorem wSetting_ζδ : wSetting.ζδ = 4311 / 5000 := rfl
@[simp] theorem wSetting_αmin : wSetting.αmin = amin := rfl
@[simp] theorem wSetting_αmax : wSetting.αmax = amax := rfl

/-- `g_π = 6841379/61445000 ≈ 0.11134151` (Chung-8 gives `0.11131`). -/
theorem wSetting_gpi : wSetting.gpi = 6841379 / 61445000 := by
  simp only [Setting.gpi, Setting.gainD, wSetting_β, wSetting_δ, wSetting_pi]
  norm_num [mbeta]

/-- `π̄ = 625/12289 ≈ 0.05085849` (Chung-8 gives `0.050889`). -/
theorem wSetting_piBar : wSetting.piBar = 625 / 12289 := by
  simp only [Setting.piBar, wSetting_β, wSetting_pi]
  norm_num [mbeta]

/-- The development's selected source weight `σ = 0.1184` for this auxiliary witness. -/
noncomputable def wTracking : Tracking wSetting where
  σ := 74 / 625
  σ_gt := by simpa using amin_lt_sigma
  σ_lt := by norm_num
  mid := 3 / 5
  mid_ge := by norm_num
  mid_le := by norm_num
  mid_gain := by
    have hmin : min wSetting.gpi (wSetting.gainD (74 / 625) / 2) ≤ wSetting.gpi :=
      min_le_left _ _
    have hcert : 2 * wSetting.gpi ≤ wSetting.gainD (3 / 5) := by
      rw [wSetting_gpi]
      simp only [Setting.gainD, wSetting_β, wSetting_δ]
      norm_num [mbeta]
    linarith

@[simp] theorem wTracking_σ : wTracking.σ = 74 / 625 := rfl

/-! ### The two hypothesis bundles -/

/-- The scalar facts of `no-break parameter conditions`, proved for the Möbius profile. -/
theorem wEntry : wSetting.piBar < wSetting.ζδ - wSetting.ρ := by
  rw [wSetting_piBar]; norm_num

theorem wZetaLe : wSetting.ζδ ≤ wSetting.αmax := by simpa using zeta_le_amax

theorem wCondB : 2 * wSetting.gpi ≤ wSetting.gainD wTracking.σ := by
  rw [wSetting_gpi]
  simp only [Setting.gainD, wSetting_β, wSetting_δ, wTracking_σ]
  norm_num [mbeta]

theorem wCondC : wSetting.ρ < wSetting.pi + wSetting.gpi - wSetting.piBar := by
  rw [wSetting_gpi, wSetting_piBar]; norm_num

theorem wGeneralRegime : GeneralRegime wSetting where
  entry := by
    have h := wEntry
    have hmin := wSetting.αmin_lt_piBar
    simp only [Setting.zetaFloor]
    linarith
  zeta_le := wZetaLe

theorem wFilecoin : FilecoinLatencyParameters wSetting wTracking where
  pi_eq := rfl
  rho_eq := rfl
  zetaDelta_eq := rfl
  sigma_eq := rfl
  gpi_lower := by rw [wSetting_gpi]; norm_num
  gpi_upper := by rw [wSetting_gpi]; norm_num
  mid_eq := rfl
  ghat_eq := wTracking.ghat_eq_gpi wCondB
  gtilde_eq :=
    gtilde_eq_gpi
      (by simp only [Setting.zetaFloor]; linarith [wEntry])
      (by simp only [Setting.zetaFloor]; norm_num)
  bMax_eq :=
    bMax_eq_zero (by
      have hb : wSetting.betaD wSetting.pi = wSetting.pi + wSetting.gpi := by
        simp only [Setting.betaD_eq]; rfl
      rw [wTracking.lam_eq_piBar wCondB, hb]
      linarith [wCondC])

/-- The development's Filecoin-shaped corollary for the unconditional Möbius profile.  The
graph hypotheses remain explicit: a sampled permutation stack supplies `expands`, while
the chosen small-indegree layer graph supplies `DepthRobust`. -/
theorem mobius_latency_corollary
    {V : Type u} {ℓ n : ℕ}
    (G : Concrete.LayeredGraph V wSetting ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5) (hℓ : 14 < ℓ)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : wSetting.ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((FilecoinLatencyParameters.filecoinZMin wSetting.gpi ℓ : ℝ) - 1) *
          ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) :=
  wFilecoin.latency_corollary G P wGeneralRegime
    hn hαpi hℓ hDepth A hA hred hweight

end Witness

/--
**The Filecoin profile is inhabited.**

`Witness.wSetting` is an explicit expansion profile satisfying every field of
`Setting`, `GeneralRegime` and `FilecoinLatencyParameters` simultaneously.  Hence the
Filecoin corollaries of `Latency.lean` are not vacuously true.

The construction assumptions on the graph itself (`LayeredGraph.expands` and
`LayeredGraph.depthRobust`) remain explicit.  The former is supplied probabilistically
by the development's permutation-interlayer bound; the latter is the chosen intra-layer DAG's
depth-robustness certificate.
-/
theorem filecoinParameters_consistent :
    ∃ (S : Setting) (T : Tracking S),
      FilecoinLatencyParameters S T ∧ GeneralRegime S :=
  ⟨Witness.wSetting, Witness.wTracking, Witness.wFilecoin, Witness.wGeneralRegime⟩

end ProofOfSpace

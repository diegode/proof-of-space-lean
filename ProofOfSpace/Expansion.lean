/-
# Expansion profiles, the gain function, and the mirror corollary

This file sets up the analytic framework of this development and proves
the mirror consequences of `reversal identity` from the reversal law bundled in
`Setting`.

* `Setting` bundles the expansion function `β` together with the parameters
  `δ, π, ρ, ζδ` and the endpoints `αmin, αmax` of the interval where `gainδ ≥ 0`.
  All structural hypotheses are exactly those listed in this development.
* `Setting.gainD_mirror` is the gain-preservation half of `reversal identity`, the identity
  `gain_δ(1 - β(σ)) = gain_δ(σ)` that `tracking definitions` uses; `Setting.gainD_piBar` is its
  consequence `gain_δ(π̄) = g_π`; and `Setting.piBar_lt_pi` uses that the mirror map
  fixes `α_g`.
* `Setting.gpi_le_gainD` is the concavity consequence used everywhere downstream:
  `gainδ ≥ g_π` on the mirror interval `[pī, pi]`.
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function

namespace ProofOfSpace

open Real Set

/-- An affine function is convex on any convex set. -/
theorem convexOn_add_const {s : Set ℝ} (hs : Convex ℝ s) (c : ℝ) :
    ConvexOn ℝ s (fun x => x + c) := by
  refine ⟨hs, ?_⟩
  intro x _ y _ a b ha hb hab
  have : a • (x + c) + b • (y + c) = (a • x + b • y) + c := by
    simp only [smul_eq_mul]; linear_combination c * hab
  exact le_of_eq this.symm

/-- A concave function on `[0,1]` dominates its chords: strictly between `a` and `b` it
is at least the corresponding convex combination of `f a` and `f b`.

`ConcaveOn.min_le_of_mem_Icc` gives only `min (f a) (f b) ≤ f x`, too weak to separate a
zero of a concave function from a nearby positive value; the chord form is what makes
such zeros unique.  `Setting.concave_interior` is this lemma specialized to `gain_δ`;
the bare version is needed by `ChungFilecoin.lean` before any `Setting` exists. -/
theorem concaveOn_chord_le {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0:ℝ) 1) f)
    {a b x : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1)
    (hax : a < x) (hxb : x < b) :
    ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b ≤ f x := by
  have hba : (0:ℝ) < b - a := by linarith
  have hlam : (0:ℝ) ≤ (b - x) / (b - a) := div_nonneg (by linarith) hba.le
  have hmu : (0:ℝ) ≤ (x - a) / (b - a) := div_nonneg (by linarith) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have hcomb : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp; ring
  have h := hf.2 ha hb hlam hmu hsum
  simp only [smul_eq_mul, hcomb] at h
  exact h

/--
The full parameter setting of the analysis.

The fields are the structural assumptions on the expansion function stated in
this development (continuity is not needed; strict monotonicity,
concavity and the reversal law are), together with the numeric parameters.
-/
structure Setting where
  /-- The expansion function of the vertical edges. -/
  β : ℝ → ℝ
  /-- The unique maximiser of `gain = β - id`. -/
  αg : ℝ
  /-- The fraction of red pebbles allowed per level. -/
  δ : ℝ
  /-- The horizontal-robustness threshold `π`. -/
  pi : ℝ
  /-- The total weight of black pebbles, `ρ = 1 - ε_space`. -/
  ρ : ℝ
  /-- The adjusted weight of the challenge set. -/
  ζδ : ℝ
  /-- Left endpoint of `{gainδ ≥ 0}`. -/
  αmin : ℝ
  /-- Right endpoint of `{gainδ ≥ 0}`. -/
  αmax : ℝ
  β_maps : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → β x ∈ Icc (0:ℝ) 1
  /-- `β(0) = 0`: the empty set has no predecessors.

  This is not decorative.  `Concrete.LayeredGraph` bundles `pred_edge`, which forces
  `pred d ∅ = ∅`, against `expands`, which demands `β 0 · n ≤ |pred d ∅|`; so any
  `Setting` with `β 0 > 0` admits *no* layered graph at all with `n > 0` and `ℓ > 1`,
  and every graph-level theorem would be vacuously true for it. -/
  β_zero : β 0 = 0
  β_strictMonoOn : StrictMonoOn β (Icc (0:ℝ) 1)
  β_concaveOn : ConcaveOn ℝ (Icc (0:ℝ) 1) β
  β_expands : ∀ ⦃x⦄, x ∈ Ioo (0:ℝ) 1 → x < β x
  /-- `reversal identity`, supplied by `ChungCurve.chungBeta_reversal` for Chung expanders. -/
  β_reversal : ∀ ⦃x⦄, x ∈ Ioo (0:ℝ) 1 → β (1 - β x) = 1 - x
  αg_mem : αg ∈ Ioo (0:ℝ) 1
  /-- `αg` is the *unique* maximiser of the gain. -/
  αg_max : ∀ ⦃x⦄, x ∈ Icc (0:ℝ) 1 → x ≠ αg → β x - x < β αg - αg
  δ_nonneg : 0 ≤ δ
  ρ_nonneg : 0 ≤ ρ
  pi_mem : pi ∈ Ioo (0:ℝ) 1
  /-- `π` sits on the decreasing branch of the gain curve. -/
  αg_lt_pi : αg < pi
  /-- `δ` is small enough that `g_π > 0`. -/
  gpi_pos : 0 < β pi - δ - pi
  αmin_mem : αmin ∈ Icc (0:ℝ) αg
  αmax_mem : αmax ∈ Icc αg 1
  gainD_αmin : β αmin - δ - αmin = 0
  gainD_αmax : β αmax - δ - αmax = 0

namespace Setting

variable (S : Setting)


/-- `gain_δ(α) = β(α) - δ - α`. -/
def gainD (x : ℝ) : ℝ := S.β x - S.δ - x

/-- `β_δ(α) = β(α) - δ`. -/
def betaD (x : ℝ) : ℝ := S.β x - S.δ

/-- `g_π = gain_δ(π)`. -/
def gpi : ℝ := S.gainD S.pi

/-- `pī = 1 - β(pi)`, the lower member of the equal-gain mirror pair. -/
def piBar : ℝ := 1 - S.β S.pi

@[simp] theorem betaD_eq (x : ℝ) : S.betaD x = x + S.gainD x := by
  simp only [betaD, gainD]; ring

theorem gpi_pos' : 0 < S.gpi := S.gpi_pos

theorem αg_mem_Icc : S.αg ∈ Icc (0:ℝ) 1 := ⟨S.αg_mem.1.le, S.αg_mem.2.le⟩

theorem pi_mem_Icc : S.pi ∈ Icc (0:ℝ) 1 := ⟨S.pi_mem.1.le, S.pi_mem.2.le⟩

/-- `gain_δ` is concave, being `β` minus an affine function. -/
theorem gainD_concaveOn : ConcaveOn ℝ (Icc (0:ℝ) 1) S.gainD := by
  have h : S.gainD = S.β - fun x => x + S.δ := by
    funext x; simp only [gainD, Pi.sub_apply]; ring
  rw [h]
  exact S.β_concaveOn.sub (convexOn_add_const (convex_Icc 0 1) S.δ)

/-- `β_δ` is strictly monotone. -/
theorem betaD_strictMonoOn : StrictMonoOn S.betaD (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  simp only [betaD]
  exact sub_lt_sub_right (S.β_strictMonoOn hx hy hxy) _

/-! ### Mirror consequences of `reversal identity` -/

/-- The mirror map `x ↦ 1 - β x` preserves the gain.  This is the identity
`gain_δ(1 - β(σ)) = gain_δ(σ)` displayed after `tracking definitions`. -/
theorem gainD_mirror {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    S.gainD (1 - S.β x) = S.gainD x := by
  simp only [gainD, S.β_reversal hx]; ring

/-- The decreasing mirror map fixes the maximiser `αg`. -/
theorem mirror_αg : 1 - S.β S.αg = S.αg := by
  set m := 1 - S.β S.αg with hm
  have hβ : S.β S.αg ∈ Ioo (0:ℝ) 1 := by
    refine ⟨lt_of_le_of_lt (S.αg_mem.1.le) (S.β_expands S.αg_mem), ?_⟩
    rcases lt_or_eq_of_le (S.β_maps S.αg_mem_Icc).2 with h | h
    · exact h
    · exfalso
      have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
      have := S.β_strictMonoOn S.αg_mem_Icc h1 S.αg_mem.2
      have hβ1 : S.β 1 ≤ 1 := (S.β_maps h1).2
      rw [h] at this; linarith
  have hmem : m ∈ Ioo (0:ℝ) 1 :=
    ⟨by simp only [hm]; linarith [hβ.2], by simp only [hm]; linarith [hβ.1]⟩
  by_contra hne
  have hmax := S.αg_max ⟨hmem.1.le, hmem.2.le⟩ hne
  have heq : S.gainD m = S.gainD S.αg := S.gainD_mirror S.αg_mem
  simp only [gainD] at heq
  linarith

/-- `pī < αg`: the mirror of a point on the decreasing branch lands on the increasing branch. -/
theorem piBar_lt_αg : S.piBar < S.αg := by
  have := S.β_strictMonoOn S.αg_mem_Icc S.pi_mem_Icc S.αg_lt_pi
  simp only [piBar]
  have := S.mirror_αg
  linarith

theorem piBar_lt_pi : S.piBar < S.pi := S.piBar_lt_αg.trans S.αg_lt_pi

theorem piBar_pos : 0 < S.piBar := by
  simp only [piBar]
  have : S.β S.pi < 1 := by
    rcases lt_or_eq_of_le (S.β_maps S.pi_mem_Icc).2 with h | h
    · exact h
    · exfalso
      have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
      have hlt := S.β_strictMonoOn S.pi_mem_Icc h1 S.pi_mem.2
      have hβ1 : S.β 1 ≤ 1 := (S.β_maps h1).2
      rw [h] at hlt; linarith
  linarith

theorem piBar_mem : S.piBar ∈ Ioo (0:ℝ) 1 :=
  ⟨S.piBar_pos, lt_trans S.piBar_lt_αg S.αg_mem.2⟩

theorem piBar_mem_Icc : S.piBar ∈ Icc (0:ℝ) 1 := ⟨S.piBar_mem.1.le, S.piBar_mem.2.le⟩

/-- The mirror value at `π`: `gain_δ(pī) = g_π`. -/
theorem gainD_piBar : S.gainD S.piBar = S.gpi := S.gainD_mirror S.pi_mem

/-! ### Concavity consequences -/

/-- The central uniform bound: `gain_δ ≥ g_π` on the mirror interval `[pī, pi]`. -/
theorem gpi_le_gainD {x : ℝ} (hx : x ∈ Icc S.piBar S.pi) : S.gpi ≤ S.gainD x := by
  have h := S.gainD_concaveOn.min_le_of_mem_Icc S.piBar_mem_Icc S.pi_mem_Icc hx
  rw [S.gainD_piBar] at h
  simpa [gpi] using h

/-- `gain_δ ≥ 0` on the active interval `[αmin, αmax]`. -/
theorem gainD_nonneg {x : ℝ} (hx : x ∈ Icc S.αmin S.αmax) : 0 ≤ S.gainD x := by
  have hmin : S.αmin ∈ Icc (0:ℝ) 1 := ⟨S.αmin_mem.1, le_trans S.αmin_mem.2 S.αg_mem.2.le⟩
  have hmax : S.αmax ∈ Icc (0:ℝ) 1 := ⟨le_trans S.αg_mem.1.le S.αmax_mem.1, S.αmax_mem.2⟩
  have h := S.gainD_concaveOn.min_le_of_mem_Icc hmin hmax hx
  have h1 : S.gainD S.αmin = 0 := S.gainD_αmin
  have h2 : S.gainD S.αmax = 0 := S.gainD_αmax
  rw [h1, h2] at h
  simpa using h

/-- `π < αmax`: the fertility threshold has positive gain, so it lies strictly inside the
active interval. -/
theorem pi_lt_αmax : S.pi < S.αmax := by
  by_contra hcon
  push_neg at hcon
  have hmemIcc : S.αmax ∈ Icc S.αg S.pi := ⟨S.αmax_mem.1, hcon⟩
  have hαg : S.αg ∈ Icc (0:ℝ) 1 := S.αg_mem_Icc
  have h := S.gainD_concaveOn.min_le_of_mem_Icc hαg S.pi_mem_Icc hmemIcc
  have hg : S.gainD S.pi ≤ S.gainD S.αg := by
    rcases eq_or_ne S.pi S.αg with h' | h'
    · rw [h']
    · have := S.αg_max S.pi_mem_Icc h'
      simp only [gainD]; linarith
  have h2 : S.gainD S.αmax = 0 := S.gainD_αmax
  have h3 : 0 < S.gainD S.pi := S.gpi_pos
  rw [h2] at h
  simp only [min_le_iff] at h
  rcases h with h | h <;> linarith

/-- `αmin < pī`, for the same reason. -/
theorem αmin_lt_piBar : S.αmin < S.piBar := by
  by_contra hcon
  push_neg at hcon
  have hmemIcc : S.αmin ∈ Icc S.piBar S.αg := ⟨hcon, S.αmin_mem.2⟩
  have hαg : S.αg ∈ Icc (0:ℝ) 1 := S.αg_mem_Icc
  have h := S.gainD_concaveOn.min_le_of_mem_Icc S.piBar_mem_Icc hαg hmemIcc
  have hg : S.gpi ≤ S.gainD S.αg := by
    rcases eq_or_ne S.pi S.αg with h' | h'
    · simp only [gpi, h']; exact le_rfl
    · have := S.αg_max S.pi_mem_Icc h'
      simp only [gpi, gainD]; linarith
  have h1 : S.gainD S.αmin = 0 := S.gainD_αmin
  have hb : S.gainD S.piBar = S.gpi := S.gainD_piBar
  rw [h1, hb] at h
  have h3 : 0 < S.gpi := S.gpi_pos
  rcases min_cases S.gpi (S.gainD S.αg) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> linarith

theorem αmin_lt_pi : S.αmin < S.pi := S.αmin_lt_piBar.trans S.piBar_lt_pi

theorem αmin_nonneg : 0 ≤ S.αmin := S.αmin_mem.1

theorem αmax_le_one : S.αmax ≤ 1 := S.αmax_mem.2

/-- `β_δ(αmax) = αmax`: the footprint cannot grow past the right endpoint. -/
theorem betaD_αmax : S.betaD S.αmax = S.αmax := by
  have := S.gainD_αmax
  simp only [betaD]; linarith

theorem αmax_mem_Icc : S.αmax ∈ Icc (0:ℝ) 1 :=
  ⟨le_trans S.αg_mem.1.le S.αmax_mem.1, S.αmax_mem.2⟩

theorem αmin_mem_Icc : S.αmin ∈ Icc (0:ℝ) 1 :=
  ⟨S.αmin_mem.1, le_trans S.αmin_mem.2 S.αg_mem.2.le⟩

/-! ### Strict positivity of the gain in the interior of the active interval

The two lemmas below are the only further consequences of concavity that the latency
analysis needs: the gain is strictly positive strictly inside `[αmin, αmax]`, and it is
at most `g_π` strictly outside the mirror interval `[pī, pi]`.  Both are obtained from
the same explicit convex-combination form of concavity. -/

/-- Concavity written at an explicit interior point of a segment. -/
theorem concave_interior {a b x : ℝ}
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (_hab : a < b) (hx : x ∈ Ioo a b) :
    ((b - x) / (b - a)) * S.gainD a + ((x - a) / (b - a)) * S.gainD b ≤ S.gainD x :=
  concaveOn_chord_le S.gainD_concaveOn ha hb hx.1 hx.2

/-- `β x < 1` for `x < 1`: strict monotonicity plus `β 1 ≤ 1`. -/
theorem β_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : S.β x < 1 := by
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hlt := S.β_strictMonoOn ⟨hx0, hx1.le⟩ h1 hx1
  have := (S.β_maps h1).2
  linarith

/-- The gain at the peak dominates `g_π`. -/
theorem gpi_le_gainD_αg : S.gpi ≤ S.gainD S.αg := by
  rcases eq_or_ne S.pi S.αg with h | h
  · simp only [gpi, h]; exact le_rfl
  · have := S.αg_max S.pi_mem_Icc h
    simp only [gpi, gainD]; linarith

theorem αmin_lt_αg : S.αmin < S.αg := S.αmin_lt_piBar.trans S.piBar_lt_αg

theorem αg_lt_αmax : S.αg < S.αmax := S.αg_lt_pi.trans S.pi_lt_αmax

/-- **The gain is strictly positive strictly inside the active interval.** -/
theorem gainD_pos {x : ℝ} (hx : x ∈ Ioo S.αmin S.αmax) : 0 < S.gainD x := by
  have hαg : 0 < S.gainD S.αg := lt_of_lt_of_le S.gpi_pos S.gpi_le_gainD_αg
  rcases lt_trichotomy x S.αg with h | h | h
  · have hlt : S.αmin < S.αg := S.αmin_lt_αg
    have hc := S.concave_interior S.αmin_mem_Icc S.αg_mem_Icc hlt ⟨hx.1, h⟩
    have h0 : S.gainD S.αmin = 0 := S.gainD_αmin
    rw [h0] at hc
    have hpos : 0 < (x - S.αmin) / (S.αg - S.αmin) :=
      div_pos (by linarith [hx.1]) (by linarith)
    nlinarith
  · rw [h]; exact hαg
  · have hlt : S.αg < S.αmax := S.αg_lt_αmax
    have hc := S.concave_interior S.αg_mem_Icc S.αmax_mem_Icc hlt ⟨h, hx.2⟩
    have h0 : S.gainD S.αmax = 0 := S.gainD_αmax
    rw [h0] at hc
    have hpos : 0 < (S.αmax - x) / (S.αmax - S.αg) :=
      div_pos (by linarith [hx.2]) (by linarith)
    nlinarith

/-- **Outside the mirror interval the gain drops below `g_π`.**  Stated on the left branch,
which is the side used by the tracking parameters of this development. -/
theorem gainD_le_gpi_of_lt_piBar {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hlt : x < S.piBar) :
    S.gainD x ≤ S.gpi := by
  have hxpi : x < S.pi := hlt.trans S.piBar_lt_pi
  have hc := S.concave_interior hx S.pi_mem_Icc hxpi ⟨hlt, S.piBar_lt_pi⟩
  rw [S.gainD_piBar] at hc
  have hden : (0:ℝ) < S.pi - x := by linarith
  have hgpi : S.gainD S.pi = S.gpi := rfl
  rw [hgpi] at hc
  set A : ℝ := (S.pi - S.piBar) / (S.pi - x) with hA
  set Bc : ℝ := (S.piBar - x) / (S.pi - x) with hBc
  have hApos : 0 < A := div_pos (by linarith [S.piBar_lt_pi]) hden
  have hsum : A + Bc = 1 := by
    rw [hA, hBc]
    field_simp
    ring
  have hBc' : Bc = 1 - A := by linarith
  rw [hBc'] at hc
  have key : A * S.gainD x ≤ A * S.gpi := by nlinarith [hc]
  exact le_of_mul_le_mul_left key hApos


/-- **Below `αmin` the gain is nonpositive.** -/
theorem gainD_nonpos_of_le_αmin {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hle : x ≤ S.αmin) :
    S.gainD x ≤ 0 := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · have h0 : S.gainD S.αmin = 0 := S.gainD_αmin
    rw [heq, h0]
  · have hαg : 0 < S.gainD S.αg := lt_of_lt_of_le S.gpi_pos' S.gpi_le_gainD_αg
    have hαmin_lt : S.αmin < S.αg := S.αmin_lt_αg
    have hc := S.concave_interior hx S.αg_mem_Icc (hlt.trans hαmin_lt) ⟨hlt, hαmin_lt⟩
    have h0 : S.gainD S.αmin = 0 := S.gainD_αmin
    rw [h0] at hc
    have hden : (0:ℝ) < S.αg - x := by linarith
    have hA : 0 < (S.αg - S.αmin) / (S.αg - x) := div_pos (by linarith) hden
    have hB : 0 < (S.αmin - x) / (S.αg - x) := div_pos (by linarith) hden
    nlinarith [hc, hA, mul_pos hB hαg]

/-- **Above `αmax` the gain is nonpositive.**  This is the right-hand counterpart of
`gainD_nonpos_of_le_αmin`; it follows from concavity, the positive gain at `αg`, and
the zero at `αmax`. -/
theorem gainD_nonpos_of_αmax_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hle : S.αmax ≤ x) : S.gainD x ≤ 0 := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · have h0 : S.gainD S.αmax = 0 := S.gainD_αmax
    rw [← heq, h0]
  · have hαg : 0 < S.gainD S.αg := lt_of_lt_of_le S.gpi_pos' S.gpi_le_gainD_αg
    have hαg_lt : S.αg < S.αmax := S.αg_lt_αmax
    have hc := S.concave_interior S.αg_mem_Icc hx (hαg_lt.trans hlt)
      ⟨hαg_lt, hlt⟩
    have h0 : S.gainD S.αmax = 0 := S.gainD_αmax
    rw [h0] at hc
    have hden : (0 : ℝ) < x - S.αg := by linarith
    have hA : 0 < (x - S.αmax) / (x - S.αg) := div_pos (by linarith) hden
    have hB : 0 < (S.αmax - S.αg) / (x - S.αg) := div_pos (by linarith) hden
    nlinarith [hc, mul_pos hA hαg, hB]

/-! ### The general positive floor `ζ_δ - ρ` and the infertile-gain floor `g̃`

this development, `challenge-floor lemma`.  Outside the entry condition
`π̄ < ζ_δ - ρ` the challenge footprint may sink below `π̄`, so infertile levels can no
longer be charged at rate `g_π`.  What survives is the coarser floor
`zetaFloor = ζ_δ - ρ`,
which the whole budget cannot breach, and the rate `g̃` certified there.  Both reduce
to the uniform constants when the entry condition does hold, since then `π̄ < ζ_δ - ρ` and
concavity gives `gain_δ(ζ_δ - ρ) ≥ g_π`. -/

/-- `zetaFloor = ζ_δ - ρ`: the footprint floor that survives the whole black-pebble budget. -/
def zetaFloor : ℝ := S.ζδ - S.ρ

/-- `g̃ = min{gain_δ(ζ_δ - ρ), g_π}`: the infertile-gain floor of the general regime. -/
noncomputable def gtilde : ℝ := min (S.gainD S.zetaFloor) S.gpi

theorem gtilde_le_gpi : S.gtilde ≤ S.gpi := min_le_right _ _

theorem gtilde_le_gainD_zetaFloor : S.gtilde ≤ S.gainD S.zetaFloor := min_le_left _ _

theorem zetaFloor_le_zetaDelta : S.zetaFloor ≤ S.ζδ := by
  simp only [zetaFloor]; linarith [S.ρ_nonneg]

theorem zetaFloor_mem_Icc (h1 : S.αmin < S.zetaFloor) (h2 : S.zetaFloor < S.αmax) :
    S.zetaFloor ∈ Icc (0 : ℝ) 1 :=
  ⟨le_of_lt (lt_of_le_of_lt S.αmin_nonneg h1), le_of_lt (lt_of_lt_of_le h2 S.αmax_le_one)⟩

/-- `g̃ > 0`: the floor sits strictly inside the active interval, where the gain is
strictly positive. -/
theorem gtilde_pos (h1 : S.αmin < S.zetaFloor) (h2 : S.zetaFloor < S.αmax) : 0 < S.gtilde :=
  lt_min (S.gainD_pos ⟨h1, h2⟩) S.gpi_pos

/-- **The certified infertile-gain floor.**  By concavity, `gain_δ ≥ g̃` throughout the
whole infertile range `[ζ_δ - ρ, π]`. -/
theorem gtilde_le_gainD (h1 : S.αmin < S.zetaFloor) (h2 : S.zetaFloor < S.αmax)
    {x : ℝ} (hx : x ∈ Icc S.zetaFloor S.pi) : S.gtilde ≤ S.gainD x := by
  have h := S.gainD_concaveOn.min_le_of_mem_Icc (S.zetaFloor_mem_Icc h1 h2) S.pi_mem_Icc hx
  simpa only [gtilde, gpi] using h

end Setting

end ProofOfSpace

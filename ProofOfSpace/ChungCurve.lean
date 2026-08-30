/-
# The Chung threshold curve, constructed

`Chung.lean` proves the anti-diagonal symmetry of the union-bound exponent but never
builds the curve.  This file constructs it: for each source density
`x ∈ (0,1)` and degree `d > 2` it produces the threshold `β_d x` as the unique zero of
the union-bound exponent `E(x, ·)`, and characterises certified expansion by

  `E(x, y) < 0  ↔  y < β_d x`      (`sec_neg_iff`, for `x < y < 1`).

The argument is elementary once the exponent is written in Reyzin's closed form: for
fixed `x`, the `y`-section is *strictly concave*, negative at `y = x`, and positive at
`y = 1`, so it has exactly one zero and is negative exactly to its left.

The point of constructing `β` rather than assuming it is that the numerical
certificates of `cor:filecoin` then become theorems about a defined object
instead of hypotheses.  In particular `σ_min` is derived: see `ChungNumerics.lean`.

**What this file does not do.**  It constructs the *threshold*: the density `β_d x` below
which Chung's union bound over a random degree-`d` graph is subexponentially small.  It
does not prove that any graph attains that expansion.  That step — "a random Chung graph
expands every density-`x` set to density `β_d x`, with high probability" — enters the
development only as the `expands` field of `Concrete.LayeredGraph`, and is assumed there,
not derived here.  So "the genuine constructed Chung-8 curve" in the downstream
docstrings should be read as a statement about the curve, never about the construction.
-/
import ProofOfSpace.Chung
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofOfSpace
namespace ChungCurve

open Real Set

/-! ### The `y`-section in closed form -/

/-- The `y`-section of the Chung exponent, in Reyzin's closed form.  Valid for
`0 < x < y < 1`; see `chungExponent_eq_sec`. -/
noncomputable def sec (d x y : ℝ) : ℝ :=
  binEntropy x + binEntropy y +
    d * ((x - y) * log (y - x) + y * log y + (1 - x) * log (1 - x))

theorem chungExponent_eq_sec {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    chungExponent d x y = sec d x y := by
  simp only [chungExponent, sec]
  rw [mul_binEntropy_div_sub_binEntropy hx hxy hy]

/-- The part of `sec` that depends on `y`, separated from the constant part. -/
noncomputable def vary (d x y : ℝ) : ℝ :=
  (d - 1) * (y * log y) - (1 - y) * log (1 - y) - d * ((y - x) * log (y - x))

/-- The constant part of `sec`. -/
noncomputable def cst (d x : ℝ) : ℝ := binEntropy x + d * ((1 - x) * log (1 - x))

theorem sec_eq (d x y : ℝ) : sec d x y = cst d x + vary d x y := by
  simp only [sec, cst, vary, binEntropy_eq_neg]
  ring

/-! ### Endpoint values -/

theorem sec_left (d x : ℝ) : sec d x x = (2 - d) * binEntropy x := by
  simp only [sec, binEntropy_eq_neg]
  rw [sub_self, log_zero]
  ring

/-- `hx` records the intended domain `0 < x < 1`; the closed form happens not to need
it. -/
theorem sec_right {d x : ℝ} (_hx : x < 1) : sec d x 1 = binEntropy x := by
  simp only [sec]
  rw [binEntropy_one, log_one, show (1:ℝ) - x = 1 - x from rfl]
  ring

/-! ### Derivatives of the section -/

/-- `∂E/∂y = (d-1) log y + log (1-y) - d log (y-x)`. -/
noncomputable def vary' (d x y : ℝ) : ℝ :=
  (d - 1) * log y + log (1 - y) - d * log (y - x)

/-- `∂²E/∂y² = (d-1)/y - 1/(1-y) - d/(y-x)`. -/
noncomputable def vary'' (d x y : ℝ) : ℝ :=
  (d - 1) / y - 1 / (1 - y) - d / (y - x)

theorem hasDerivAt_sec {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    HasDerivAt (fun t => sec d x t) (vary' d x y) y := by
  have hy0 : (0:ℝ) < y := hx.trans hxy
  have hsub : (0:ℝ) < y - x := sub_pos.mpr hxy
  have hone : (0:ℝ) < 1 - y := sub_pos.mpr hy
  have hin2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1:ℝ)
  have hin3 : HasDerivAt (fun t : ℝ => t - x) 1 y := by
    simpa using (hasDerivAt_id y).sub_const x
  have h1 : HasDerivAt (fun t : ℝ => t * log t) (log y + 1) y :=
    hasDerivAt_mul_log (ne_of_gt hy0)
  have h2 : HasDerivAt (fun t : ℝ => (1 - t) * log (1 - t))
      (-1 * log (1 - y) + (1 - y) * (-1 / (1 - y))) y :=
    hin2.mul (hin2.log (by simpa using ne_of_gt hone))
  have h3 : HasDerivAt (fun t : ℝ => (t - x) * log (t - x))
      (1 * log (y - x) + (y - x) * (1 / (y - x))) y :=
    hin3.mul (hin3.log (by simpa using ne_of_gt hsub))
  have hcomb : HasDerivAt
      (fun t : ℝ => cst d x +
        ((d - 1) * (t * log t) - (1 - t) * log (1 - t) - d * ((t - x) * log (t - x))))
      ((d - 1) * (log y + 1) - (-1 * log (1 - y) + (1 - y) * (-1 / (1 - y)))
        - d * (1 * log (y - x) + (y - x) * (1 / (y - x)))) y :=
    (((h1.const_mul (d - 1)).sub h2).sub (h3.const_mul d)).const_add (cst d x)
  have heq : (fun t => sec d x t) =
      (fun t : ℝ => cst d x +
        ((d - 1) * (t * log t) - (1 - t) * log (1 - t) - d * ((t - x) * log (t - x)))) := by
    funext t; rw [sec_eq]; rfl
  rw [heq]
  convert hcomb using 1
  simp only [vary']
  field_simp
  ring

theorem hasDerivAt_vary' {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    HasDerivAt (fun t => vary' d x t) (vary'' d x y) y := by
  have hy0 : (0:ℝ) < y := hx.trans hxy
  have hsub : (0:ℝ) < y - x := sub_pos.mpr hxy
  have hone : (0:ℝ) < 1 - y := sub_pos.mpr hy
  have hin2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1:ℝ)
  have hin3 : HasDerivAt (fun t : ℝ => t - x) 1 y := by
    simpa using (hasDerivAt_id y).sub_const x
  have h1 : HasDerivAt (fun t : ℝ => log t) y⁻¹ y := Real.hasDerivAt_log (ne_of_gt hy0)
  have h2 : HasDerivAt (fun t : ℝ => log (1 - t)) (-1 / (1 - y)) y :=
    hin2.log (by simpa using ne_of_gt hone)
  have h3 : HasDerivAt (fun t : ℝ => log (t - x)) (1 / (y - x)) y :=
    hin3.log (by simpa using ne_of_gt hsub)
  have hcomb : HasDerivAt (fun t : ℝ => (d - 1) * log t + log (1 - t) - d * log (t - x))
      ((d - 1) * y⁻¹ + -1 / (1 - y) - d * (1 / (y - x))) y :=
    ((h1.const_mul (d - 1)).add h2).sub (h3.const_mul d)
  have heq : (fun t => vary' d x t) =
      (fun t : ℝ => (d - 1) * log t + log (1 - t) - d * log (t - x)) := by
    funext t; rfl
  rw [heq]
  convert hcomb using 1
  simp only [vary'']
  field_simp
  ring

/-- The key sign: the section is strictly concave in `y`. -/
theorem vary''_neg {d x y : ℝ} (hd : 1 ≤ d) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    vary'' d x y < 0 := by
  have hy0 : (0:ℝ) < y := hx.trans hxy
  have hsub : (0:ℝ) < y - x := sub_pos.mpr hxy
  have hone : (0:ℝ) < 1 - y := sub_pos.mpr hy
  have key : vary'' d x y = -(((d - 1) * x + y) / (y * (y - x))) - 1 / (1 - y) := by
    simp only [vary'']
    field_simp
    ring
  rw [key]
  have hnum : 0 < (d - 1) * x + y := by nlinarith
  have h1 : 0 < ((d - 1) * x + y) / (y * (y - x)) := div_pos hnum (by positivity)
  have h2 : 0 < 1 / (1 - y) := by positivity
  linarith

/-! ### Continuity and strict concavity of the section -/

theorem continuous_sec (d x : ℝ) : Continuous (fun t => sec d x t) := by
  have h1 : Continuous (fun t : ℝ => (t - x) * log (t - x)) :=
    continuous_mul_log.comp (continuous_id.sub continuous_const)
  have heq : (fun t => sec d x t) = fun t =>
      binEntropy x + binEntropy t +
        d * (-((t - x) * log (t - x)) + t * log t + (1 - x) * log (1 - x)) := by
    funext t; simp only [sec]; ring
  rw [heq]
  exact (continuous_const.add binEntropy_continuous).add
    (continuous_const.mul ((h1.neg.add continuous_mul_log).add continuous_const))

theorem deriv_sec_eq {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    deriv (fun t => sec d x t) y = vary' d x y := (hasDerivAt_sec hx hxy hy).deriv

theorem deriv2_sec_eq {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    deriv^[2] (fun t => sec d x t) y = vary'' d x y := by
  have hnhds : Ioo x 1 ∈ nhds y := Ioo_mem_nhds hxy hy
  have heq : deriv (fun t => sec d x t) =ᶠ[nhds y] (fun t => vary' d x t) := by
    filter_upwards [hnhds] with t ht using deriv_sec_eq hx ht.1 ht.2
  change deriv (deriv (fun t => sec d x t)) y = vary'' d x y
  rw [heq.deriv_eq]
  exact (hasDerivAt_vary' hx hxy hy).deriv

/-- **The section is strictly concave.**  This is the whole analytic content: it is what
makes the certified region an interval and `β` well defined. -/
theorem strictConcaveOn_sec {d x : ℝ} (hd : 1 ≤ d) (hx : 0 < x) (_hx1 : x < 1) :
    StrictConcaveOn ℝ (Icc x 1) (fun t => sec d x t) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Icc x 1)
    (continuous_sec d x).continuousOn ?_
  intro y hy
  rw [interior_Icc] at hy
  rw [deriv2_sec_eq hx hy.1 hy.2]
  exact vary''_neg hd hx hy.1 hy.2

/-! ### Endpoint signs and the root -/

theorem sec_left_neg {d x : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1) : sec d x x < 0 := by
  rw [sec_left]
  have := binEntropy_pos hx hx1
  nlinarith

theorem sec_right_pos {d x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 < sec d x 1 := by
  rw [sec_right hx1]; exact binEntropy_pos hx hx1

theorem exists_root {d x : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1) :
    ∃ r ∈ Ioo x 1, sec d x r = 0 := by
  have hmem : (0:ℝ) ∈ Ioo (sec d x x) (sec d x 1) :=
    ⟨sec_left_neg hd hx hx1, sec_right_pos hx hx1⟩
  obtain ⟨r, hr, hval⟩ :=
    intermediate_value_Ioo hx1.le (continuous_sec d x).continuousOn hmem
  exact ⟨r, hr, hval⟩

/-! ### The sign characterisation -/

theorem sec_pos_of_root_lt {d x r y : ℝ} (hd : 1 ≤ d) (hx : 0 < x) (hx1 : x < 1)
    (hr : r ∈ Ioo x 1) (hroot : sec d x r = 0) (hy : y ∈ Ioo r 1) : 0 < sec d x y := by
  have hconc := strictConcaveOn_sec hd hx hx1
  have hrmem : r ∈ Icc x 1 := ⟨hr.1.le, hr.2.le⟩
  have h1mem : (1:ℝ) ∈ Icc x 1 := ⟨hx1.le, le_refl 1⟩
  have hden : (0:ℝ) < 1 - r := by linarith [hr.2]
  have hne : (1:ℝ) - r ≠ 0 := ne_of_gt hden
  have hapos : 0 < (1 - y) / (1 - r) := div_pos (by linarith [hy.2]) hden
  have hbpos : 0 < (y - r) / (1 - r) := div_pos (by linarith [hy.1]) hden
  have hab : (1 - y) / (1 - r) + (y - r) / (1 - r) = 1 := by
    have h : (1 - y) / (1 - r) + (y - r) / (1 - r) = ((1 - y) + (y - r)) / (1 - r) := by ring
    rw [h, div_eq_iff hne]; ring
  have hstrict := hconc.2 hrmem h1mem (ne_of_lt hr.2) hapos hbpos hab
  simp only [smul_eq_mul] at hstrict
  have hcomb : (1 - y) / (1 - r) * r + (y - r) / (1 - r) * 1 = y := by
    have h : (1 - y) / (1 - r) * r + (y - r) / (1 - r) * 1
        = ((1 - y) * r + (y - r)) / (1 - r) := by ring
    rw [h, div_eq_iff hne]; ring
  rw [hcomb, hroot] at hstrict
  have hpos := sec_right_pos (d := d) hx hx1
  nlinarith

theorem sec_neg_of_lt_root {d x r y : ℝ} (hd : 1 ≤ d) (hx : 0 < x) (hx1 : x < 1)
    (hr : r ∈ Ioo x 1) (hroot : sec d x r = 0) (hy : y ∈ Ioo x r) : sec d x y < 0 := by
  by_contra hcon
  push Not at hcon
  have hconc := strictConcaveOn_sec hd hx hx1
  have hylt1 : y < 1 := lt_trans hy.2 hr.2
  have hymem : y ∈ Icc x 1 := ⟨hy.1.le, hylt1.le⟩
  have h1mem : (1:ℝ) ∈ Icc x 1 := ⟨hx1.le, le_refl 1⟩
  have hden : (0:ℝ) < 1 - y := by linarith
  have hne : (1:ℝ) - y ≠ 0 := ne_of_gt hden
  have hapos : 0 < (1 - r) / (1 - y) := div_pos (by linarith [hr.2]) hden
  have hbpos : 0 < (r - y) / (1 - y) := div_pos (by linarith [hy.2]) hden
  have hab : (1 - r) / (1 - y) + (r - y) / (1 - y) = 1 := by
    have h : (1 - r) / (1 - y) + (r - y) / (1 - y) = ((1 - r) + (r - y)) / (1 - y) := by ring
    rw [h, div_eq_iff hne]; ring
  have hstrict := hconc.2 hymem h1mem (ne_of_lt hylt1) hapos hbpos hab
  simp only [smul_eq_mul] at hstrict
  have hcomb : (1 - r) / (1 - y) * y + (r - y) / (1 - y) * 1 = r := by
    have h : (1 - r) / (1 - y) * y + (r - y) / (1 - y) * 1
        = ((1 - r) * y + (r - y)) / (1 - y) := by ring
    rw [h, div_eq_iff hne]; ring
  rw [hcomb, hroot] at hstrict
  have hpos := sec_right_pos (d := d) hx hx1
  nlinarith

/-! ### The threshold curve -/

/-- `β_d x`, the Chung expansion threshold: the unique zero of `E(x, ·)` in `(x, 1)`. -/
noncomputable def chungBeta (d x : ℝ) : ℝ := sSup {y | y ∈ Ioo x 1 ∧ sec d x y < 0}

theorem chungBeta_eq_root {d x r : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1)
    (hr : r ∈ Ioo x 1) (hroot : sec d x r = 0) : chungBeta d x = r := by
  have hd1 : (1:ℝ) ≤ d := by linarith
  have hset : {y | y ∈ Ioo x 1 ∧ sec d x y < 0} = Ioo x r := by
    ext y
    constructor
    · rintro ⟨hy, hneg⟩
      refine ⟨hy.1, ?_⟩
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with heq | hlt
      · rw [heq] at hroot; linarith
      · have := sec_pos_of_root_lt hd1 hx hx1 hr hroot ⟨hlt, hy.2⟩
        linarith
    · intro hy
      exact ⟨⟨hy.1, hy.2.trans hr.2⟩, sec_neg_of_lt_root hd1 hx hx1 hr hroot hy⟩
  rw [chungBeta, hset, csSup_Ioo hr.1]

/-- **The defining property of `β`.**  For `x < y < 1`, the Chung union bound certifies
expansion from density `x` to density `y` exactly when `y < β_d x`. -/
theorem sec_neg_iff {d x y : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1)
    (hxy : x < y) (hy : y < 1) : sec d x y < 0 ↔ y < chungBeta d x := by
  obtain ⟨r, hr, hroot⟩ := exists_root hd hx hx1
  have hd1 : (1:ℝ) ≤ d := by linarith
  rw [chungBeta_eq_root hd hx hx1 hr hroot]
  constructor
  · intro hneg
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq] at hroot; linarith
    · have := sec_pos_of_root_lt hd1 hx hx1 hr hroot ⟨hlt, hy⟩
      linarith
  · intro hlt
    exact sec_neg_of_lt_root hd1 hx hx1 hr hroot ⟨hxy, hlt⟩

theorem chungBeta_mem {d x : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1) :
    chungBeta d x ∈ Ioo x 1 := by
  obtain ⟨r, hr, hroot⟩ := exists_root hd hx hx1
  rw [chungBeta_eq_root hd hx hx1 hr hroot]; exact hr

theorem sec_chungBeta {d x : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1) :
    sec d x (chungBeta d x) = 0 := by
  obtain ⟨r, hr, hroot⟩ := exists_root hd hx hx1
  rw [chungBeta_eq_root hd hx hx1 hr hroot]; exact hroot

/-- **The reversal law for the constructed Chung threshold itself.**

This theorem is not conditional on any abstract interface: `chungBeta` is the
supremum/root constructed in this file.  The
reflected point `1 - x` is a root of the section based at `1 - chungBeta d x` by the
anti-diagonal symmetry of `chungExponent`; uniqueness of the section root then gives
the identity. -/
theorem chungBeta_reversal {d x : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1) :
    chungBeta d (1 - chungBeta d x) = 1 - x := by
  have hβ := chungBeta_mem hd hx hx1
  have hmx0 : 0 < 1 - chungBeta d x := by linarith [hβ.2]
  have hmx1 : 1 - chungBeta d x < 1 := by linarith [hβ.1]
  have hr : 1 - x ∈ Ioo (1 - chungBeta d x) 1 :=
    ⟨by linarith [hβ.1], by linarith⟩
  apply chungBeta_eq_root hd hmx0 hmx1 hr
  calc
    sec d (1 - chungBeta d x) (1 - x) =
        chungExponent d (1 - chungBeta d x) (1 - x) :=
      (chungExponent_eq_sec hmx0 hr.1 hr.2).symm
    _ = chungExponent d x (chungBeta d x) :=
      (chungExponent_symm hx hβ.1 hβ.2).symm
    _ = sec d x (chungBeta d x) :=
      chungExponent_eq_sec hx hβ.1 hβ.2
    _ = 0 := sec_chungBeta hd hx hx1

/-- The constructed Chung threshold is strictly increasing on the open unit interval.

If `chungBeta d x ≤ y`, expansion at `y` gives the result immediately.  Otherwise,
reflecting the strip between `y` and `chungBeta d x` across the anti-diagonal puts it
strictly below the root based at `1 - chungBeta d x`; the exponent is negative there,
so the threshold at `y` lies strictly above `chungBeta d x`. -/
theorem chungBeta_strictMonoOn (d : ℝ) (hd : 2 < d) :
    StrictMonoOn (chungBeta d) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hβx := chungBeta_mem hd hx.1 hx.2
  have hβy := chungBeta_mem hd hy.1 hy.2
  by_cases hle : chungBeta d x ≤ y
  · exact hle.trans_lt hβy.1
  · have hyβ : y < chungBeta d x := lt_of_not_ge hle
    have hm0 : 0 < 1 - chungBeta d x := by linarith [hβx.2]
    have hm1 : 1 - chungBeta d x < 1 := by linarith [hx.1, hβx.1]
    have hmt : 1 - chungBeta d x < 1 - y := by linarith
    have ht1 : 1 - y < 1 := by linarith [hy.1]
    have hroot : chungBeta d (1 - chungBeta d x) = 1 - x :=
      chungBeta_reversal hd hx.1 hx.2
    have hnegMirror : sec d (1 - chungBeta d x) (1 - y) < 0 :=
      (sec_neg_iff hd hm0 hm1 hmt ht1).2 (by rw [hroot]; linarith)
    have hneg : sec d y (chungBeta d x) < 0 := by
      calc
        sec d y (chungBeta d x) = chungExponent d y (chungBeta d x) :=
          (chungExponent_eq_sec hy.1 hyβ hβx.2).symm
        _ = chungExponent d (1 - chungBeta d x) (1 - y) :=
          chungExponent_symm hy.1 hyβ hβx.2
        _ = sec d (1 - chungBeta d x) (1 - y) :=
          chungExponent_eq_sec hm0 hmt ht1
        _ < 0 := hnegMirror
    exact (sec_neg_iff hd hy.1 hy.2 hyβ hβx.2).1 hneg

/-! ### Numeric bracketing -/

/-- If the exponent is negative at `a`, the threshold is above `a`. -/
theorem lt_chungBeta {d x a : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1)
    (hxa : x < a) (ha1 : a < 1) (hneg : sec d x a < 0) : a < chungBeta d x :=
  (sec_neg_iff hd hx hx1 hxa ha1).mp hneg

/-- If the exponent is positive at `b`, the threshold is below `b`. -/
theorem chungBeta_lt {d x b : ℝ} (hd : 2 < d) (hx : 0 < x) (hx1 : x < 1)
    (hxb : x < b) (hb1 : b < 1) (hpos : 0 < sec d x b) : chungBeta d x < b := by
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt
  · have := sec_chungBeta hd hx hx1
    rw [← heq] at this; linarith
  · have := (sec_neg_iff hd hx hx1 hxb hb1).mpr hlt
    linarith

end ChungCurve
end ProofOfSpace

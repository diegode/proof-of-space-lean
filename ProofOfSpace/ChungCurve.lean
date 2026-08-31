/-
# The `y`-section of the Chung exponent, and its strict concavity

`Chung.lean` proves the anti-diagonal symmetry of the union-bound exponent.  This file
puts the exponent in Reyzin's closed form `sec` and proves the one analytic fact the
threshold theory rests on: for fixed `x`, the `y`-section is *strictly concave*.  Since
it is negative at `y = x` and positive at `y = 1`, it therefore has exactly one root, and
is negative exactly to the left of it.

That is what `ChungShifted.lean` turns into a threshold and a sign characterisation.
Nothing here claims that any graph attains the expansion the threshold describes; that is
the union bound's job, in `UnionBound.lean`.
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

end ChungCurve
end ProofOfSpace

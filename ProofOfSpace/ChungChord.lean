import ProofOfSpace.ChungShifted

/-!
# The Chung exponent along a straight chord

`ChungShifted.lean` constructs the finite-size threshold `shiftedBeta d ε` as an exact
root and records why that root cannot serve as a global `Setting.β`.  A rational polygon
is used instead, and the question this file settles is what it takes to certify one: are
the *vertices* enough?

They are, and the reason is elementary.  Restrict the exponent to a straight line
`y = p x + q`.  Every summand of `sec` is then `κ · g x · log (g x)` for an affine `g`,
so the restriction is a sum of five `affLog` terms whose second derivative

  `chordSec'' d p q x = -1/x + (d-1)/(1-x) + (d-1) p²/y - p²/(1-y) - d (p-1)²/(y-x)`

is a *rational* function of `x`: no logarithm survives differentiating twice.  Wherever
that rational function is positive the restriction is strictly convex, hence bounded
above by its endpoint values, and two vertex certificates carry the entire segment
between them.

This replaces the implicit-function route.  No curvature bound on the level set and no
`C²` smoothness of `shiftedBeta` is required.
-/

namespace ProofOfSpace
namespace ChungCurve

open Real Set

/-! ### `t log t` along an affine map -/

/-- `t log t` precomposed with the affine map `x ↦ p x + q`.  Every summand of `sec`
restricted to a chord has this shape. -/
noncomputable def affLog (p q x : ℝ) : ℝ := (p * x + q) * log (p * x + q)

/-- The derivative of `affLog p q`. -/
noncomputable def affLog' (p q x : ℝ) : ℝ := p * (log (p * x + q) + 1)

theorem continuous_affLog (p q : ℝ) : Continuous (affLog p q) :=
  Real.continuous_mul_log.comp (by fun_prop)

theorem hasDerivAt_affine (p q x : ℝ) : HasDerivAt (fun t : ℝ => p * t + q) p x := by
  simpa using ((hasDerivAt_id x).const_mul p).add_const q

theorem hasDerivAt_affLog {p q x : ℝ} (h : p * x + q ≠ 0) :
    HasDerivAt (affLog p q) (affLog' p q x) x := by
  change HasDerivAt (fun t : ℝ => (p * t + q) * log (p * t + q)) (affLog' p q x) x
  have hu : HasDerivAt (fun t : ℝ => p * t + q) p x := hasDerivAt_affine p q x
  have key : affLog' p q x = p * log (p * x + q) + (p * x + q) * (p / (p * x + q)) := by
    simp only [affLog']
    field_simp
  rw [key]
  exact hu.mul (hu.log h)

theorem hasDerivAt_affLog' {p q x : ℝ} (h : p * x + q ≠ 0) :
    HasDerivAt (affLog' p q) (p * p / (p * x + q)) x := by
  change HasDerivAt (fun t : ℝ => p * (log (p * t + q) + 1)) (p * p / (p * x + q)) x
  have hu : HasDerivAt (fun t : ℝ => p * t + q) p x := hasDerivAt_affine p q x
  have key : p * p / (p * x + q) = p * (p / (p * x + q)) := by ring
  rw [key]
  exact ((hu.log h).add_const 1).const_mul p

/-! ### The section along a chord -/

/-- The finite-size Chung exponent restricted to the line `y = p x + q`. -/
noncomputable def chordSec (d ε p q x : ℝ) : ℝ := shiftedSec d ε x (p * x + q)

/-- Its derivative. -/
noncomputable def chordSec' (d p q x : ℝ) : ℝ :=
  -affLog' 1 0 x + (d - 1) * affLog' (-1) 1 x + (d - 1) * affLog' p q x
    - affLog' (-p) (1 - q) x - d * affLog' (p - 1) q x

/-- Its second derivative: a rational function of `x`. -/
noncomputable def chordSec'' (d p q x : ℝ) : ℝ :=
  -(1 / x) + (d - 1) / (1 - x) + (d - 1) * p ^ 2 / (p * x + q)
    - p ^ 2 / (1 - (p * x + q)) - d * (p - 1) ^ 2 / (p * x + q - x)

/-- The five-term `affLog` expansion.  This is `binEntropy_eq_neg` and a rearrangement,
so it holds for every `x`. -/
theorem chordSec_eq (d ε p q x : ℝ) :
    chordSec d ε p q x =
      -affLog 1 0 x + (d - 1) * affLog (-1) 1 x + (d - 1) * affLog p q x
        - affLog (-p) (1 - q) x - d * affLog (p - 1) q x + ε := by
  have h1 : (1 : ℝ) * x + 0 = x := by ring
  have h2 : (-1 : ℝ) * x + 1 = 1 - x := by ring
  have h3 : (-p) * x + (1 - q) = 1 - (p * x + q) := by ring
  have h4 : (p - 1) * x + q = p * x + q - x := by ring
  simp only [chordSec, shiftedSec, sec, binEntropy_eq_neg, affLog, h1, h2, h3, h4]
  ring

theorem continuous_chordSec (d ε p q : ℝ) : Continuous (chordSec d ε p q) := by
  have h : chordSec d ε p q = fun x =>
      -affLog 1 0 x + (d - 1) * affLog (-1) 1 x + (d - 1) * affLog p q x
        - affLog (-p) (1 - q) x - d * affLog (p - 1) q x + ε :=
    funext (chordSec_eq d ε p q)
  rw [h]
  exact ((((continuous_affLog 1 0).neg.add
    (continuous_const.mul (continuous_affLog (-1) 1))).add
    (continuous_const.mul (continuous_affLog p q))).sub
    (continuous_affLog (-p) (1 - q))).sub
    (continuous_const.mul (continuous_affLog (p - 1) q)) |>.add continuous_const

/-! ### The scaling form on a chord through the origin

The two extreme segments run to the degenerate corners, where the finite-size region is
empty and no vertex certificate exists.  A chord through the origin, `y = c x`, has a
closed form in which `log x` appears linearly, so a single certificate at a tiny dyadic
abscissa is enough to start the induction.  Its `log` values are `-k log 2` plus the
two constants `log c` and `log (c-1)`. -/

/-- `-(1-t) log (1-t) ≤ t`: the elementary upper bound used at the degenerate corner. -/
theorem neg_one_sub_mul_log_le {t : ℝ} (ht1 : t < 1) :
    -((1 - t) * log (1 - t)) ≤ t := by
  have h1 : (0 : ℝ) < 1 - t := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - t)⁻¹ by positivity)
  rw [Real.log_inv] at h
  have hkey : -log (1 - t) ≤ t / (1 - t) := by
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  calc -((1 - t) * log (1 - t)) = (1 - t) * (-log (1 - t)) := by ring
    _ ≤ (1 - t) * (t / (1 - t)) := by
        exact mul_le_mul_of_nonneg_left hkey h1.le
    _ = t := by field_simp

/-- The exponent along the ray `y = c x`, with `log x` isolated. -/
theorem shiftedSec_scaling {d ε c x : ℝ} (hx : 0 < x) (hc : 1 < c) :
    shiftedSec d ε x (c * x) =
      x * ((d - 1 - c) * log x + (d - 1) * c * log c - d * (c - 1) * log (c - 1))
        + (d - 1) * ((1 - x) * log (1 - x)) - (1 - c * x) * log (1 - c * x) + ε := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hsub : c * x - x = (c - 1) * x := by ring
  have l1 : log (c * x) = log c + log x := Real.log_mul (ne_of_gt hc0) (ne_of_gt hx)
  have l2 : log (c * x - x) = log (c - 1) + log x := by
    rw [hsub, Real.log_mul (ne_of_gt hc1) (ne_of_gt hx)]
  simp only [shiftedSec, sec, binEntropy_eq_neg, l1, l2]
  ring

/-- A single scalar inequality certifies a point of the ray `y = c x`. -/
theorem shiftedSec_neg_of_scaling {d ε c x : ℝ} (hd : 1 ≤ d) (hx : 0 < x) (hx1 : x < 1)
    (hc : 1 < c) (hcx : c * x < 1)
    (hcert : x * ((d - 1 - c) * log x + (d - 1) * c * log c
      - d * (c - 1) * log (c - 1) + c) + ε < 0) :
    shiftedSec d ε x (c * x) < 0 := by
  rw [shiftedSec_scaling hx hc]
  have h1 : (1 - x) * log (1 - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (Real.log_nonpos (by linarith) (by linarith))
  have h2 : -((1 - c * x) * log (1 - c * x)) ≤ c * x := neg_one_sub_mul_log_le hcx
  nlinarith

/-! ### Positivity of the rational second derivative

Three shapes suffice for a reversal-symmetric polygon.  A generic segment is handled by
bounding each of the five terms by its extreme value over the segment; the two segments
that run into the degenerate corners have singular terms that cancel exactly, and are
handled by the two rewriting lemmas below. -/

/-- Term-by-term lower bound on a segment.  `u` bounds `x` from below, `v` bounds the
chord value from above, and `w` bounds the gap `y - x` from below. -/
theorem chordSec''_pos {d p q x u v w : ℝ} (hd : 1 ≤ d)
    (hu : 0 < u) (hxu : u ≤ x)
    (hxv : p * x + q ≤ v) (hv1 : v < 1)
    (hw : 0 < w) (hxw : w ≤ p * x + q - x)
    (hcert : 0 < -(1 / u) + (d - 1) / (1 - u) + (d - 1) * p ^ 2 / v
      - p ^ 2 / (1 - v) - d * (p - 1) ^ 2 / w) :
    0 < chordSec'' d p q x := by
  have hx : 0 < x := lt_of_lt_of_le hu hxu
  have hxy : x < p * x + q := by linarith
  have hx1 : x < 1 := by linarith
  have hu1 : u < 1 := lt_of_le_of_lt hxu hx1
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hv : (0 : ℝ) < v := by linarith
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have hy : (0 : ℝ) < p * x + q := by linarith
  have h1y : (0 : ℝ) < 1 - (p * x + q) := by linarith
  have hgx : (0 : ℝ) < p * x + q - x := by linarith
  have hd1 : (0 : ℝ) ≤ d - 1 := by linarith
  have t1 : 1 / x ≤ 1 / u := one_div_le_one_div_of_le hu hxu
  have t2 : (d - 1) / (1 - u) ≤ (d - 1) / (1 - x) :=
    div_le_div_of_nonneg_left hd1 h1x (by linarith)
  have t3 : (d - 1) * p ^ 2 / v ≤ (d - 1) * p ^ 2 / (p * x + q) :=
    div_le_div_of_nonneg_left (by positivity) hy hxv
  have t4 : p ^ 2 / (1 - (p * x + q)) ≤ p ^ 2 / (1 - v) :=
    div_le_div_of_nonneg_left (by positivity) h1v (by linarith)
  have t5 : d * (p - 1) ^ 2 / (p * x + q - x) ≤ d * (p - 1) ^ 2 / w :=
    div_le_div_of_nonneg_left (by positivity) hw hxw
  simp only [chordSec'']
  linarith

/-- On a chord through the origin the three singular terms collapse. -/
theorem chordSec''_ray_eq {d p x : ℝ} (hx : x ≠ 0) (hp : p ≠ 0) (hp1 : p - 1 ≠ 0)
    (h1x : (1 : ℝ) - x ≠ 0) (_h1y : (1 : ℝ) - p * x ≠ 0) :
    chordSec'' d p 0 x =
      (d - 1 - p) / x + (d - 1) / (1 - x) - p ^ 2 / (1 - p * x) := by
  have hpx : p * x ≠ 0 := mul_ne_zero hp hx
  have hgx : p * x + 0 - x ≠ 0 := by
    have : p * x + 0 - x = (p - 1) * x := by ring
    rw [this]
    exact mul_ne_zero hp1 hx
  simp only [chordSec'', add_zero]
  field_simp
  ring

/-- On the closing chord, which ends at `(1,1)`, the same three terms collapse. -/
theorem chordSec''_top_eq {d p x : ℝ} (hx : x ≠ 0) (_hp : p ≠ 0) (hp1 : p - 1 ≠ 0)
    (h1x : (1 : ℝ) - x ≠ 0) (_hy : p * x + (1 - p) ≠ 0) :
    chordSec'' d p (1 - p) x =
      -(1 / x) + ((d - 1) * p - 1) / (1 - x) + (d - 1) * p ^ 2 / (p * x + (1 - p)) := by
  have e1 : (1 : ℝ) - (p * x + (1 - p)) = p * (1 - x) := by ring
  have e2 : p * x + (1 - p) - x = -(p - 1) * (1 - x) := by ring
  have hp1' : -(p - 1) ≠ 0 := neg_ne_zero.mpr hp1
  simp only [chordSec'', e1, e2]
  field_simp
  ring

/-! ### The chord domain -/

/-- Where the chord stays inside the open triangle `0 < x < y < 1`. -/
def ChordDomain (p q : ℝ) : Set ℝ := {x | 0 < x ∧ x < p * x + q ∧ p * x + q < 1}

theorem isOpen_chordDomain (p q : ℝ) : IsOpen (ChordDomain p q) := by
  have h1 : Continuous fun x : ℝ => p * x + q := by fun_prop
  exact (isOpen_lt continuous_const continuous_id).inter
    ((isOpen_lt continuous_id h1).inter (isOpen_lt h1 continuous_const))

theorem hasDerivAt_chordSec {d ε p q x : ℝ} (hx : x ∈ ChordDomain p q) :
    HasDerivAt (chordSec d ε p q) (chordSec' d p q x) x := by
  obtain ⟨hx0, hxy, hy1⟩ := hx
  have hx1 : x < 1 := hxy.trans hy1
  have e1 : (1 : ℝ) * x + 0 ≠ 0 := by intro h; apply absurd h; nlinarith
  have e2 : (-1 : ℝ) * x + 1 ≠ 0 := by intro h; apply absurd h; nlinarith
  have e3 : p * x + q ≠ 0 := by intro h; apply absurd h; nlinarith
  have e4 : (-p) * x + (1 - q) ≠ 0 := by intro h; apply absurd h; nlinarith
  have e5 : (p - 1) * x + q ≠ 0 := by intro h; apply absurd h; nlinarith
  have h := ((((hasDerivAt_affLog e1).neg.add
    ((hasDerivAt_affLog e2).const_mul (d - 1))).add
    ((hasDerivAt_affLog e3).const_mul (d - 1))).sub
    (hasDerivAt_affLog e4)).sub
    ((hasDerivAt_affLog e5).const_mul d) |>.add_const ε
  have heq : chordSec d ε p q = fun x =>
      -affLog 1 0 x + (d - 1) * affLog (-1) 1 x + (d - 1) * affLog p q x
        - affLog (-p) (1 - q) x - d * affLog (p - 1) q x + ε :=
    funext (chordSec_eq d ε p q)
  rw [heq]
  exact h

theorem hasDerivAt_chordSec' {d p q x : ℝ} (hx : x ∈ ChordDomain p q) :
    HasDerivAt (chordSec' d p q) (chordSec'' d p q x) x := by
  obtain ⟨hx0, hxy, hy1⟩ := hx
  have hx1 : x < 1 := hxy.trans hy1
  have e1 : (1 : ℝ) * x + 0 ≠ 0 := by intro h; apply absurd h; nlinarith
  have e2 : (-1 : ℝ) * x + 1 ≠ 0 := by intro h; apply absurd h; nlinarith
  have e3 : p * x + q ≠ 0 := by intro h; apply absurd h; nlinarith
  have e4 : (-p) * x + (1 - q) ≠ 0 := by intro h; apply absurd h; nlinarith
  have e5 : (p - 1) * x + q ≠ 0 := by intro h; apply absurd h; nlinarith
  have h := ((((hasDerivAt_affLog' e1).neg.add
    ((hasDerivAt_affLog' e2).const_mul (d - 1))).add
    ((hasDerivAt_affLog' e3).const_mul (d - 1))).sub
    (hasDerivAt_affLog' e4)).sub
    ((hasDerivAt_affLog' e5).const_mul d)
  refine h.congr_deriv ?_
  have d1 : (1 : ℝ) * x + 0 = x := by ring
  have d2 : (-1 : ℝ) * x + 1 = 1 - x := by ring
  have d4 : (-p) * x + (1 - q) = 1 - (p * x + q) := by ring
  have d5 : (p - 1) * x + q = p * x + q - x := by ring
  rw [d1, d2, d4, d5]
  simp only [chordSec'']
  ring

theorem deriv2_chordSec_eq {d ε p q x : ℝ} (hx : x ∈ ChordDomain p q) :
    deriv^[2] (chordSec d ε p q) x = chordSec'' d p q x := by
  have hnhds : ChordDomain p q ∈ nhds x := (isOpen_chordDomain p q).mem_nhds hx
  have heq : deriv (chordSec d ε p q) =ᶠ[nhds x] chordSec' d p q := by
    filter_upwards [hnhds] with t ht using (hasDerivAt_chordSec (d := d) (ε := ε) ht).deriv
  change deriv (deriv (chordSec d ε p q)) x = _
  rw [heq.deriv_eq]
  exact (hasDerivAt_chordSec' hx).deriv

/-! ### Strict convexity and the endpoint principle -/

theorem strictConvexOn_chordSec {d ε p q a b : ℝ}
    (hdom : Icc a b ⊆ ChordDomain p q)
    (hpos : ∀ x ∈ Ioo a b, 0 < chordSec'' d p q x) :
    StrictConvexOn ℝ (Icc a b) (chordSec d ε p q) := by
  refine strictConvexOn_of_deriv2_pos (convex_Icc a b)
    (continuous_chordSec d ε p q).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv2_chordSec_eq (d := d) (ε := ε) (hdom (Ioo_subset_Icc_self hx))]
  exact hpos x hx

/-- **Two vertices carry the segment.**  A chord whose restricted exponent is convex and
strictly negative at both endpoints is strictly negative along its whole length. -/
theorem chordSec_neg_of_endpoints {d ε p q a b : ℝ} (hab : a ≤ b)
    (hdom : Icc a b ⊆ ChordDomain p q)
    (hpos : ∀ x ∈ Ioo a b, 0 < chordSec'' d p q x)
    (ha : chordSec d ε p q a < 0) (hb : chordSec d ε p q b < 0)
    {x : ℝ} (hx : x ∈ Icc a b) : chordSec d ε p q x < 0 :=
  lt_of_le_of_lt
    ((strictConvexOn_chordSec hdom hpos).convexOn.le_max_of_mem_Icc
      (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hx)
    (max_lt ha hb)

/-- The same statement in the `shiftedSec` interface: the whole chord lies strictly
inside the finite-size Chung region. -/
theorem shiftedSec_neg_on_chord {d ε p q a b : ℝ} (hab : a ≤ b)
    (hdom : Icc a b ⊆ ChordDomain p q)
    (hpos : ∀ x ∈ Ioo a b, 0 < chordSec'' d p q x)
    (ha : shiftedSec d ε a (p * a + q) < 0) (hb : shiftedSec d ε b (p * b + q) < 0)
    {x : ℝ} (hx : x ∈ Icc a b) : shiftedSec d ε x (p * x + q) < 0 :=
  chordSec_neg_of_endpoints (ε := ε) hab hdom hpos ha hb hx

end ChungCurve
end ProofOfSpace

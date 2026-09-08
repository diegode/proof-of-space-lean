/-
# The Chung union-bound exponent and its anti-diagonal symmetry

This file proves the analytic half of the expander-specific input of the latency
analysis: the union-bound exponent controlling the failure probability of a random
degree-`d` Chung graph,

  `E(x,y) = H(x) + H(y) + d (y H(x/y) - H(x))`,

is invariant under the anti-diagonal reflection `(x,y) ↦ (1-y, 1-x)`
(`chungExponent_symm`).  This is Reyzin's computation, proved outright from the closed
form `y H(x/y) - H(x) = (x-y) log (y-x) + y log y + (1-x) log (1-x)`.

That symmetry is what yields the reversal law `β (1 - β α) = 1 - α` — Proposition
`reversal identity` of this development,
= Claim 13 of Reyzin, *Proofs of Space with Maximal Hardness*, FOCS 2024.  The reversal
law itself is proved in `ChungCurve.lean` (`chungBeta_reversal`), directly for the
constructed threshold rather than through an abstract interface.
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace ProofOfSpace

open Real

/-! ## The union-bound exponent -/

/-- The union-bound exponent for a random degree-`d` Chung graph:
`E(x, y) = H(x) + H(y) + d (y H(x/y) - H(x))`.
Expansion from density `x` to density `y` is certified whenever this is negative. -/
noncomputable def chungExponent (d x y : ℝ) : ℝ :=
  binEntropy x + binEntropy y + d * (y * binEntropy (x / y) - binEntropy x)

/-- The binary entropy in the `-p log p - (1-p) log (1-p)` form. -/
theorem binEntropy_eq_neg (p : ℝ) :
    binEntropy p = -(p * log p) - (1 - p) * log (1 - p) := by
  simp [binEntropy, Real.log_inv]
  ring

/-- Reyzin's closed form for the degree-dependent part of the exponent:
`y H(x/y) - H(x) = (x - y) log (y - x) + y log y + (1 - x) log (1 - x)`. -/
theorem mul_binEntropy_div_sub_binEntropy {x y : ℝ} (hx : 0 < x) (hxy : x < y) (_hy : y < 1) :
    y * binEntropy (x / y) - binEntropy x
      = (x - y) * log (y - x) + y * log y + (1 - x) * log (1 - x) := by
  have hy0 : (0:ℝ) < y := hx.trans hxy
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsub : (0:ℝ) < y - x := sub_pos.mpr hxy
  have hsubne : y - x ≠ 0 := ne_of_gt hsub
  have hone : (1:ℝ) - x / y = (y - x) / y := by field_simp
  rw [binEntropy_eq_neg, binEntropy_eq_neg, hone, Real.log_div hxne hyne,
    Real.log_div hsubne hyne]
  field_simp
  ring

/-- **The anti-diagonal symmetry of the Chung exponent.**
`E(x, y) = E(1 - y, 1 - x)` for `0 < x < y < 1`.  This is the analytic content of
`reversal identity`. -/
theorem chungExponent_symm {d x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    chungExponent d x y = chungExponent d (1 - y) (1 - x) := by
  have h1 := mul_binEntropy_div_sub_binEntropy hx hxy hy
  have h2 := mul_binEntropy_div_sub_binEntropy (x := 1 - y) (y := 1 - x)
    (by linarith) (by linarith) (by linarith)
  rw [show (1 : ℝ) - x - (1 - y) = y - x from by ring,
    show (1 : ℝ) - (1 - y) = y from by ring, binEntropy_one_sub] at h2
  simp only [chungExponent, binEntropy_one_sub]
  rw [h1, h2]
  ring

end ProofOfSpace

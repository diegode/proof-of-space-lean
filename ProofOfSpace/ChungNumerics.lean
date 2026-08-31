import ProofOfSpace.ChungFilecoinCurve

/-!
# Rational constants for the Chung-8 latency theorems

Only the exact rational evaluations consumed by `chung8Tracking` and the potential
ledger are retained here. The probabilistic expansion theorem uses the finite
combinatorial bound in `UnionBound.lean` directly and does not need logarithmic
approximations to the asymptotic Chung exponent.
-/

namespace ProofOfSpace
namespace ChungCurve

/-- The adjusted gain of the degree-eight polygon at `δ = 0.0378`. -/
noncomputable def gainD8 (t : ℝ) : ℝ := filecoinBeta t - 189 / 5000 - t

/-- `g_π = gain_δ(0.8)`. -/
noncomputable def gpi8 : ℝ := gainD8 (4 / 5)

/-- The tracked source satisfies `gain_δ(σ) ≥ 2 g_π`. -/
theorem condB_holds_at_1184 : 2 * gpi8 ≤ gainD8 (74 / 625) := by
  norm_num [gainD8, gpi8]

/-- The rational interval used by the latency accounting. -/
theorem gpi8_bounds : (1113 : ℝ) / 10000 < gpi8 ∧ gpi8 < (557 : ℝ) / 5000 := by
  norm_num [gpi8, gainD8]

/-- The doubled tracking gain remains valid at the chosen midpoint. -/
theorem two_gpi_le_gainD8_06 : 2 * gpi8 ≤ gainD8 (3 / 5) := by
  norm_num [gainD8, gpi8]

end ChungCurve
end ProofOfSpace

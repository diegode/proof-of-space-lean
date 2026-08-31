import ProofOfSpace.ChungFilecoin
import ProofOfSpace.UnionBound

/-!
# The Chung-8 profile is realised with high probability

`UnionBound.lean` proves `PermutationExpansionWhpClaim` from an inequality between two
natural numbers.  This file discharges that inequality for the finite-size Chung-8
profile at width `n = 20` and degree `d = 8`, so the claim becomes an unconditional
theorem with an explicit, non-trivial failure probability:

  a uniformly sampled `8`-tuple of permutations of a `20`-element layer realises the
  Filecoin polygon's expansion with probability at least `5 / 6`.

Two honest remarks about the size of this statement.  First, the width `20` is chosen so
that the certificate is a comparison of two 150-digit integers, decided by the kernel;
`UnionBound.lean` itself is uniform in `n`.  Raising `n` alone would not buy much,
though: the union bound is governed by `exp(n · max E₈(x, β x))`, and the tightest
vertex has `E₈ ≈ -1.6·10⁻⁵`, so the failure bound only starts to decay once `n` is far
past `10⁵`; a small `δ` at deployed widths needs two-sided binomial-entropy estimates
that Mathlib does not currently carry.  Second, this closes the probabilistic gap in the
development's *own* sampling model: the deployed Filecoin interlayer is a Feistel
permutation network, not a uniform tuple of permutations.
-/

namespace ProofOfSpace
namespace Concrete

open Finset
open scoped ENNReal

/-- The failure profile of the Chung-8 polygon at width `20`: `chung8Fail20 k` is the
largest neighbourhood size that still fails the expansion requirement on a `k`-set. -/
def chung8Fail20 : ℕ → ℕ
  | 1 => 3 | 2 => 6 | 3 => 8 | 4 => 10 | 5 => 11 | 6 => 13 | 7 => 14 | 8 => 14
  | 9 => 15 | 10 => 16 | 11 => 16 | 12 => 17 | 13 => 17 | 14 => 18 | 15 => 18
  | 16 => 18 | 17 => 19 | 18 => 19 | 19 => 19 | 20 => 19
  | _ => 0

theorem chung8Fail20_le (k : ℕ) : chung8Fail20 k ≤ 20 := by
  unfold chung8Fail20
  split <;> norm_num

/-- Each value really is an admissible failure size: the polygon's requirement at `k/20`
is below `chung8Fail20 k + 1`. -/
theorem chung8Fail20_spec (k : ℕ) (hk : k ≤ 20) :
    ChungCurve.chung8Setting.β (k / 20) * 20 ≤ (chung8Fail20 k : ℝ) + 1 := by
  have hb : ChungCurve.chung8Setting.β = ChungCurve.filecoinBeta := rfl
  rw [hb]
  interval_cases k <;> simp only [chung8Fail20]
  · have h := ChungCurve.filecoinBeta_le_affine_0 ((0 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_0 ((1 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_2 ((2 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_3 ((3 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_4 ((4 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_5 ((5 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_5 ((6 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_6 ((7 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_6 ((8 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_7 ((9 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_7 ((10 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_8 ((11 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_8 ((12 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_9 ((13 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_9 ((14 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_10 ((15 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_10 ((16 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_11 ((17 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_11 ((18 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_11 ((19 : ℝ) / 20)
    push_cast
    linarith
  · have h := ChungCurve.filecoinBeta_le_affine_11 ((20 : ℝ) / 20)
    push_cast
    linarith

/-- **The Chung-8 polygon is realised with probability at least `5 / 6` at width 20.**
This is `PermutationExpansionWhpClaim` — the proposition `Constructions.lean` isolates
as the development's probabilistic gap — proved outright. -/
theorem chung8_permutationExpansion_whp :
    PermutationExpansionWhpClaim ChungCurve.chung8Setting 20 8 ((1 : ℝ≥0∞) / (6 : ℝ≥0∞)) := by
  have h := permutationExpansion_whp ChungCurve.chung8Setting 20 8 chung8Fail20
    chung8Fail20_spec chung8Fail20_le (a := 1) (b := 6) (by norm_num) (by decide)
  simpa using h

end Concrete
end ProofOfSpace

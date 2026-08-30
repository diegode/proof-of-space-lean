/-
# Numerical certificates for the Chung curve

The Filecoin instantiation of `cor:filecoin` fixes `δ = 0.0378` and needs
the source condition `gain_δ(σ) ≥ 2 g_π`,

  `gain_δ(σ) ≥ 2 g_π`,   where `gain_δ(t) = β₈(t) - δ - t` and `g_π = gain_δ(0.8)`.

Here that condition is *decided* rather than assumed, for the curve `β₈` constructed in
`ChungCurve.lean`.  The outcome is that `σ_min` must be rounded up:

* `condB_fails_at_118`  — `σ = 0.118` violates the source condition `gain_δ(σ) ≥ 2 g_π`;
* `condB_holds_at_1184` — `σ = 0.1184` satisfies it.

Everything reduces, via `lt_chungBeta` / `chungBeta_lt`, to the sign of the exponent at
four explicit rationals.  Those signs are settled by bracketing the logarithms involved:
each `log (a/b)` is rescaled by a power of two into the fast-convergence range and then
bounded by the Mercator series with Mathlib's explicit tail estimate
`Real.abs_log_sub_add_sum_range_le`, together with the ten-digit bounds on `log 2`.
-/
import ProofOfSpace.ChungCurve
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProofOfSpace
namespace ChungCurve

open Real Set


/-! ### Logarithm brackets (each accurate to `1e-8`) -/

theorem log_4_5 :
    (-0.223143561314 : ℝ) < log ((4 : ℝ)/5) ∧ log ((4 : ℝ)/5) < (-0.223143541314 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/5)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_1_5 :
    (-1.609437922434 : ℝ) < log ((1 : ℝ)/5) ∧ log ((1 : ℝ)/5) < (-1.609437902434 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/5)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (1 : ℝ)/5 = ((4 : ℝ)/5) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_74_625 :
    (-2.133686566532 : ℝ) < log ((74 : ℝ)/625) ∧ log ((74 : ℝ)/625) < (-2.133686546532 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((33 : ℝ)/625)) (by norm_num) 10
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (74 : ℝ)/625 = ((592 : ℝ)/625) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_551_625 :
    (-0.126016850583 : ℝ) < log ((551 : ℝ)/625) ∧ log ((551 : ℝ)/625) < (-0.126016830583 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((74 : ℝ)/625)) (by norm_num) 13
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_59_500 :
    (-2.137070664516 : ℝ) < log ((59 : ℝ)/500) ∧ log ((59 : ℝ)/500) < (-2.137070644516 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((7 : ℝ)/125)) (by norm_num) 10
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (59 : ℝ)/500 = ((118 : ℝ)/125) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_441_500 :
    (-0.125563232975 : ℝ) < log ((441 : ℝ)/500) ∧ log ((441 : ℝ)/500) < (-0.125563212975 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((59 : ℝ)/500)) (by norm_num) 13
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_2966_3125 :
    (-0.052220049473 : ℝ) < log ((2966 : ℝ)/3125) ∧
      log ((2966 : ℝ)/3125) < (-0.052220029473 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((159 : ℝ)/3125)) (by norm_num) 10
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_159_3125 :
    (-2.978285369950 : ℝ) < log ((159 : ℝ)/3125) ∧
      log ((159 : ℝ)/3125) < (-2.978285349950 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((581 : ℝ)/3125)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (159 : ℝ)/3125 = ((2544 : ℝ)/3125) / 2^4 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^4) = 4 * Real.log 2 := by
    rw [show ((2:ℝ)^4) = (2:ℝ)^(4:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_466_3125 :
    (-1.903003938045 : ℝ) < log ((466 : ℝ)/3125) ∧
      log ((466 : ℝ)/3125) < (-1.903003918045 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-603 : ℝ)/3125)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (466 : ℝ)/3125 = ((3728 : ℝ)/3125) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_3031_8000 :
    (-0.970548953604 : ℝ) < log ((3031 : ℝ)/8000) ∧
      log ((3031 : ℝ)/8000) < (-0.970548933604 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((969 : ℝ)/4000)) (by norm_num) 20
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (3031 : ℝ)/8000 = ((3031 : ℝ)/4000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_4969_8000 :
    (-0.476222939060 : ℝ) < log ((4969 : ℝ)/8000) ∧
      log ((4969 : ℝ)/8000) < (-0.476222919060 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-969 : ℝ)/4000)) (by norm_num) 20
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (4969 : ℝ)/8000 = ((4969 : ℝ)/4000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_10419_40000 :
    (-1.345248401684 : ℝ) < log ((10419 : ℝ)/40000) ∧
      log ((10419 : ℝ)/40000) < (-1.345248381684 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-419 : ℝ)/10000)) (by norm_num) 9
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (10419 : ℝ)/40000 = ((10419 : ℝ)/10000) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_5907_15625 :
    (-0.972734117297 : ℝ) < log ((5907 : ℝ)/15625) ∧
      log ((5907 : ℝ)/15625) < (-0.972734097297 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((3811 : ℝ)/15625)) (by norm_num) 20
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (5907 : ℝ)/15625 = ((11814 : ℝ)/15625) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_9718_15625 :
    (-0.474892369639 : ℝ) < log ((9718 : ℝ)/15625) ∧
      log ((9718 : ℝ)/15625) < (-0.474892349639 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-3811 : ℝ)/15625)) (by norm_num) 20
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (9718 : ℝ)/15625 = ((19436 : ℝ)/15625) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_16253_62500 :
    (-1.346889059621 : ℝ) < log ((16253 : ℝ)/62500) ∧
      log ((16253 : ℝ)/62500) < (-1.346889039621 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-628 : ℝ)/15625)) (by norm_num) 9
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (16253 : ℝ)/62500 = ((16253 : ℝ)/15625) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_94911_100000 :
    (-0.052230585604 : ℝ) < log ((94911 : ℝ)/100000) ∧
      log ((94911 : ℝ)/100000) < (-0.052230565604 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((5089 : ℝ)/100000)) (by norm_num) 10
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_5089_100000 :
    (-2.978088848381 : ℝ) < log ((5089 : ℝ)/100000) ∧
      log ((5089 : ℝ)/100000) < (-2.978088828381 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1161 : ℝ)/6250)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (5089 : ℝ)/100000 = ((5089 : ℝ)/6250) / 2^4 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^4) = 4 * Real.log 2 := by
    rw [show ((2:ℝ)^4) = (2:ℝ)^(4:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_14911_100000 :
    (-1.903071000379 : ℝ) < log ((14911 : ℝ)/100000) ∧
      log ((14911 : ℝ)/100000) < (-1.903070980379 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-2411 : ℝ)/12500)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (14911 : ℝ)/100000 = ((14911 : ℝ)/12500) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! ### Brackets for the `σ̃ = 3/5` mid-point certificate -/

theorem log_3_5 :
    (-0.510825625006 : ℝ) < log ((3 : ℝ)/5) ∧ log ((3 : ℝ)/5) < (-0.510825622506 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-1 : ℝ)/5)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (3 : ℝ)/5 = ((6 : ℝ)/5) / 2 := by norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num)]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_2_5 :
    (-0.916290733115 : ℝ) < log ((2 : ℝ)/5) ∧ log ((2 : ℝ)/5) < (-0.916290730614 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/5)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (2 : ℝ)/5 = ((4 : ℝ)/5) / 2 := by norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num)]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_173_200 :
    (-0.145025773056 : ℝ) < log ((173 : ℝ)/200) ∧
      log ((173 : ℝ)/200) < (-0.145025771044 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((27 : ℝ)/200)) (by norm_num) 12
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_27_200 :
    (-2.002480502264 : ℝ) < log ((27 : ℝ)/200) ∧
      log ((27 : ℝ)/200) < (-2.002480498764 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-2 : ℝ)/25)) (by norm_num) 12
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (27 : ℝ)/200 = ((27 : ℝ)/25) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_53_200 :
    (-1.328025454476 : ℝ) < log ((53 : ℝ)/200) ∧
      log ((53 : ℝ)/200) < (-1.328025451476 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-3 : ℝ)/50)) (by norm_num) 12
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (53 : ℝ)/200 = ((53 : ℝ)/50) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! ### Brackets for the left-root certificate

`log_255_256`, `log_31_32` and `log_7_8` are the three series needed to decide the sign
of the exponent at `(x, y) = (1/256, 1/32)`.  Both coordinates are powers of two and
`y - x = 7/256`, so every logarithm in `sec` reduces to `log 2` plus a Mercator series
with argument at most `1/8`; five terms already suffice for `1/256`. -/

theorem log_255_256 :
    (-0.003913899331 : ℝ) < log ((255 : ℝ)/256) ∧
      log ((255 : ℝ)/256) < (-0.003913899311 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/256)) (by norm_num) 5
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_31_32 :
    (-0.031748698325 : ℝ) < log ((31 : ℝ)/32) ∧
      log ((31 : ℝ)/32) < (-0.031748698304 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/32)) (by norm_num) 8
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_7_8 :
    (-0.133531392635 : ℝ) < log ((7 : ℝ)/8) ∧
      log ((7 : ℝ)/8) < (-0.133531392614 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1 : ℝ)/8)) (by norm_num) 15
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_1_256 : log ((1 : ℝ)/256) = -8 * Real.log 2 := by
  rw [show ((1 : ℝ)/256) = ((2 : ℝ)^(8 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
  ring

theorem log_1_32 : log ((1 : ℝ)/32) = -5 * Real.log 2 := by
  rw [show ((1 : ℝ)/32) = ((2 : ℝ)^(5 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
  ring

theorem log_7_256 : log ((7 : ℝ)/256) = log ((7 : ℝ)/8) - 5 * Real.log 2 := by
  rw [show ((7 : ℝ)/256) = ((7 : ℝ)/8) / (2 : ℝ)^(5 : ℕ) by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  ring

/-! ### Signs of the exponent at four explicit points -/

theorem sec_neg_08_lower : sec 8 (4/5) (94911/100000) < 0 := by
  have e1 := log_4_5; have e2 := log_1_5
  have e3 := log_94911_100000; have e4 := log_5089_100000; have e5 := log_14911_100000
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_pos_08_upper : 0 < sec 8 (4/5) (2966/3125) := by
  have e1 := log_4_5; have e2 := log_1_5
  have e3 := log_2966_3125; have e4 := log_159_3125; have e5 := log_466_3125
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_neg_1184_lower : sec 8 (74/625) (3031/8000) < 0 := by
  have e1 := log_74_625; have e2 := log_551_625
  have e3 := log_3031_8000; have e4 := log_4969_8000; have e5 := log_10419_40000
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_pos_118_upper : 0 < sec 8 (59/500) (5907/15625) := by
  have e1 := log_59_500; have e2 := log_441_500
  have e3 := log_5907_15625; have e4 := log_9718_15625; have e5 := log_16253_62500
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-! ### Brackets for the threshold curve -/

theorem beta_08_lower : (94911 : ℝ)/100000 < chungBeta 8 (4/5) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_08_lower

theorem beta_08_upper : chungBeta 8 (4/5) < (2966 : ℝ)/3125 :=
  chungBeta_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_pos_08_upper

theorem beta_1184_lower : (3031 : ℝ)/8000 < chungBeta 8 (74/625) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_1184_lower

theorem beta_118_upper : chungBeta 8 (59/500) < (5907 : ℝ)/15625 :=
  chungBeta_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_pos_118_upper

/-! ### the source condition, decided -/

/-- The adjusted gain of the Chung-8 curve at `δ = 0.0378`. -/
noncomputable def gainD8 (t : ℝ) : ℝ := chungBeta 8 t - 189/5000 - t

/-- `g_π = gain_δ(0.8)`. -/
noncomputable def gpi8 : ℝ := gainD8 (4/5)

/-- **`σ = 0.1184` satisfies the source condition `gain_δ(σ) ≥ 2 g_π`.** -/
theorem condB_holds_at_1184 : 2 * gpi8 ≤ gainD8 (74/625) := by
  simp only [gainD8, gpi8]
  linarith [beta_08_upper, beta_1184_lower]

/-- **`σ = 0.118` violates the source condition `gain_δ(σ) ≥ 2 g_π`.**  This is why `σ_min` must be rounded up:
the paper's earlier value `0.118` lies just below `σ_min = 0.1183474…`. -/
theorem condB_fails_at_118 : gainD8 (59/500) < 2 * gpi8 := by
  simp only [gainD8, gpi8]
  linarith [beta_08_lower, beta_118_upper]

/-- `g_π ∈ (0.1113, 0.1114)`: the bracket asserted by `FilecoinLatencyParameters`,
here derived from the construction. -/
theorem gpi8_bounds : (1113 : ℝ)/10000 < gpi8 ∧ gpi8 < (557 : ℝ)/5000 := by
  constructor
  · simp only [gpi8, gainD8]; linarith [beta_08_lower]
  · simp only [gpi8, gainD8]; linarith [beta_08_upper]

/-- **The rounding direction of `σ_min`, decided.**  the source condition separates the two
four-digit candidates: the paper's original `σ = 0.118` is inadmissible, and `0.1184`
is admissible.  Both halves are theorems about the constructed curve `β₈`; no numerical
value is taken on trust. -/
theorem sigmaMin_rounds_up :
    gainD8 (59/500) < 2 * gpi8 ∧ 2 * gpi8 ≤ gainD8 (74/625) :=
  ⟨condB_fails_at_118, condB_holds_at_1184⟩

/-! ### The left root of `gain_δ`

`gain_δ(0) = -δ < 0` but `chungBeta8` is only *defined* to be `0` at `0`, so the sign of
`gain_δ` just to the right of `0` has to be certified separately.  One point suffices:
at `x = 1/256` the threshold is below `1/32`, hence
`gain_δ(1/256) < 1/32 - δ - 1/256 = -0.0104 < 0`.  Together with `gain_δ(0.1184) > 0`
(`condB_holds_at_1184`) and continuity this brackets the left zero `α_δ^min`. -/

theorem sec_pos_1_256 : 0 < sec 8 (1/256) (1/32) := by
  have e2 := log_255_256
  have e4 := log_31_32
  have e6 := log_7_8
  have h256 : ((1 : ℝ) - 1/256) = 255/256 := by norm_num
  have h32 : ((1 : ℝ) - 1/32) = 31/32 := by norm_num
  have h7 : ((1 : ℝ)/32 - 1/256) = 7/256 := by norm_num
  simp only [sec, binEntropy_eq_neg, h256, h32, h7, log_1_256, log_1_32, log_7_256]
  linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, e2.1, e2.2, e4.1, e4.2,
    e6.1, e6.2]

theorem beta_1_256_upper : chungBeta 8 (1/256) < (1 : ℝ)/32 :=
  chungBeta_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_pos_1_256

/-- **`gain_δ` is negative at `1/256`.**  This is the missing sign that turns the left
zero `α_δ^min` from an assumption into a consequence of concavity. -/
theorem gainD8_neg_at_1_256 : gainD8 (1/256) < 0 := by
  simp only [gainD8]
  linarith [beta_1_256_upper]

/-! ### The mid-point certificate `2 g_π ≤ gain_δ(3/5)`

This is the single extra Chung-8 evaluation needed by the two-piece growth potential
`ProofOfSpace.growthPot`.  Together with the source condition at `σ` and concavity of `gain_δ`
it certifies `gain_δ ≥ 2 g_π` on the whole segment `[σ, 3/5]`, which is what lets the
growth window drop from `a = 6.13` levels to `Φ_{3/5}(π) + 1 = 4.97`. -/

theorem sec_neg_06_lower : sec 8 (3/5) (173/200) < 0 := by
  have e1 := log_3_5; have e2 := log_2_5
  have e3 := log_173_200; have e4 := log_27_200; have e5 := log_53_200
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem beta_06_lower : (173 : ℝ)/200 < chungBeta 8 (3/5) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_06_lower

/-- The mid-point certificate: the doubled tracking gain survives all the way to
`σ̃ = 3/5`. -/
theorem two_gpi_le_gainD8_06 : 2 * gpi8 ≤ gainD8 (3/5) := by
  have h1 := beta_06_lower
  have h2 := beta_08_upper
  simp only [gainD8, gpi8]
  linarith

end ChungCurve
end ProofOfSpace

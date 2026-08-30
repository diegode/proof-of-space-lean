/-
# Numerical certificates for the Chung curve

The Filecoin instantiation of `cor:filecoin` fixes `δ = 0.0378` and needs
the source condition `gain_δ(σ) ≥ 2 g_π`,

  `gain_δ(σ) ≥ 2 g_π`,   where `gain_δ(t) = β₈(t) - δ - t` and `g_π = gain_δ(0.8)`.

Here that condition is proved for `σ = 0.1184` and the curve `β₈` constructed in
`ChungCurve.lean`.

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

/-! ### the source condition, decided -/

/-- The adjusted gain of the Chung-8 curve at `δ = 0.0378`. -/
noncomputable def gainD8 (t : ℝ) : ℝ := chungBeta 8 t - 189/5000 - t

/-- `g_π = gain_δ(0.8)`. -/
noncomputable def gpi8 : ℝ := gainD8 (4/5)

/-- **`σ = 0.1184` satisfies the source condition `gain_δ(σ) ≥ 2 g_π`.** -/
theorem condB_holds_at_1184 : 2 * gpi8 ≤ gainD8 (74/625) := by
  simp only [gainD8, gpi8]
  linarith [beta_08_upper, beta_1184_lower]

/-- `g_π ∈ (0.1113, 0.1114)`: the bracket asserted by `FilecoinLatencyParameters`,
here derived from the construction. -/
theorem gpi8_bounds : (1113 : ℝ)/10000 < gpi8 ∧ gpi8 < (557 : ℝ)/5000 := by
  constructor
  · simp only [gpi8, gainD8]; linarith [beta_08_lower]
  · simp only [gpi8, gainD8]; linarith [beta_08_upper]

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


/-! ### Brackets for the reference-chain steps

The potential ledger of `PotentialLedger.lean` needs a reference chain: a finite
increasing sequence each of whose steps one free level of the footprint recurrence can
achieve.  For the Chung-8 Filecoin parameters that chain is the `β_δ` orbit of the
tracking floor, rationalized downwards, and certifying it means four more `β₈` lower
brackets.  Each needs the five logarithms `log x`, `log (1-x)`, `log y`, `log (1-y)` and
`log (y-x)`, produced by the same Mercator-plus-`log 2` recipe as above. -/

/-! #### Chain point `x_1 = 0.1622` -/

theorem log_811_5000 :
    (-1.818925138021 : ℝ) < log ((811 : ℝ)/5000) ∧
      log ((811 : ℝ)/5000) < (-1.818925136520 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-186 : ℝ)/625)) (by norm_num) 26
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (811 : ℝ)/5000 = ((811 : ℝ)/625) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_4189_5000 :
    (-0.176975870470 : ℝ) < log ((4189 : ℝ)/5000) ∧
      log ((4189 : ℝ)/5000) < (-0.176975870469 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((811 : ℝ)/5000)) (by norm_num) 17
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_4663_10000 :
    (-0.762926075408 : ℝ) < log ((4663 : ℝ)/10000) ∧
      log ((4663 : ℝ)/10000) < (-0.762926074907 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((337 : ℝ)/5000)) (by norm_num) 11
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (4663 : ℝ)/10000 = ((4663 : ℝ)/5000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_5337_10000 :
    (-0.627921395883 : ℝ) < log ((5337 : ℝ)/10000) ∧
      log ((5337 : ℝ)/10000) < (-0.627921395382 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-337 : ℝ)/5000)) (by norm_num) 11
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (5337 : ℝ)/10000 = ((5337 : ℝ)/5000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_3041_10000 :
    (-1.190398684779 : ℝ) < log ((3041 : ℝ)/10000) ∧
      log ((3041 : ℝ)/10000) < (-1.190398683778 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-541 : ℝ)/2500)) (by norm_num) 21
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (3041 : ℝ)/10000 = ((3041 : ℝ)/2500) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! #### Chain point `x_2 = 0.4285` -/

theorem log_857_2000 :
    (-0.847464541185 : ℝ) < log ((857 : ℝ)/2000) ∧
      log ((857 : ℝ)/2000) < (-0.847464540684 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((143 : ℝ)/1000)) (by norm_num) 16
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (857 : ℝ)/2000 = ((857 : ℝ)/1000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_1143_2000 :
    (-0.559490795988 : ℝ) < log ((1143 : ℝ)/2000) ∧
      log ((1143 : ℝ)/2000) < (-0.559490795487 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-143 : ℝ)/1000)) (by norm_num) 16
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (1143 : ℝ)/2000 = ((1143 : ℝ)/1000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_1929_2500 :
    (-0.259288997951 : ℝ) < log ((1929 : ℝ)/2500) ∧
      log ((1929 : ℝ)/2500) < (-0.259288997950 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((571 : ℝ)/2500)) (by norm_num) 22
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_571_2500 :
    (-1.476656801681 : ℝ) < log ((571 : ℝ)/2500) ∧
      log ((571 : ℝ)/2500) < (-1.476656800680 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((54 : ℝ)/625)) (by norm_num) 13
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (571 : ℝ)/2500 = ((571 : ℝ)/625) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_3431_10000 :
    (-1.069733329358 : ℝ) < log ((3431 : ℝ)/10000) ∧
      log ((3431 : ℝ)/10000) < (-1.069733328857 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1569 : ℝ)/5000)) (by norm_num) 28
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (3431 : ℝ)/10000 = ((3431 : ℝ)/5000) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! #### Chain point `x_3 = 0.7338` -/

theorem log_3669_5000 :
    (-0.309518767061 : ℝ) < log ((3669 : ℝ)/5000) ∧
      log ((3669 : ℝ)/5000) < (-0.309518767060 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1331 : ℝ)/5000)) (by norm_num) 24
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_1331_5000 :
    (-1.323507373502 : ℝ) < log ((1331 : ℝ)/5000) ∧
      log ((1331 : ℝ)/5000) < (-1.323507372501 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-81 : ℝ)/1250)) (by norm_num) 11
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (1331 : ℝ)/5000 = ((1331 : ℝ)/1250) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_579_625 :
    (-0.076449172164 : ℝ) < log ((579 : ℝ)/625) ∧
      log ((579 : ℝ)/625) < (-0.076449172163 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((46 : ℝ)/625)) (by norm_num) 12
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_46_625 :
    (-2.609110254208 : ℝ) < log ((46 : ℝ)/625) ∧
      log ((46 : ℝ)/625) < (-2.609110252207 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-111 : ℝ)/625)) (by norm_num) 18
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (46 : ℝ)/625 = ((736 : ℝ)/625) / 2^4 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^4) = 4 * Real.log 2 := by
    rw [show ((2:ℝ)^4) = (2:ℝ)^(4:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_963_5000 :
    (-1.647139780099 : ℝ) < log ((963 : ℝ)/5000) ∧
      log ((963 : ℝ)/5000) < (-1.647139779098 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((287 : ℝ)/1250)) (by norm_num) 22
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (963 : ℝ)/5000 = ((963 : ℝ)/1250) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! #### Chain point `x_4 = 0.8886` -/

theorem log_4443_5000 :
    (-0.118108088481 : ℝ) < log ((4443 : ℝ)/5000) ∧
      log ((4443 : ℝ)/5000) < (-0.118108088480 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((557 : ℝ)/5000)) (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_557_5000 :
    (-2.194627952210 : ℝ) < log ((557 : ℝ)/5000) ∧
      log ((557 : ℝ)/5000) < (-2.194627950709 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((68 : ℝ)/625)) (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (557 : ℝ)/5000 = ((557 : ℝ)/625) / 2^3 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^3) = 3 * Real.log 2 := by
    rw [show ((2:ℝ)^3) = (2:ℝ)^(3:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_9711_10000 :
    (-0.029325829382 : ℝ) < log ((9711 : ℝ)/10000) ∧
      log ((9711 : ℝ)/10000) < (-0.029325829381 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((289 : ℝ)/10000)) (by norm_num) 9
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_289_10000 :
    (-3.543913685065 : ℝ) < log ((289 : ℝ)/10000) ∧
      log ((289 : ℝ)/10000) < (-3.543913682564 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((47 : ℝ)/625)) (by norm_num) 12
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (289 : ℝ)/10000 = ((578 : ℝ)/625) / 2^5 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^5) = 5 * Real.log 2 := by
    rw [show ((2:ℝ)^5) = (2:ℝ)^(5:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_33_400 :
    (-2.494956986602 : ℝ) < log ((33 : ℝ)/400) ∧
      log ((33 : ℝ)/400) < (-2.494956984601 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-8 : ℝ)/25)) (by norm_num) 28
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (33 : ℝ)/400 = ((33 : ℝ)/25) / 2^4 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^4) = 4 * Real.log 2 := by
    rw [show ((2:ℝ)^4) = (2:ℝ)^(4:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]


/-! ### The four chain-step certificates of the potential ledger

`Potential.lean`'s reference chain for the Chung-8 Filecoin parameters is the `β_δ`
orbit of the tracking floor `π̂`, rationalized downwards:

  `x₀ = π̄`, `x₁ = 0.1622`, `x₂ = 0.4285`, `x₃ = 0.7338`, `x₄ = 0.8886`,

together with the chord extension point `x_top = 0.9333` used by the `t1` certificate.
The first step `x₁ = β_δ(π̄)` is exact — the mirror law gives `β(π̄) = 1 - π`, so
`β_δ(π̄) = 1 - π - δ = 811/5000` on the nose — and needs no numerics.  The remaining
four steps `x_{k+1} + δ ≤ β₈(x_k)` are the brackets below, each with `3·10⁻⁴` or more
of room. -/

theorem sec_neg_1622_lower : sec 8 (811/5000) (4663/10000) < 0 := by
  have e1 := log_811_5000; have e2 := log_4189_5000
  have e3 := log_4663_10000; have e4 := log_5337_10000; have e5 := log_3041_10000
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_neg_4285_lower : sec 8 (857/2000) (1929/2500) < 0 := by
  have e1 := log_857_2000; have e2 := log_1143_2000
  have e3 := log_1929_2500; have e4 := log_571_2500; have e5 := log_3431_10000
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_neg_7338_lower : sec 8 (3669/5000) (579/625) < 0 := by
  have e1 := log_3669_5000; have e2 := log_1331_5000
  have e3 := log_579_625; have e4 := log_46_625; have e5 := log_963_5000
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem sec_neg_8886_lower : sec 8 (4443/5000) (9711/10000) < 0 := by
  have e1 := log_4443_5000; have e2 := log_557_5000
  have e3 := log_9711_10000; have e4 := log_289_10000; have e5 := log_33_400
  simp only [sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-- `β₈(x₁) > x₂ + δ`: the second chain step. -/
theorem beta_1622_lower : (4663 : ℝ)/10000 < chungBeta 8 (811/5000) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_1622_lower

/-- `β₈(x₂) > x₃ + δ`: the third chain step. -/
theorem beta_4285_lower : (1929 : ℝ)/2500 < chungBeta 8 (857/2000) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_4285_lower

/-- `β₈(x₃) > x₄ + δ`: the fourth chain step. -/
theorem beta_7338_lower : (579 : ℝ)/625 < chungBeta 8 (3669/5000) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_7338_lower

/-- `β₈(x₄) > x_top + δ`: the chord extension point of the `t1` certificate. -/
theorem beta_8886_lower : (9711 : ℝ)/10000 < chungBeta 8 (4443/5000) :=
  lt_chungBeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sec_neg_8886_lower

end ChungCurve
end ProofOfSpace

/-
# Numerical certificates for the finite-size Chung profile

The rational profile of `ChungFilecoinCurve.lean` is certified by showing that
its interior vertices and a point of its opening ray lie strictly inside the
finite-size Chung region `E₈(x,y) < -2⁻²²`.

Each such sign is settled by bracketing the five logarithms it involves.  Each
`log (a/b)` is rescaled by a power of two into the fast-convergence range and then
bounded by the Mercator series with Mathlib's explicit tail estimate
`Real.abs_log_sub_add_sum_range_le`, together with the ten-digit bounds on `log 2`.
`ChungRegion.lean` turns these point certificates into a statement about the whole
profile.
-/
import ProofOfSpace.ChungFilecoinCurve
import ProofOfSpace.ChungChord
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

/-! ### Entropy certificates for polygon vertices -/

theorem shiftedSec_neg_08_vertex :
    shiftedSec 8 filecoinEpsilon (4 / 5) (94911 / 100000) < 0 := by
  have e1 := log_4_5; have e2 := log_1_5
  have e3 := log_94911_100000; have e4 := log_5089_100000; have e5 := log_14911_100000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem shiftedSec_neg_1184_vertex :
    shiftedSec 8 filecoinEpsilon (74 / 625) (3031 / 8000) < 0 := by
  have e1 := log_74_625; have e2 := log_551_625
  have e3 := log_3031_8000; have e4 := log_4969_8000; have e5 := log_10419_40000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-! ### Logarithm brackets for the remaining polygon vertices -/

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

/-! #### Polygon vertex `x_2 = 0.4285` -/

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

/-! #### Polygon vertex `x_3 = 0.7338` -/

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

/-! ### Entropy certificates at the remaining vertices -/

theorem shiftedSec_neg_1622_vertex :
    shiftedSec 8 filecoinEpsilon (811 / 5000) (4663 / 10000) < 0 := by
  have e1 := log_811_5000; have e2 := log_4189_5000
  have e3 := log_4663_10000; have e4 := log_5337_10000; have e5 := log_3041_10000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem shiftedSec_neg_4285_vertex :
    shiftedSec 8 filecoinEpsilon (857 / 2000) (1929 / 2500) < 0 := by
  have e1 := log_857_2000; have e2 := log_1143_2000
  have e3 := log_1929_2500; have e4 := log_571_2500; have e5 := log_3431_10000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem shiftedSec_neg_7338_vertex :
    shiftedSec 8 filecoinEpsilon (3669 / 5000) (579 / 625) < 0 := by
  have e1 := log_3669_5000; have e2 := log_1331_5000
  have e3 := log_579_625; have e4 := log_46_625; have e5 := log_963_5000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-! #### The anti-diagonal fixed vertex `x = 0.3201`

The fixed point of the reversal has `1 - y = x`, so only three distinct logarithms
occur. -/

theorem log_3201_10000 :
    (-1.139121842006 : ℝ) < log ((3201 : ℝ)/10000) ∧
      log ((3201 : ℝ)/10000) < (-1.139121822006 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((-701 : ℝ)/2500)) (by norm_num) 22
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (3201 : ℝ)/10000 = ((3201 : ℝ)/2500) / 2^2 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by
    rw [show ((2:ℝ)^2) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

theorem log_6799_10000 :
    (-0.385809560450 : ℝ) < log ((6799 : ℝ)/10000) ∧
      log ((6799 : ℝ)/10000) < (-0.385809540450 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((3201 : ℝ)/10000)) (by norm_num) 24
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_1799_5000 :
    (-1.022206967466 : ℝ) < log ((1799 : ℝ)/5000) ∧
      log ((1799 : ℝ)/5000) < (-1.022206947466 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((701 : ℝ)/2500)) (by norm_num) 22
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  have hsplit : (1799 : ℝ)/5000 = ((1799 : ℝ)/2500) / 2^1 := by norm_num
  have hlog2 : Real.log ((2:ℝ)^1) = 1 * Real.log 2 := by
    rw [show ((2:ℝ)^1) = (2:ℝ)^(1:ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num), hlog2]
  constructor <;> linarith [Real.log_two_lt_d9, Real.log_two_gt_d9, h.1, h.2]

/-! ### The degenerate-corner certificate

The first polygon segment is the ray `y = (20000 / 5089) x`, which runs into the corner
`(0,0)` where the finite-size region is empty.  `shiftedSec_neg_of_scaling` turns a
point of that ray into one scalar inequality, and at the dyadic abscissa `2⁻²⁵` the
inequality has a factor of four to spare.  This is the certificate that starts the
first and last segments. -/

theorem shiftedSec_neg_ray_2_25 :
    shiftedSec 8 filecoinEpsilon (1 / 2^25) (20000 / 5089 * (1 / 2^25)) < 0 := by
  have hx : log ((1:ℝ)/2^25) = -(25 * log 2) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hc : log ((20000:ℝ)/5089) = log ((1:ℝ)/5) - log ((5089:ℝ)/100000) := by
    rw [show ((20000:ℝ)/5089) = ((1:ℝ)/5) / ((5089:ℝ)/100000) by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have hc1 : log ((14911:ℝ)/5089) = log ((14911:ℝ)/100000) - log ((5089:ℝ)/100000) := by
    rw [show ((14911:ℝ)/5089) = ((14911:ℝ)/100000) / ((5089:ℝ)/100000) by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  refine shiftedSec_neg_of_scaling (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  have e1 := log_1_5
  have e2 := log_5089_100000
  have e3 := log_14911_100000
  simp only [filecoinEpsilon]
  norm_num [hx, hc, hc1]
  nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2,
    Real.log_two_gt_d9, Real.log_two_lt_d9]

/-! ### Finite-size (`E = -2⁻²²`) vertex certificates -/

theorem shiftedSec_neg_center_vertex :
    shiftedSec 8 filecoinEpsilon (3201 / 10000) (6799 / 10000) < 0 := by
  have e1 := log_3201_10000; have e2 := log_6799_10000
  have e3 := log_1799_5000
  simp only [shiftedSec, filecoinEpsilon, sec, binEntropy_eq_neg]
  norm_num
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

theorem shiftedSec_neg_05089_vertex :
    shiftedSec 8 filecoinEpsilon (5089 / 100000) (1 / 5) < 0 := by
  calc
    shiftedSec 8 filecoinEpsilon (5089 / 100000) (1 / 5) =
        shiftedSec 8 filecoinEpsilon (4 / 5) (94911 / 100000) := by
      convert shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
        (x := (4 / 5 : ℝ)) (y := (94911 / 100000 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) using 1
      norm_num
    _ < 0 := shiftedSec_neg_08_vertex

theorem shiftedSec_neg_0736_vertex :
    shiftedSec 8 filecoinEpsilon (46 / 625) (1331 / 5000) < 0 := by
  calc
    shiftedSec 8 filecoinEpsilon (46 / 625) (1331 / 5000) =
        shiftedSec 8 filecoinEpsilon (3669 / 5000) (579 / 625) := by
      convert shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
        (x := (3669 / 5000 : ℝ)) (y := (579 / 625 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) using 1
      norm_num
    _ < 0 := shiftedSec_neg_7338_vertex

theorem shiftedSec_neg_2284_vertex :
    shiftedSec 8 filecoinEpsilon (571 / 2500) (1143 / 2000) < 0 := by
  calc
    shiftedSec 8 filecoinEpsilon (571 / 2500) (1143 / 2000) =
        shiftedSec 8 filecoinEpsilon (857 / 2000) (1929 / 2500) := by
      convert shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
        (x := (857 / 2000 : ℝ)) (y := (1929 / 2500 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) using 1
      norm_num
    _ < 0 := shiftedSec_neg_4285_vertex

theorem shiftedSec_neg_5337_vertex :
    shiftedSec 8 filecoinEpsilon (5337 / 10000) (4189 / 5000) < 0 := by
  calc
    shiftedSec 8 filecoinEpsilon (5337 / 10000) (4189 / 5000) =
        shiftedSec 8 filecoinEpsilon (811 / 5000) (4663 / 10000) := by
      convert shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
        (x := (811 / 5000 : ℝ)) (y := (4663 / 10000 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) using 1
      norm_num
    _ < 0 := shiftedSec_neg_1622_vertex

theorem shiftedSec_neg_621125_vertex :
    shiftedSec 8 filecoinEpsilon (4969 / 8000) (551 / 625) < 0 := by
  calc
    shiftedSec 8 filecoinEpsilon (4969 / 8000) (551 / 625) =
        shiftedSec 8 filecoinEpsilon (74 / 625) (3031 / 8000) := by
      convert shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
        (x := (74 / 625 : ℝ)) (y := (3031 / 8000 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) using 1
      norm_num
    _ < 0 := shiftedSec_neg_1184_vertex

end ChungCurve
end ProofOfSpace

import ProofOfSpace.DRSample.LogEstimates
import ProofOfSpace.DRSample.ShiftedRobustness

namespace ProofOfSpace.DRSample

noncomputable def paperScale (n : ℕ) : ℝ :=
  Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
noncomputable def paperBlockUnit (n : ℕ) : ℕ := Nat.ceil (116 * paperScale n)
noncomputable def paperBudget (n : ℕ) : ℕ := Nat.floor ((n : ℝ) / (18000 * paperScale n))
noncomputable def paperWidth (n : ℕ) : ℕ := Nat.floor (3600 * paperScale n)
noncomputable def paperFailure (n : ℕ) : ℝ := Real.exp (-(n : ℝ) / (11000 * paperScale n))

theorem logb_120_upper : Real.logb 2 120 ≤ (6907 / 1000 : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 15)
  norm_num at hsmall
  have hsum : Real.log (120 : ℝ) + Real.log (16 / 15 : ℝ) = 7 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    have h := Real.log_pow (2 : ℝ) 7
    norm_num at h
    exact h
  rw [Real.logb]
  apply (div_le_iff₀ hl2).mpr
  linarith [Real.log_two_lt_d9]

theorem paper_quadratic_small {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    (10 ^ 12 : ℝ) * (Real.logb 2 n) ^ 2 ≤ n := by
  have hx := (log_parameters hn).1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := exp_linear_lower (a := Real.log 2 / 2) (by norm_num : (0 : ℝ) < 120) hx
    (by linarith [Real.log_two_gt_d9])
  have hbase : Real.exp (Real.log 2 / 2 * 120) = (2 : ℝ) ^ 60 := by
    rw [show Real.log 2 / 2 * 120 = (60 : ℝ) * Real.log 2 by ring]
    exact exp_nat_log_two 60
  rw [hbase] at h
  have hsquare := mul_self_le_mul_self (by positivity) h
  have hex : Real.exp (Real.log 2 / 2 * Real.logb 2 n) *
      Real.exp (Real.log 2 / 2 * Real.logb 2 n) = (n : ℝ) := by
    rw [← Real.exp_add]
    have hlog : Real.log 2 * Real.logb 2 n = Real.log n := by
      rw [Real.logb, mul_div_cancel₀ _ hl2.ne']
    rw [show Real.log 2 / 2 * Real.logb 2 n + Real.log 2 / 2 * Real.logb 2 n =
      Real.log n by linarith]
    exact Real.exp_log (by exact_mod_cast (show 0 < n by omega))
  rw [hex] at hsquare
  norm_num at hsquare
  nlinarith [sq_nonneg (Real.logb 2 n)]

theorem paper_depth_scalar {x c C E : ℝ} (hx : 120 ≤ x) (hc : c ≤ 1 / 5)
    (hC : 0 ≤ C) (hE : 0 < E)
    (hbase : Real.exp (c * Real.logb 2 120) ≤ E)
    (hnum : C * (6907 / 1000 : ℝ) * E ≤ (999 * 9 / 40000 : ℝ) * 120) :
    C * Real.logb 2 x ≤ (999 * 9 / 40000 : ℝ) * x * Real.exp (-c * Real.logb 2 x) := by
  let y := Real.logb 2 x
  let y₀ := Real.logb 2 120
  let a := Real.log 2 - c
  have hx0 : 0 < x := by linarith
  have hy₀ := logb_120_bounds.1
  have hy₀0 : 0 < y₀ := by dsimp [y₀]; linarith
  have hy : y₀ ≤ y := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
  have hy0 : 0 ≤ y := by linarith
  have hlin := exp_linear_lower (a := a) hy₀0 hy
    (by dsimp [a, y₀] at *; nlinarith [Real.log_two_gt_d9])
  have hcancel : Real.exp (a * y₀) * Real.exp (c * y₀) = 120 := by
    rw [← Real.exp_add]
    have hl : Real.log 2 * y₀ = Real.log 120 := by dsimp [y₀, Real.logb]; field_simp
    rw [show a * y₀ + c * y₀ = Real.log 120 by dsimp [a]; nlinarith]
    exact Real.exp_log (by norm_num)
  have hbaseLower : 120 / E ≤ Real.exp (a * y₀) := by
    apply (div_le_iff₀ hE).mpr
    have h := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (a * y₀)).le
    rw [hcancel] at h
    linarith
  have hratio : Real.exp (a * y) = x * Real.exp (-c * y) := by
    have hl : Real.log 2 * y = Real.log x := by dsimp [y, Real.logb]; field_simp
    rw [show a * y = Real.log x + -c * y by dsimp [a]; nlinarith,
      Real.exp_add, Real.exp_log hx0]
  rw [hratio] at hlin
  have hyscale : y / (6907 / 1000 : ℝ) ≤ y / y₀ :=
    div_le_div_of_nonneg_left hy0 hy₀0 logb_120_upper
  have h := (mul_le_mul hyscale hbaseLower (by positivity)
    (div_nonneg hy0 hy₀0.le)).trans hlin
  have hnum' : C ≤ (999 * 9 / 40000 : ℝ) * (120 / E) / (6907 / 1000) := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [← mul_div_assoc (999 * 9 / 40000 : ℝ) 120 E]
    apply (le_div_iff₀ hE).mpr
    exact hnum
  have hc' := mul_le_mul_of_nonneg_right hnum' hy0
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 999 * 9 / 40000)
  change C * y ≤ (999 * 9 / 40000 : ℝ) * x * Real.exp (-c * y)
  nlinarith

theorem paper_depth_scalar_dr {x : ℝ} (hx : 120 ≤ x) :
    (37 / 25 : ℝ) * Real.logb 2 x ≤ (999 * 9 / 40000 : ℝ) * x *
      Real.exp (-(39083 / 278400 : ℝ) * Real.logb 2 x) := by
  apply paper_depth_scalar hx (by norm_num) (by norm_num) (E := 1319 / 500) (by norm_num)
  · have hbound := Real.exp_bound' (n := 10)
      (by norm_num : (0 : ℝ) ≤ 97 / 100) (by norm_num : (97 / 100 : ℝ) ≤ 1) (by norm_num)
    have hmono : Real.exp ((39083 / 278400 : ℝ) * Real.logb 2 120) ≤ Real.exp (97 / 100 : ℝ) :=
      Real.exp_le_exp.mpr (by nlinarith [logb_120_upper])
    norm_num [Finset.sum_range_succ] at hbound
    linarith
  · norm_num

theorem paper_depth_scalar_harmonic {x : ℝ} (hx : 120 ≤ x) :
    (2 : ℝ) * Real.logb 2 x ≤ (999 * 9 / 40000 : ℝ) * x *
      Real.exp (-(323 / 2320 * Real.log 2) * Real.logb 2 x) := by
  apply paper_depth_scalar hx (by linarith [Real.log_two_lt_d9]) (by norm_num)
    (E := 1949 / 1000) (by norm_num)
  · have hbound := Real.exp_bound' (n := 10)
      (by norm_num : (0 : ℝ) ≤ 667 / 1000) (by norm_num : (667 / 1000 : ℝ) ≤ 1) (by norm_num)
    have hprod := mul_le_mul (le_of_lt Real.log_two_lt_d9) logb_120_upper
      (by linarith [logb_120_bounds.1]) (by norm_num)
    have hmono : Real.exp ((323 / 2320 * Real.log 2) * Real.logb 2 120) ≤
        Real.exp (667 / 1000 : ℝ) := Real.exp_le_exp.mpr (by nlinarith)
    norm_num [Finset.sum_range_succ] at hbound
    linarith
  · norm_num

theorem paper_scale_bounds {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    16 ≤ paperScale n ∧ paperScale n ≤ Real.logb 2 n := by
  obtain ⟨hx, hy, hxy, _⟩ := log_parameters hn
  have hy0 : 0 < Real.logb 2 (Real.logb 2 n) := by linarith
  constructor
  · exact (le_div_iff₀ hy0).mpr hxy
  · apply (div_le_iff₀ hy0).mpr
    nlinarith

theorem paper_block_bounds {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    0 < paperBlockUnit n ∧
    2320 * paperScale n ≤ (20 * paperBlockUnit n : ℕ) ∧
    ((20 * paperBlockUnit n : ℕ) : ℝ) ≤ 2322 * paperScale n ∧
    2 * ((20 * paperBlockUnit n : ℕ) : ℝ) ≤ (n : ℝ) / 1000 := by
  have hs := paper_scale_bounds hn
  have hL : 0 < paperScale n := by linarith [hs.1]
  have hlo : 116 * paperScale n ≤ (paperBlockUnit n : ℝ) := Nat.le_ceil _
  have hhi : (paperBlockUnit n : ℝ) < 116 * paperScale n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hpos : 0 < paperBlockUnit n := by exact_mod_cast (show (0 : ℝ) < paperBlockUnit n by nlinarith)
  have hB : ((20 * paperBlockUnit n : ℕ) : ℝ) ≤ 2322 * paperScale n := by
    push_cast
    linarith [hs.1]
  refine ⟨hpos, by push_cast; linarith, hB, ?_⟩
  have hsmall := paper_quadratic_small hn
  have hx := (log_parameters hn).1
  nlinarith [sq_nonneg (Real.logb 2 n - 1)]

theorem paper_integer_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    2 * (20 * paperBlockUnit n) < n ∧ 0 < paperWidth n ∧
    (paperBudget n : ℝ) * (paperWidth n + 20 * paperBlockUnit n) ≤
      ((n : ℝ) - 2 * (20 * paperBlockUnit n)) / 3 := by
  have hB := paper_block_bounds hn
  have hs := paper_scale_bounds hn
  have hL : 0 < paperScale n := by linarith [hs.1]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (paperBudget n : ℝ) ≤ (n : ℝ) / (18000 * paperScale n) := Nat.floor_le (by positivity)
  have heb := (le_div_iff₀ (by positivity : 0 < 18000 * paperScale n)).mp he
  have hb : (paperWidth n : ℝ) ≤ 3600 * paperScale n := Nat.floor_le (by positivity)
  have hbpos : 0 < paperWidth n := Nat.floor_pos.mpr (by change 1 ≤ 3600 * paperScale n; linarith [hs.1])
  have hprod := mul_le_mul_of_nonneg_left
    (show (paperWidth n : ℝ) + (20 * paperBlockUnit n : ℕ) ≤ 5922 * paperScale n by linarith [hB.2.2.1])
    (Nat.cast_nonneg (paperBudget n))
  refine ⟨?_, hbpos, ?_⟩
  · exact_mod_cast (show (2 : ℝ) * (20 * paperBlockUnit n : ℕ) < n by linarith [hB.2.2.2])
  · push_cast at hprod hB
    nlinarith

theorem paper_depth_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    (37 / 25 : ℝ) * (n : ℝ) / paperScale n ≤
      (9 / 40 : ℝ) * ((n : ℝ) - 2 * (20 * paperBlockUnit n)) *
        Real.exp (-323 / ((1 / (Real.logb 2 n + 1)) * (20 * paperBlockUnit n))) ∧
    (2 : ℝ) * (n : ℝ) / paperScale n ≤
      (9 / 40 : ℝ) * ((n : ℝ) - 2 * (20 * paperBlockUnit n)) *
        Real.exp (-323 / ((1 / Real.log n) * (20 * paperBlockUnit n))) := by
  let x := Real.logb 2 n
  let y := Real.logb 2 x
  let B : ℝ := 20 * paperBlockUnit n
  have hx : 120 ≤ x := (log_parameters hn).1
  have hy : 6 ≤ y := (log_parameters hn).2.1
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 0 < paperScale n := by have := (paper_scale_bounds hn).1; linarith
  have hb := paper_block_bounds hn
  have hB : 0 < B := by dsimp [B]; have := hb.1; positivity
  have hlo : 2320 * x ≤ B * y := by
    have h := hb.2.1
    push_cast at h
    change 2320 * (x / y) ≤ B at h
    have hh := mul_le_mul_of_nonneg_right h hy0.le
    field_simp at hh
    nlinarith
  have hcomplete : (999 / 1000 : ℝ) * n ≤ (n : ℝ) - 2 * B := by
    have h := hb.2.2.2
    push_cast at h
    change 2 * B ≤ (n : ℝ) / 1000 at h
    linarith
  have hlog : Real.log n = x * Real.log 2 := by
    dsimp [x, Real.logb]
    field_simp
  have hlog0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcoef_dr : 323 / ((1 / (x + 1)) * B) ≤ (39083 / 278400 : ℝ) * y := by
    have hxp : 0 < x + 1 := by linarith
    apply (div_le_iff₀ (by positivity : 0 < (1 / (x + 1)) * B)).mpr
    field_simp
    nlinarith
  have hcoef_harm : 323 / ((1 / Real.log n) * B) ≤ (323 / 2320 * Real.log 2) * y := by
    apply (div_le_iff₀ (by positivity : 0 < (1 / Real.log n) * B)).mpr
    field_simp
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_right hlo (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have hscalar (C c : ℝ) (hc : C * y ≤ (999 * 9 / 40000 : ℝ) * x * Real.exp (-c * y)) :
      C * (n : ℝ) / paperScale n ≤
        (9 / 40 : ℝ) * ((n : ℝ) - 2 * B) * Real.exp (-c * y) := by
    have h := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (n : ℝ) / x)
    have hleft : (n : ℝ) / x * (C * y) = C * (n : ℝ) / paperScale n := by
      dsimp [paperScale, x, y]
      field_simp
    have hright : (n : ℝ) / x * ((999 * 9 / 40000 : ℝ) * x * Real.exp (-c * y)) =
        (999 * 9 / 40000 : ℝ) * n * Real.exp (-c * y) := by field_simp
    rw [hleft, hright] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith
  constructor
  · apply (hscalar _ _ (paper_depth_scalar_dr hx)).trans
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hcoef_dr))
      (show 0 ≤ (9 / 40 : ℝ) * ((n : ℝ) - 2 * B) by nlinarith)
    simpa only [neg_mul, neg_div] using h
  · apply (hscalar _ _ (paper_depth_scalar_harmonic hx)).trans
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hcoef_harm))
      (show 0 ≤ (9 / 40 : ℝ) * ((n : ℝ) - 2 * B) by nlinarith)
    simpa only [neg_mul, neg_div] using h

theorem paper_failure_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    ((20 * paperBlockUnit n : ℕ) : ℝ) *
      Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / (20 * paperBlockUnit n) - 2)) ≤
      paperFailure n := by
  let B : ℝ := 20 * paperBlockUnit n
  let L := paperScale n
  let x := Real.logb 2 n
  let kappa : ℝ := 8 / 5 - Real.log 4
  have hb := paper_block_bounds hn
  have hs := paper_scale_bounds hn
  have hL : 0 < L := by dsimp [L]; linarith [hs.1]
  have hx : 120 ≤ x := (log_parameters hn).1
  have hB : 0 < B := by dsimp [B]; have := hb.1; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hBupper : B ≤ 2322 * L := by simpa [B, L] using hb.2.2.1
  have hBsmall : 2 * B ≤ (n : ℝ) / 1000 := by simpa [B] using hb.2.2.2
  have hlogn : Real.log n = x * Real.log 2 := by dsimp [x, Real.logb]; field_simp
  have hlognpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlognx : Real.log n ≤ x := by rw [hlogn]; nlinarith [Real.log_two_lt_d9]
  have hlogB : Real.log B ≤ (1 / 1000000 : ℝ) * ((n : ℝ) / L) := by
    have hBn : B ≤ n := by linarith
    apply (Real.log_le_log hB hBn).trans
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hL).mpr
    have hprod := mul_le_mul hlognx hs.2 hL.le (by linarith : (0 : ℝ) ≤ x)
    have hsmall := paper_quadratic_small hn
    change (10 ^ 12 : ℝ) * x ^ 2 ≤ n at hsmall
    change Real.log n * L ≤ x * x at hprod
    nlinarith [sq_nonneg x]
  have hquot : (999 / 2322000 : ℝ) * ((n : ℝ) / L) ≤ (n : ℝ) / B - 2 := by
    have hcomplete : (999 / 1000 : ℝ) * n ≤ (n : ℝ) - 2 * B := by linarith
    have hdiv := div_le_div_of_nonneg_right hcomplete hB.le
    have hden := div_le_div_of_nonneg_left (by positivity : 0 ≤ (999 / 1000 : ℝ) * n)
      hB hBupper
    have h := hden.trans hdiv
    calc
      _ = ((999 / 1000 : ℝ) * n) / (2322 * L) := by ring
      _ ≤ ((n : ℝ) - 2 * B) / B := h
      _ = _ := by field_simp [hB.ne']
  have hk : 0 < kappa := multiscale_kappa_pos
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hconstant : (1 / 11000 + 1 / 1000000 : ℝ) ≤ kappa * (999 / 2322000) := by
    dsimp [kappa]
    rw [hlog4]
    linarith [Real.log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_left hquot hk.le
  have hcoef := mul_le_mul_of_nonneg_right hconstant (by positivity : 0 ≤ (n : ℝ) / L)
  have hexp : Real.log B - kappa * ((n : ℝ) / B - 2) ≤ -(n : ℝ) / (11000 * L) := by
    have hdiv : -(n : ℝ) / (11000 * L) = -(1 / 11000 : ℝ) * ((n : ℝ) / L) := by ring
    rw [hdiv]
    nlinarith
  push_cast
  change B * Real.exp (-kappa * ((n : ℝ) / B - 2)) ≤ Real.exp (-(n : ℝ) / (11000 * L))
  calc
    _ = Real.exp (Real.log B + -kappa * ((n : ℝ) / B - 2)) := by
      rw [Real.exp_add, Real.exp_log hB]
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using hexp)

end ProofOfSpace.DRSample

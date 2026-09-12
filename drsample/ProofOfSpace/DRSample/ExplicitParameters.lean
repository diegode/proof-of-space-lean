import ProofOfSpace.DRSample.OptimizedRobustness

/-! # An explicit cutoff with the improved conjecture constants

The stronger finite theorem applies to the rounded conjecture parameters for
every `n ≥ 2^120`. The numerical comparisons use rational exponential bounds;
the resulting theorems concern the exact DRSample and Filecoin distributions.
-/
namespace ProofOfSpace.DRSample

/-- A tangent bound which also proves monotonicity of the exponential-to-linear ratio. -/
theorem exp_linear_lower {a t t₀ : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (ha : 1 ≤ a * t₀) :
    t / t₀ * Real.exp (a * t₀) ≤ Real.exp (a * t) := by
  have hlin : t / t₀ ≤ a * (t - t₀) + 1 := by
    apply (div_le_iff₀ ht₀).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ht)]
  calc
    _ ≤ Real.exp (a * (t - t₀)) * Real.exp (a * t₀) :=
      mul_le_mul_of_nonneg_right (hlin.trans (Real.add_one_le_exp _)) (by positivity)
    _ = Real.exp (a * t) := by rw [← Real.exp_add]; congr 1; ring

theorem exp_nat_log_two (k : ℕ) :
    Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Rational bounds at the logarithmic base case `log₂ n = 120`. -/
theorem logb_120_bounds :
    (6 : ℝ) ≤ Real.logb 2 120 ∧ Real.logb 2 120 ≤ 691 / 100 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (6 : ℝ) ≤ Real.logb 2 120 := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hsmall := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
  norm_num at hsmall
  have hsum : Real.log (120 : ℝ) + Real.log (16 / 15 : ℝ) = 7 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
    have h := Real.log_pow (2 : ℝ) 7
    norm_num at h
    exact h
  refine ⟨hlo, ?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ hl2).mpr
  linarith [Real.log_two_lt_d9]

theorem log_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    120 ≤ Real.logb 2 n ∧
    6 ≤ Real.logb 2 (Real.logb 2 n) ∧
    16 * Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n ∧
    3201000 * Real.logb 2 n ≤ (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : (120 : ℝ) ≤ Real.logb 2 n := by
    apply (Real.le_logb_iff_rpow_le (by norm_num) hn0).mpr
    norm_cast
  have hx0 : 0 < Real.logb 2 n := by linarith
  let y₀ := Real.logb 2 120
  have hy₀ : (6 : ℝ) ≤ y₀ := logb_120_bounds.1
  have hy₀0 : 0 < y₀ := by linarith
  have hy : y₀ ≤ Real.logb 2 (Real.logb 2 n) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
  have hex (x : ℝ) (hx : 0 < x) : Real.exp (Real.log 2 * Real.logb 2 x) = x := by
    rw [Real.logb, mul_div_cancel₀ _ hl2.ne', Real.exp_log hx]
  have hxy := exp_linear_lower (a := Real.log 2) hy₀0 hy
    (by nlinarith [Real.log_two_gt_d9])
  rw [hex _ hx0, hex 120 (by norm_num)] at hxy
  have hprod := mul_le_mul_of_nonneg_right hxy hy₀0.le
  have hcancel := div_mul_cancel₀ (Real.logb 2 (Real.logb 2 n)) hy₀0.ne'
  have hupper := mul_le_mul_of_nonneg_left logb_120_bounds.2 hx0.le
  have hxn := exp_linear_lower (a := Real.log 2) (by norm_num : (0 : ℝ) < 120) hx
    (by linarith [Real.log_two_gt_d9])
  have h120 := exp_nat_log_two 120
  norm_num at h120
  rw [hex _ hn0, mul_comm (Real.log 2) 120, h120] at hxn
  exact ⟨hx, hy₀.trans hy, by dsimp [y₀] at *; nlinarith, by linarith⟩

/-- The depth comparison increases from `log₂log₂ n = log₂ 120`.
A quadratic Taylor sum with a bounded cubic remainder gives the rational
base-case estimate `exp ((303/2000) log₂ 120) ≤ 57/20`. -/
theorem depth_scalar {x : ℝ} (hx : 120 ≤ x) :
    (101 / 100 : ℝ) * Real.logb 2 x ≤
      (999 / 6000 : ℝ) * x * Real.exp (-(303 / 2000 : ℝ) * Real.logb 2 x) := by
  let y := Real.logb 2 x
  let y₀ := Real.logb 2 120
  let a : ℝ := Real.log 2 - 303 / 2000
  have hx0 : 0 < x := by linarith
  have hy₀ : (6 : ℝ) ≤ y₀ := logb_120_bounds.1
  have hy₀0 : 0 < y₀ := by linarith
  have hy₀upper : y₀ ≤ 691 / 100 := logb_120_bounds.2
  have hy : y₀ ≤ y := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
  have hlin := exp_linear_lower (a := a) hy₀0 hy
    (by dsimp [a]; nlinarith [Real.log_two_gt_d9])
  have hbase : Real.exp ((303 / 2000 : ℝ) * y₀) ≤ 57 / 20 := by
    have hsmall := Real.exp_bound' (n := 3)
      (by norm_num : (0 : ℝ) ≤ 9373 / 200000)
      (by norm_num : (9373 / 200000 : ℝ) ≤ 1) (by norm_num)
    norm_num [Finset.sum_range_succ] at hsmall
    have hone : Real.exp 1 ≤ 87 / 32 := by linarith [Real.exp_one_lt_d9]
    calc
      _ ≤ Real.exp (1 + 9373 / 200000 : ℝ) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 1 * Real.exp (9373 / 200000 : ℝ) := Real.exp_add _ _
      _ ≤ 57 / 20 := by
        have hprod := mul_le_mul hone hsmall (by positivity) (by norm_num)
        norm_num at hprod ⊢
        linarith
  have hcancel : Real.exp (a * y₀) * Real.exp ((303 / 2000 : ℝ) * y₀) = 120 := by
    rw [← Real.exp_add]
    have hl : Real.log 2 * y₀ = Real.log 120 := by
      dsimp [y₀, Real.logb]
      field_simp
    rw [show a * y₀ + (303 / 2000 : ℝ) * y₀ = Real.log 120 by dsimp [a]; nlinarith]
    exact Real.exp_log (by norm_num)
  have hbaseLower : 800 / 19 ≤ Real.exp (a * y₀) := by
    have := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (a * y₀)).le
    rw [hcancel] at this
    linarith
  have hratio : Real.exp (a * y) = x * Real.exp (-(303 / 2000 : ℝ) * y) := by
    have hl : Real.log 2 * y = Real.log x := by
      dsimp [y, Real.logb]
      field_simp
    rw [show a * y = Real.log x + -(303 / 2000 : ℝ) * y by dsimp [a]; nlinarith,
      Real.exp_add, Real.exp_log hx0]
  rw [hratio] at hlin
  have hyscale : (100 / 691 : ℝ) * y ≤ y / y₀ := by
    apply (le_div_iff₀ hy₀0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hy₀upper (show 0 ≤ y by linarith)]
  have h := (mul_le_mul hyscale hbaseLower (by norm_num)
    (div_nonneg (by linarith) hy₀0.le)).trans hlin
  change (101 / 100 : ℝ) * y ≤
    (999 / 6000 : ℝ) * x * Real.exp (-(303 / 2000 : ℝ) * y)
  nlinarith


set_option maxHeartbeats 1000000 in
-- Clearing the rational rounding bounds creates several polynomial inequalities.
/-- All rounded parameters satisfy the improved finite theorem for `n ≥ 2^120`. -/
theorem finite_parameters {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    12 ≤ blockWidth n ∧ blockWidth n ≤ n ∧ intervalWidth n ≤ blockWidth n ∧
    0 < intervalWidth n ∧ 2 * deletionBudget n ≤ (n / blockWidth n) / 3 ∧
    (101 / 100 : ℝ) * targetDepth n ≤
      ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 6) *
        Real.exp (-(160 * blockWidth n * (Real.logb 2 n + 1) /
          (3 * (blockWidth n / 3 : ℕ) ^ 2))) ∧
    targetDepth n / 3300 ≤ (n / blockWidth n : ℕ) := by
  have hp := log_parameters hn
  let x := Real.logb 2 n
  let y := Real.logb 2 x
  let m := blockWidth n
  have hx120 : 120 ≤ x := hp.1
  have hy6 : 6 ≤ y := hp.2.1
  have hy16 : 16 * y ≤ x := hp.2.2.1
  have hsmall : 3201000 * x ≤ (n : ℝ) := hp.2.2.2
  have hy : 1 ≤ y := by linarith
  have hyx : y ≤ x := by linarith
  change y ≤ x at hyx
  have hy0 : 0 < y := by linarith
  have hx1 : 1 ≤ x := hy.trans hyx
  have hx0 : 0 < x := by linarith
  have hscale : (3200 : ℝ) ≤ 3200 * x / y := (le_div_iff₀ hy0).mpr (by nlinarith)
  have hlo : 3200 * x / y ≤ (m : ℝ) := Nat.le_ceil _
  have hhi : (m : ℝ) < 3200 * x / y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm12 : 12 ≤ m := by exact_mod_cast (show (12 : ℝ) ≤ m by linarith)
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmy : (m : ℝ) * y ≤ 3201 * x := by
    have hh := (lt_div_iff₀ hy0).mp (show (m : ℝ) - 1 < 3200 * x / y by linarith)
    nlinarith
  have hscaleupper : 3200 * x / y ≤ 3200 * x := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hfour : 16 * m ≤ n := by
    exact_mod_cast (show (16 : ℝ) * m ≤ n by linarith)
  have hmle : m ≤ n := by omega
  have hquot : 16 ≤ n / m := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
  have hquotR : (16 : ℝ) ≤ (n / m : ℕ) := by exact_mod_cast hquot
  have hdivision : n < m * (n / m + 1) := by
    have hmod := Nat.mod_lt n hm0
    have heq := Nat.mod_add_div n m
    nlinarith
  have hdivisionR : (n : ℝ) < (m : ℝ) * ((n / m : ℕ) + 1) := by exact_mod_cast hdivision
  have hm1000 : (1000 : ℝ) * m ≤ n := by linarith
  have hcomplete999 : (999 / 1000 : ℝ) * n ≤ m * (n / m : ℕ) := by nlinarith
  have hcomplete : (n : ℝ) ≤ (4 / 3 : ℝ) * m * (n / m : ℕ) := by nlinarith
  have hcomplete_sharp : (n : ℝ) ≤ (17 / 16 : ℝ) * m * (n / m : ℕ) := by nlinarith
  have hbudget : (deletionBudget n : ℝ) ≤ (n : ℝ) * y / (20000 * x) :=
    Nat.floor_le (by positivity)
  have hbudgetmul := (le_div_iff₀ (by positivity : 0 < 20000 * x)).mp hbudget
  have hny : (n : ℝ) * y ≤ 3300 * x * (n / m : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_right hcomplete999 hy0.le
    have h2 := mul_le_mul_of_nonneg_right hmy (Nat.cast_nonneg (n / m))
    nlinarith
  have he6 : 6 * deletionBudget n ≤ n / m := by
    have hR : (6 : ℝ) * deletionBudget n ≤ (n / m : ℕ) := by
      by_contra! hbad
      have hpos := mul_pos hx0 (sub_pos.mpr hbad)
      nlinarith
    exact_mod_cast hR
  have hcount : targetDepth n / 3300 ≤ (n / m : ℕ) := by
    change ((n : ℝ) * y / x) / 3300 ≤ (n / m : ℕ)
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < x * 3300)).mpr
    nlinarith
  have hb : intervalWidth n ≤ m := Nat.floor_le_ceil _
  have hbpos : 0 < intervalWidth n := by
    have hge : 1 ≤ intervalWidth n := by
      apply Nat.le_floor
      norm_num only [Nat.cast_one]
      change (1 : ℝ) ≤ 3200 * x / y
      linarith
    omega
  refine ⟨hm12, hmle, hb, hbpos, ?_, ?_, hcount⟩
  · change 2 * deletionBudget n ≤ (n / m) / 3
    omega
  -- Control the loss from integer port widths before comparing the depths.
  have hm32768 : 32768 ≤ m := by
    have hlo' := (div_le_iff₀ hy0).mp hlo
    exact_mod_cast (show (32768 : ℝ) ≤ m by nlinarith)
  have ht : 5000 * m ≤ 15001 * (m / 3) := by omega
  have htR : (5000 : ℝ) * m ≤ 15001 * (m / 3 : ℕ) := by exact_mod_cast ht
  have htsq : (25000000 : ℝ) * (m : ℝ) ^ 2 ≤
      225030001 * ((m / 3 : ℕ) : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 5000 * m) htR]
  have htpos : 0 < m / 3 := by omega
  have hcoef : 160 * m * (x + 1) / (3 * ((m / 3 : ℕ) : ℝ) ^ 2) ≤
      12120 * x / (25 * m) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < 25 * m)).mpr
    have hprod := mul_le_mul_of_nonneg_right htsq hx0.le
    have hprod2 := mul_le_mul_of_nonneg_left
      (show x + 1 ≤ 121 * x / 120 by linarith) (sq_nonneg (m : ℝ))
    nlinarith
  have hexponent : 160 * m * (x + 1) / (3 * ((m / 3 : ℕ) : ℝ) ^ 2) ≤
      (303 / 2000 : ℝ) * y := by
    apply hcoef.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 25 * m)).mpr
    have hlo' := (div_le_iff₀ hy0).mp hlo
    nlinarith
  have hexp : Real.exp (-(303 / 2000 : ℝ) * y) ≤
      Real.exp (-(160 * m * (x + 1) / (3 * ((m / 3 : ℕ) : ℝ) ^ 2))) := by
    simpa only [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hscalar := depth_scalar hx120
  change (101 / 100 : ℝ) * y ≤
    (999 / 6000 : ℝ) * x * Real.exp (-(303 / 2000 : ℝ) * y) at hscalar
  have htarget : (101 / 100 : ℝ) * ((n : ℝ) * y / x) ≤
      ((999 / 6000 : ℝ) * n) * Real.exp (-(303 / 2000 : ℝ) * y) := by
    have hh := mul_le_mul_of_nonneg_left hscalar (by positivity : 0 ≤ (n : ℝ) / x)
    convert hh using 1 <;> first | rfl | field_simp [hx0.ne']
  apply htarget.trans
  apply mul_le_mul _ hexp (by positivity) (by positivity)
  nlinarith


/-- The harmonic-avoidance theorem at an explicit size, retaining all public constants. -/
theorem harmonic_robustness {n : ℕ} (hn : 2 ^ 120 ≤ n)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ A : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n v i)) :
    (graphLaw (blockWidth n) p).probability (fun s =>
      BlockDepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n) (intervalWidth n)) ≥
      1 - failureBound n := by
  obtain ⟨hm, hmn, hb, _, he, hd, hcount⟩ := finite_parameters hn
  have hfinite := finite_block_robustness_overlap hm hmn hb he p havoid
  have hfailure : Real.exp (-((4 / 3 : ℝ) - Real.log 3) * (n / blockWidth n : ℕ)) ≤
      failureBound n := finite_failureBound_le hcount
  have hbound := (show 1 - failureBound n ≤
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * (n / blockWidth n : ℕ)) by
    linarith).trans hfinite
  apply hbound.trans
  apply FiniteLaw.probability_mono
  intro s hs
  simp only [sampledGraph, dif_pos (show 0 < blockWidth n by omega)]
  exact hs.mono le_rfl hd

/-- The explicit theorem for the exact public DRSample distribution. -/
theorem drsample_conjecture2 {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    ProofOfSpaceStatement.drsampleProbability n (fun parents =>
      ProofOfSpaceStatement.DRSampleBlockDepthRobust parents
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n) (intervalWidth n)) ≥
      1 - failureBound n := by
  have hn0 : 0 < n := by omega
  have hm : 0 < blockWidth n := by have := (finite_parameters hn).1; omega
  have h := harmonic_robustness hn (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp only [sampledGraph, dif_pos hm] at h
  rw [graphLaw_probability_as_pi hm (drIncomingLaw hn0)
    (fun G => BlockDepthRobust G (deletionBudget n)
      ((101 / 100 : ℝ) * targetDepth n) (intervalWidth n))] at h
  simp_rw [drIncomingLaw_as_map] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  simp_rw [incomingGraph_block_statement] at h
  rw [drsampleProbability_eq hn0]
  exact h

/-- Conjecture 1 holds at the same cutoff as Conjecture 2. -/
theorem drsample_conjecture1 {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    (drsampleLaw n (blockWidth n)).probability (fun s =>
      DepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n)) ≥ 1 - failureBound n := by
  have hn0 : 0 < n := by omega
  have h := harmonic_robustness hn (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp only [drsampleLaw, dif_pos hn0]
  apply h.trans
  apply FiniteLaw.probability_mono
  intro s hs
  exact hs.depthRobust (finite_parameters hn).2.2.2.1

/-- The same explicit threshold for Filecoin's ideal five-draw sampler. -/
theorem filecoin_bucket6 {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    (filecoinBucket6Law n (blockWidth n)).probability (fun s =>
      IndegreeAtMost (sampledGraph n (blockWidth n) s) 6 ∧
      BlockDepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n) (intervalWidth n) ∧
      DepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) ((101 / 100 : ℝ) * targetDepth n)) ≥ 1 - failureBound n := by
  have hp := finite_parameters hn
  have hn0 : 0 < n := by omega
  have hm0 : 0 < blockWidth n := by have := hp.1; omega
  simp only [filecoinBucket6Law, dif_pos hn0]
  have hblock := harmonic_robustness hn (filecoinIncomingLaw hn0)
    (fun _ hv A => filecoinIncomingLaw_avoidance_sharp (by omega) hv A)
  have hdegree : ∀ s : GraphSample n (blockWidth n),
      (graphLaw (blockWidth n) (filecoinIncomingLaw hn0)).weight s ≠ 0 →
        IndegreeAtMost (sampledGraph n (blockWidth n) s) 6 := by
    intro s hs
    simp only [sampledGraph, dif_pos hm0]
    exact filecoin_bucket6_indegree hn0 hm0 s hs
  rw [FiniteLaw.probability_and_of_support _ _ _ hdegree]
  apply hblock.trans
  apply FiniteLaw.probability_mono
  intro s hs
  exact ⟨hs, hs.depthRobust hp.2.2.2.1⟩

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.ShiftedRobustness
import ProofOfSpace.DRSample.LogEstimates
import ProofOfSpace.DRSample.MultiSamplerRegistry

/-! # Exponent-dependent sampler bounds

The current paper states asymptotic bounds for every fixed exponent in `(0,1)`.
We reuse the finite avoidance estimate with a block scale proportional to
`L(n) / ε`. The constants below are proof witnesses, not paper parameters.
This specializes the sampler avoidance argument to a fixed deletion fraction;
it does not assert the paper's general `eb ≥ β n` version.
-/
namespace ProofOfSpace.DRSample
open Finset Filter

noncomputable def robustnessScale (n : ℕ) : ℝ :=
  Real.logb 2 n / Real.logb 2 (Real.logb 2 n)

theorem robustnessScale_bounds {n : ℕ} (hn : 2 ^ 120 ≤ n) :
    16 ≤ robustnessScale n ∧ robustnessScale n ≤ Real.logb 2 n := by
  obtain ⟨hx, hy, hxy, _⟩ := log_parameters hn
  have hy0 : 0 < Real.logb 2 (Real.logb 2 n) := by linarith
  constructor
  · exact (le_div_iff₀ hy0).mpr hxy
  · apply (div_le_iff₀ hy0).mpr
    nlinarith

theorem eventually_scale_small_const (C : ℝ) (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2 ^ 120 ≤ n ∧
      C * (robustnessScale n / ε) ^ 2 ≤ n := by
  have hsmall := (Real.isLittleO_pow_logb_id_atTop (b := (2 : ℝ)) (n := 2)).bound
    (show 0 < ε ^ 2 / C by positivity)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [eventually_ge_atTop (2 ^ 120), hnat] with n hn hs
  have hL := robustnessScale_bounds hn
  have hx : 0 ≤ Real.logb 2 n := by linarith [hL.1, hL.2]
  simp only [Real.norm_eq_abs, id_eq] at hs
  rw [abs_of_nonneg (sq_nonneg (Real.logb 2 n)),
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hs
  refine ⟨hn, ?_⟩
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
  rw [div_mul_eq_mul_div] at hs
  have hs := (le_div_iff₀ hC).mp hs
  have hsq := sq_le_sq₀ (by linarith : 0 ≤ robustnessScale n) hx |>.mpr hL.2
  nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]

set_option maxHeartbeats 800000 in
-- The numerical bounds combine rounded parameters, logarithms, and exponentials.
/-- A fixed-fraction specialization of the current sampler avoidance lemma.
The witnesses are uniform in the exponent and the incoming-edge laws. -/
theorem eventually_avoidance_robustness {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, 2 ^ 120 ≤ n ∧ ∃ e b : ℕ,
      (1 / 200000 : ℝ) * (ε * n / robustnessScale n) ≤ e ∧
      (e : ℝ) ≤ 2000 * (ε * n / robustnessScale n) ∧
      (1 / 200000 : ℝ) * (robustnessScale n / ε) ≤ b ∧
      (b : ℝ) ≤ 2000 * (robustnessScale n / ε) ∧
      ∀ p : ℕ → FiniteLaw (Finset (Fin n)),
        (∀ v < n, ∀ U : Finset (Fin n),
          (p v).probability (fun parents => Disjoint parents U) ≤
            Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u)) →
        (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
          BlockDepthRobust (incomingGraph sets) e
            ((1 / 200000 : ℝ) * n / (Real.logb 2 n) ^ ε) b) ≥
          1 - Real.exp (-(1 / 200000 : ℝ) * (ε * n / robustnessScale n)) := by
  filter_upwards [eventually_scale_small_const (10 ^ 14) (by norm_num) hε] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let x := Real.logb 2 n
  let q := robustnessScale n / ε
  have hx : 120 ≤ x := (log_parameters hn.1).1
  have hx0 : 0 < x := by linarith
  have hL := robustnessScale_bounds hn.1
  have hL0 : 0 < robustnessScale n := by linarith [hL.1]
  have hq : 1 ≤ q := (le_div_iff₀ hε).mpr (by linarith [hL.1])
  have hq0 : 0 < q := by linarith
  have hsmall : (10 ^ 14 : ℝ) * q ^ 2 ≤ n := hn.2
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hnq : 200000 * q ≤ (n : ℝ) := by nlinarith
  have hratio : ε * n / robustnessScale n = (n : ℝ) / q := by
    dsimp [q]
    field_simp
  let a := Nat.ceil (100 * q)
  let B : ℝ := 20 * a
  let e := Nat.floor ((n : ℝ) / (100000 * q))
  let b := Nat.floor (1000 * q)
  have haLo : 100 * q ≤ (a : ℝ) := Nat.le_ceil _
  have haHi : (a : ℝ) < 100 * q + 1 := Nat.ceil_lt_add_one (by positivity)
  have ha : 0 < a := by exact_mod_cast (show (0 : ℝ) < a by nlinarith)
  have hBLo : 2000 * q ≤ B := by dsimp [B]; linarith
  have hBHi : B ≤ 2020 * q := by dsimp [B]; linarith
  have hB0 : 0 < B := by linarith
  have hBsmall : 4 * B ≤ (n : ℝ) := by nlinarith
  have hnB : 2 * (20 * a) < n := by
    exact_mod_cast (show 2 * (20 * (a : ℝ)) < n by change 2 * B < n; linarith)
  have heHi : (e : ℝ) ≤ (n : ℝ) / (100000 * q) := Nat.floor_le (by positivity)
  have heLo : (n : ℝ) / (100000 * q) - 1 < (e : ℝ) := Nat.sub_one_lt_floor _
  have heMul : (e : ℝ) * (100000 * q) ≤ n := (le_div_iff₀ (by positivity)).mp heHi
  have heTwo : (2 : ℝ) ≤ (n : ℝ) / (100000 * q) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hbHi : (b : ℝ) ≤ 1000 * q := Nat.floor_le (by positivity)
  have hbLo : 1000 * q - 1 < (b : ℝ) := Nat.sub_one_lt_floor _
  have hb : 0 < b := by exact_mod_cast (show (0 : ℝ) < b by linarith)
  have hbudget : (e : ℝ) * (b + 20 * a) ≤ ((n : ℝ) - 2 * (20 * a)) / 3 := by
    have hprod := mul_le_mul_of_nonneg_left
      (show (b : ℝ) + B ≤ 3020 * q by linarith) (Nat.cast_nonneg e)
    change (e : ℝ) * (b + B) ≤ ((n : ℝ) - 2 * B) / 3
    nlinarith
  refine ⟨hn.1, e, b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hratio]
    have hehalf : (n : ℝ) / (100000 * q) / 2 ≤ (e : ℝ) := by linarith
    calc
      _ = (n : ℝ) / (100000 * q) / 2 := by ring
      _ ≤ e := hehalf
  · rw [hratio]
    apply heHi.trans
    have hnq0 : 0 ≤ (n : ℝ) / q := by positivity
    calc
      _ = ((n : ℝ) / q) / 100000 := by ring
      _ ≤ _ := by linarith
  · change (1 / 200000 : ℝ) * q ≤ b
    linarith
  · change (b : ℝ) ≤ 2000 * q
    linarith
  intro p havoid
  have heta : 0 < 1 / (x + 1) := by positivity
  have hfinite := finite_avoidance_robustness ha hnB p heta havoid
  push_cast at hfinite
  have hdepth : (1 / 200000 : ℝ) * n / x ^ ε ≤
      (9 / 40 : ℝ) * ((n : ℝ) - 2 * B) * Real.exp (-323 / ((1 / (x + 1)) * B)) := by
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqEq : q * (ε * Real.log x) = x * Real.log 2 := by
      change (x / (Real.log x / Real.log 2) / ε) * (ε * Real.log x) = x * Real.log 2
      field_simp
    have hcoef : 323 / ((1 / (x + 1)) * B) ≤ ε * Real.log x := by
      apply (div_le_iff₀ (by positivity : 0 < (1 / (x + 1)) * B)).mpr
      rw [one_div_mul_eq_div, ← mul_div_assoc,
        le_div_iff₀ (by linarith : 0 < x + 1)]
      have hmul := mul_le_mul_of_nonneg_right hBLo (by positivity : 0 ≤ ε * Real.log x)
      nlinarith [Real.log_two_gt_d9]
    have hexp : (x ^ ε)⁻¹ ≤ Real.exp (-323 / ((1 / (x + 1)) * B)) := by
      rw [Real.rpow_def_of_pos hx0, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      rw [neg_div, mul_comm (Real.log x)]
      exact neg_le_neg hcoef
    have hmul := mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ (9 / 40 : ℝ) * ((n : ℝ) - 2 * B) by linarith)
    rw [div_eq_mul_inv]
    apply le_trans ?_ hmul
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hfailure : B * Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) ≤
      Real.exp (-(1 / 200000 : ℝ) * (ε * n / robustnessScale n)) := by
    have hk : (1 / 5 : ℝ) ≤ (8 / 5 : ℝ) - Real.log 4 := by
      have hl := Real.log_pow (2 : ℝ) 2
      norm_num at hl
      linarith [Real.log_two_lt_d9]
    have hlogB : Real.log B ≤ B := (Real.log_le_sub_one_of_pos hB0).trans (by linarith)
    have hnB4 : (4 : ℝ) ≤ (n : ℝ) / B := (le_div_iff₀ hB0).mpr hBsmall
    have hquot : (n : ℝ) / (2020 * q) ≤ (n : ℝ) / B :=
      div_le_div_of_nonneg_left hn0.le hB0 hBHi
    have hcost : B + 2 / 5 ≤ (n : ℝ) / (20200 * q) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hprod := mul_le_mul_of_nonneg_right hBHi hq0.le
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hk (by linarith : 0 ≤ (n : ℝ) / B - 2)
    have hexponent : Real.log B - ((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2) ≤
        -(1 / 200000 : ℝ) * (ε * n / robustnessScale n) := by
      rw [hratio]
      have heq1 : (n : ℝ) / (2020 * q) = ((n : ℝ) / q) / 2020 := by ring
      have heq2 : (n : ℝ) / (20200 * q) = ((n : ℝ) / q) / 20200 := by ring
      rw [heq1] at hquot
      rw [heq2] at hcost
      have : 0 ≤ (n : ℝ) / q := by positivity
      linarith
    calc
      _ = Real.exp (Real.log B - ((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) := by
        rw [Real.exp_sub, Real.exp_log hB0, neg_mul, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  have hbound := (show 1 - Real.exp (-(1 / 200000 : ℝ) * (ε * n / robustnessScale n)) ≤
      1 - B * Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) by linarith).trans hfinite
  apply hbound.trans
  apply FiniteLaw.probability_mono
  intro sets hs
  exact (hs e b hb hbudget).mono le_rfl hdepth

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.Fractional
import ProofOfSpace.DRSample.GeneralParameters

/-! # Fractional robustness of DRSample and BucketSample

The constants depend only on the prescribed fraction `0 < f < 1/2`.
The two directions hold on the same block-robustness event, and the same
constants and size threshold work for every positive number of bucket draws.
-/
namespace ProofOfSpace.DRSample
open Finset Filter ProofOfSpaceStatement

/-- Apply the deterministic fractional conversion while retaining uniform
asymptotic constants and absorbing the rounding of the deletion budget. -/
theorem eventually_fractional_avoidance {f : ℝ} (hf : 0 < f) (hfHalf : f < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n : ℕ in atTop, 2 ^ 120 ≤ n ∧ ∃ e : ℕ,
        c * (ε * n / robustnessScale n) ≤ e ∧
        (e : ℝ) ≤ C * (ε * n / robustnessScale n) ∧
        ∀ p : ℕ → FiniteLaw (Finset (Fin n)),
          (∀ v < n, ∀ U : Finset (Fin n),
            (p v).probability (fun parents => Disjoint parents U) ≤
              Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u)) →
          (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
            FractionalDepthRobust (incomingGraph sets).edge e
              (c * n / (Real.logb 2 n) ^ ε) f f) ≥
            1 - Real.exp (-c * (ε * n / robustnessScale n)) := by
  classical
  let β := f + 1 / 2
  obtain ⟨c, C, hc, hC, hparams⟩ := eventually_avoidance_product
    (show 0 < β by dsimp [β]; linarith) (show β < 1 by dsimp [β]; linarith)
  refine ⟨c / 4, C, by positivity, hC, ?_⟩
  intro ε hε hε1
  let Q := 1 + C + 4 / c
  have hQ : 0 < Q := by dsimp [Q]; positivity
  filter_upwards [hparams ε hε hε1, eventually_scale_small_const Q hQ hε] with n hn hsmall
  obtain ⟨hn, e, b, heLo, heHi, hbLo, hbHi, heb, hrobust⟩ := hn
  let q := robustnessScale n / ε
  have hL := robustnessScale_bounds hn
  have hq : 1 ≤ q := (le_div_iff₀ hε).mpr (by linarith [hL.1])
  have hq0 : 0 < q := by linarith
  have hL0 : 0 < robustnessScale n := by linarith [hL.1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : ε * n / robustnessScale n = (n : ℝ) / q := by dsimp [q]; field_simp
  have hterm (z : ℝ) (hz : 0 ≤ z) (hzQ : z ≤ Q) : z * q ≤ (n : ℝ) := by
    have hq2 : q ≤ q ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hq2 hz).trans
      ((mul_le_mul_of_nonneg_right hzQ (sq_nonneg q)).trans hsmall.2)
  have hb : 1 ≤ b := by
    have : (0 : ℝ) < b := lt_of_lt_of_le (by positivity : 0 < c * q) hbLo
    have : 0 < b := by exact_mod_cast this
    omega
  have hbn : b ≤ n := by
    have hCQ : C ≤ Q := by
      dsimp [Q]
      have : 0 < 4 / c := by positivity
      linarith
    exact_mod_cast hbHi.trans (hterm C hC.le hCQ)
  have he2 : 2 ≤ e := by
    have hfour := hterm (4 / c) (by positivity) (by dsimp [Q]; linarith)
    have hfour' : (4 : ℝ) ≤ c * ((n : ℝ) / q) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hq0).mpr
      have hh := mul_le_mul_of_nonneg_left hfour hc.le
      have hcancel : c * (4 / c * q) = 4 * q := by field_simp
      rwa [hcancel] at hh
    rw [hratio] at heLo
    have : (2 : ℝ) ≤ e := by linarith
    exact_mod_cast this
  have hhalf : (e : ℝ) / 4 ≤ (e / 2 : ℕ) := by
    have hnat : e ≤ 4 * (e / 2) := by omega
    have hreal : (e : ℝ) ≤ 4 * (e / 2 : ℕ) := by exact_mod_cast hnat
    linarith
  refine ⟨hn, e / 2, ?_, ?_, ?_⟩
  · nlinarith only [heLo, hhalf]
  · exact (Nat.cast_le.mpr (Nat.div_le_self e 2)).trans heHi
  intro p havoid
  have hfrac : f ≤ (e : ℝ) * b / (2 * n) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hβ : 2 * f ≤ β := by dsimp [β]; linarith
    have hfn : f * (2 * (n : ℝ)) ≤ β * n := by
      nlinarith only [mul_le_mul_of_nonneg_right hβ hn0.le]
    exact hfn.trans heb
  have hdepth : c / 4 * n / (Real.logb 2 n) ^ ε ≤ c * n / (Real.logb 2 n) ^ ε := by
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by
      have hx := (log_parameters hn).1
      linarith) _)
    nlinarith only [hc, hn0]
  have hfail : 1 - Real.exp (-(c / 4) * (ε * n / robustnessScale n)) ≤
      1 - Real.exp (-c * (ε * n / robustnessScale n)) := by
    have hx : 0 ≤ ε * n / robustnessScale n := by positivity
    have hh : -c * (ε * n / robustnessScale n) ≤ -(c / 4) * (ε * n / robustnessScale n) := by
      nlinarith [mul_nonneg hc.le hx]
    linarith only [Real.exp_le_exp.mpr hh]
  apply (hfail.trans (hrobust p havoid)).trans
  apply FiniteLaw.probability_mono
  intro sets hs
  have hs' : GraphBlockDepthRobust (incomingGraph sets).edge e
      (c * n / (Real.logb 2 n) ^ ε) b := by
    simpa only [GraphBlockDepthRobust, BlockDepthRobust, HasPath, blockDeleted,
      mem_filter, mem_univ, true_and, not_exists, not_and] using hs
  exact (hs'.fractional (fun u v huv => ⟨by change u.val < v.val; omega, Or.inl huv⟩)
    hb hbn).mono le_rfl hdepth hfrac hfrac

end ProofOfSpace.DRSample

namespace ProofOfSpaceStatement
open Finset Filter ProofOfSpace.DRSample

/-- Paper result `cor:bucket-fractional`, for DRSample. -/
theorem drsample_fractional_robustness {f : ℝ} (hf : 0 < f) (hfHalf : f < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e : ℕ, c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          drsampleProbability n (fun parents => FractionalDepthRobust (drsampleEdge parents)
            e (c * n / (Real.logb 2 n) ^ ε) f f) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  obtain ⟨c, C, hc, hC, hparams⟩ := eventually_fractional_avoidance hf hfHalf
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε hε1
  filter_upwards [hparams ε hε hε1] with n hn
  obtain ⟨hn, e, heLo, heHi, hrobust⟩ := hn
  refine ⟨e, heLo, heHi, ?_⟩
  have hn0 : 0 < n := by omega
  have h := hrobust (drIncomingLaw hn0)
    (fun _ hv A => drIncomingLaw_avoidance_sharp (by omega) hv A)
  simp_rw [drIncomingLaw_as_map] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  have hedge (parents : Fin n → Fin n) :
      (incomingGraph (fun v => sampledParents v.val (fun _ : Fin 1 => parents v))).edge =
        drsampleEdge parents := by
    funext u v
    simp [incomingGraph, sampledParents, drsampleEdge, eq_comm]
    tauto
  simp_rw [hedge] at h
  rw [← drsampleProbability_eq hn0] at h
  exact h

/-- Paper result `cor:bucket-fractional`, for every positive number of draws. -/
theorem bucketSample_fractional_robustness {f : ℝ} (hf : 0 < f) (hfHalf : f < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ, 1 ≤ r → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e : ℕ, c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          bucketSampleProbability n r (fun parents =>
            FractionalDepthRobust (multiSampleEdge parents)
              e (c * n / (Real.logb 2 n) ^ ε) f f) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  classical
  obtain ⟨c, C, hc, hC, hparams⟩ := eventually_fractional_avoidance hf hfHalf
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε hε1 r hr
  filter_upwards [hparams ε hε hε1] with n hn
  obtain ⟨hn, e, heLo, heHi, hrobust⟩ := hn
  refine ⟨e, heLo, heHi, ?_⟩
  have hn0 : 0 < n := by omega
  have hr0 : 0 < r := by omega
  have h := hrobust (bucketIncomingLaw hn0 hr0)
    (fun _ hv A => bucketIncomingLaw_avoidance_sharp (by omega) hr0 hv A)
  simp only [bucketIncomingLaw, parentSetLaw] at h
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map] at h
  have hedge (parents : Fin n → Fin r → Fin n) :
      (incomingGraph (fun v => sampledParents v.val (parents v))).edge =
        multiSampleEdge parents := by
    funext u v
    simp [incomingGraph, sampledParents, multiSampleEdge]
    tauto
  simp_rw [hedge] at h
  rw [← bucketSampleProbability_eq hn0 hr0] at h
  exact h

end ProofOfSpaceStatement

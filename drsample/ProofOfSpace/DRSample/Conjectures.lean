import ProofOfSpace.DRSample.Degree
import ProofOfSpace.DRSample.Parameters

/-! # Conjectures 1 and 2, and Filecoin's indegree-six corollary

All logarithms in the parameters have base two. The probability bound is
explicit, tends to one, and quantifies over deleted sets after sampling.
-/
namespace ProofOfSpace.DRSample
open Finset Classical Filter

abbrev GraphSample (n m : ℕ) := SampleSpace (Fin m → Finset (Fin n)) (n / m + 1)

/-- A total definition; the zero-width branch is irrelevant to the eventual results. -/
def sampledGraph (n m : ℕ) (s : GraphSample n m) : OrderedGraph n :=
  if hm : 0 < m then rowGraph hm (n / m + 1) s else
    { edge := fun u v => u.val + 1 = v.val
      increasing := fun h => by change _ < _; omega }

noncomputable def drsampleLaw (n m : ℕ) : FiniteLaw (GraphSample n m) :=
  graphLaw m (fun j => if hn : 0 < n then drIncomingLaw hn j else FiniteLaw.pure ∅)

noncomputable def filecoinBucket6Law (n m : ℕ) : FiniteLaw (GraphSample n m) :=
  graphLaw m (fun j => if hn : 0 < n then filecoinIncomingLaw hn j else FiniteLaw.pure ∅)

noncomputable def failureBound (n : ℕ) : ℝ :=
  Real.exp (-(1 / 14060 : ℝ) * targetDepth n)

theorem failure_coefficient_pos : 0 < (4 / 3 : ℝ) - Real.log 3 := by
  have hlog3 : Real.log 3 < 6 / 5 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) ≠ 1)
    rw [show (3 : ℝ) = 2 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  linarith

/-- The rounded failure coefficient follows from the finite block count. -/
theorem finite_failureBound_le {n m : ℕ} (hcount : targetDepth n / 3300 ≤ (m : ℝ)) :
    Real.exp (-((4 / 3 : ℝ) - Real.log 3) * m) ≤ failureBound n := by
  have hcoef : (3300 / 14060 : ℝ) ≤ (4 / 3 : ℝ) - Real.log 3 := by
    linarith [Real.log_three_lt_d9]
  apply Real.exp_le_exp.mpr
  change -((4 / 3 : ℝ) - Real.log 3) * m ≤ -(1 / 14060 : ℝ) * targetDepth n
  have h := mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 3300 / 14060)
  have hc := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

theorem conjecture_at_parameters {n : ℕ}
    (hm : 12 ≤ blockWidth n) (hmn : blockWidth n ≤ n)
    (hb : intervalWidth n ≤ blockWidth n)
    (he : 2 * deletionBudget n ≤ (n / blockWidth n) / 3)
    (hd : targetDepth n ≤ ((blockWidth n : ℝ) * (n / blockWidth n : ℕ) / 18) *
      Real.exp (-(160 * blockWidth n * (Real.logb 2 n + 1) / (blockWidth n / 3 : ℕ) ^ 2)))
    (hcount : targetDepth n / 3300 ≤ (n / blockWidth n : ℕ))
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ A : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n v i)) :
    (graphLaw (blockWidth n) p).probability (fun s =>
      BlockDepthRobust (sampledGraph n (blockWidth n) s)
        (deletionBudget n) (targetDepth n) (intervalWidth n)) ≥ 1 - failureBound n := by
  have hfinite := finite_block_robustness_sharp hm hmn hb he p havoid
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

theorem targetDepth_tendsto : Tendsto targetDepth atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hnat
  apply tendsto_atTop_mono' _ _ hsqrt
  have hsmall := hnat.eventually (logb_eventually_le_rpow (C := 1) (r := 1 / 2) (by norm_num) (by norm_num))
  filter_upwards [hsmall, eventually_log_parameters] with n hsmall hn
  have hx1 : 1 ≤ Real.logb 2 n := hn.2.1.trans hn.2.2.1
  have hx : 0 < Real.logb 2 n := by linarith
  have hxsmall : Real.logb 2 n ≤ Real.sqrt (n : ℝ) := by simpa [Real.sqrt_eq_rpow] using hsmall
  unfold targetDepth
  apply (le_div_iff₀ hx).mpr
  have h1 := mul_le_mul_of_nonneg_left hxsmall (Real.sqrt_nonneg (n : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hn.2.1 (Nat.cast_nonneg n)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- The explicit exponentially small failure bound tends to zero. -/
theorem failureBound_tendsto_zero : Tendsto failureBound atTop (nhds 0) := by
  have hc : 0 < (1 / 14060 : ℝ) := by norm_num
  have h := targetDepth_tendsto.const_mul_atTop hc
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  change Tendsto (fun n => Real.exp (-(1 / 14060 : ℝ) *
    targetDepth n)) atTop (nhds 0)
  simpa only [Function.comp_def, neg_mul] using he

end ProofOfSpace.DRSample

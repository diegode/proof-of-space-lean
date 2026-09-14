import ProofOfSpace.DRSample.Samplers

namespace ProofOfSpace.DRSample
open Finset Classical

/-- BucketSample uses the same fine position `r v` for all `r` draws. -/
noncomputable def bucketParentLaw {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (v : ℕ) :
    FiniteLaw (Fin n) :=
  if hv : v < n then
    if hv2 : 2 ≤ v then contractedBucketLaw false r v (Nat.clog 2 (r * v))
      hr hv (by nlinarith) (Nat.clog_pos (by norm_num) (by nlinarith))
    else FiniteLaw.pure ⟨0, hn⟩
  else FiniteLaw.pure ⟨0, hn⟩

theorem bucketParentLaw_weight_ge {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    {v : ℕ} (hv : v < n) (u : Fin n) (hu : u.val + 2 ≤ v) :
    (1 / (Real.logb 2 (r * n : ℕ) + 1)) / (v - u.val : ℕ) ≤
      (bucketParentLaw hn hr v).weight u := by
  have hv2 : 2 ≤ v := by omega
  have hrv : 2 ≤ r * v := by nlinarith
  have hB := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < r * v)
  rw [bucketParentLaw, dif_pos hv, dif_pos hv2]
  apply le_trans _ (contractedBucketLaw_weight_ge_sharp false r v _ hr hv hrv hB le_rfl u hu)
  rw [div_div]
  have hc := bucketCount_real_bound_sharp hrv (Nat.mul_le_mul_left r hv.le)
  have hBR : (0 : ℝ) < Nat.clog 2 (r * v) := by exact_mod_cast hB
  have hd : (0 : ℝ) < (v - u.val : ℕ) := by exact_mod_cast (show 0 < v - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

noncomputable def bucketIncomingLaw {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (v : ℕ) :
    FiniteLaw (Finset (Fin n)) := parentSetLaw r v (bucketParentLaw hn hr v)

theorem bucketIncomingLaw_avoidance {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r)
    {v : ℕ} (hv : v < n) (A : Finset (Fin n)) :
    (bucketIncomingLaw (by omega) hr v).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-((r : ℝ) / (Real.logb 2 (r * n : ℕ) + 1)) * ∑ i ∈ A, harmonicAt n v i) := by
  have hlog := logb_two_ge_one (show 2 ≤ r * n by nlinarith)
  simpa [bucketIncomingLaw, div_eq_mul_inv] using
    parentSetLaw_avoidance_harmonic (d := r) (bucketParentLaw (by omega) hr v)
      (by positivity) (bucketParentLaw_weight_ge (by omega) hr hv) A

theorem bucket_coefficient_ge {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r) :
    1 / (Real.logb 2 n + 1) ≤ (r : ℝ) / (Real.logb 2 (r * n : ℕ) + 1) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := logb_two_ge_one hn
  have hlogr := logb_two_ge_one (show 2 ≤ r * n by nlinarith)
  have hrlog : Real.logb 2 r ≤ (r : ℝ) - 1 := by
    apply (Real.logb_le_iff_le_rpow (by norm_num) hrR).mpr
    have hpow : r ≤ 2 ^ (r - 1) := by have := Nat.lt_two_pow_self (n := r - 1); omega
    have he : (r : ℝ) - 1 = ((r - 1 : ℕ) : ℝ) := by push_cast [Nat.one_le_iff_ne_zero.mpr hr.ne']; rfl
    rw [he, Real.rpow_natCast]
    exact_mod_cast hpow
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Nat.cast_mul, Real.logb_mul hrR.ne' hnR.ne']
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

theorem bucketIncomingLaw_avoidance_sharp {n r : ℕ} (hn : 2 ≤ n) (hr : 0 < r)
    {v : ℕ} (hv : v < n) (A : Finset (Fin n)) :
    (bucketIncomingLaw (by omega) hr v).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n v i) := by
  apply (bucketIncomingLaw_avoidance hn hr hv A).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right (neg_le_neg (bucket_coefficient_ge hn hr))
  exact sum_nonneg fun i _ => by unfold harmonicAt; positivity

end ProofOfSpace.DRSample

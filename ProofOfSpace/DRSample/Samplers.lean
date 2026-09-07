import ProofOfSpace.DRSample.ParentLaw
import ProofOfSpace.DRSample.ParentAvoidance

/-! # DRSample and Filecoin's indegree-six bucket sampler

Randomness means independent uniform bucket and distance choices. This is the
idealized graph distribution, not a claim about the fixed ChaCha seed used by
the deployed implementation.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem dr_bucket_cover (j : ℕ) : Nat.clog 2 (1 * j) ≤ Nat.log 2 (j + 1) + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (j + 1)
  simpa only [one_mul] using (show j ≤ 2 ^ (Nat.log 2 (j + 1) + 1) by omega)

noncomputable def drParentLaw {n : ℕ} (hn : 0 < n) (j : ℕ) : FiniteLaw (Fin n) :=
  if hj : j < n then
    if hj2 : 2 ≤ j then contractedBucketLaw true 1 j (Nat.log 2 (j + 1) + 1)
      (by norm_num) hj (by omega) (by omega)
    else FiniteLaw.pure ⟨0, hn⟩
  else FiniteLaw.pure ⟨0, hn⟩

noncomputable def filecoinParentLaw {n : ℕ} (hn : 0 < n) (j : ℕ) : FiniteLaw (Fin n) :=
  if hj : j < n then
    if hj2 : 2 ≤ j then contractedBucketLaw false 5 j (Nat.clog 2 (5 * j))
      (by norm_num) hj (by omega) (Nat.clog_pos (by norm_num) (by omega))
    else FiniteLaw.pure ⟨0, hn⟩
  else FiniteLaw.pure ⟨0, hn⟩

theorem logb_two_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).mpr
  simpa using (show (2 : ℝ) ≤ n by exact_mod_cast hn)

theorem dr_bucket_count_le {j n : ℕ} (hj : j < n) (hn : 2 ≤ n) :
    ((Nat.log 2 (j + 1) + 1 : ℕ) : ℝ) ≤ 2 * Real.logb 2 n := by
  have hfloor := Real.natLog_le_logb (j + 1) 2
  have hmono : Real.logb 2 (j + 1 : ℕ) ≤ Real.logb 2 n := by
    apply (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr
    exact_mod_cast (show j + 1 ≤ n by omega)
  have hlog := logb_two_ge_one hn
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hfloor hmono ⊢
  linarith

theorem drParentLaw_weight_ge {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (4 * Real.logb 2 n)) / (j - u.val : ℕ) ≤ (drParentLaw hn j).weight u := by
  have hj2 : 2 ≤ j := by omega
  have hn2 : 2 ≤ n := by omega
  rw [drParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge true 1 j _ (by norm_num) hj
    (by omega) (by omega) (dr_bucket_cover j) u hu)
  rw [div_div]
  have hc := dr_bucket_count_le hj hn2
  have hB : (0 : ℝ) < (Nat.log 2 (j + 1) + 1 : ℕ) := by positivity
  have hr : (0 : ℝ) < (j - u.val : ℕ) := by exact_mod_cast (show 0 < j - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem filecoinParentLaw_weight_ge {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (4 * Real.logb 2 (5 * n : ℕ))) / (j - u.val : ℕ) ≤
      (filecoinParentLaw hn j).weight u := by
  have hj2 : 2 ≤ j := by omega
  have hv : 2 ≤ 5 * j := by omega
  have hB := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < 5 * j)
  rw [filecoinParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge false 5 j _ (by norm_num) hj hv hB le_rfl u hu)
  rw [div_div]
  have hc := bucketCount_real_bound hv (show 5 * j ≤ 5 * n by omega)
  have hBR : (0 : ℝ) < Nat.clog 2 (5 * j) := by exact_mod_cast hB
  have hr : (0 : ℝ) < (j - u.val : ℕ) := by exact_mod_cast (show 0 < j - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

noncomputable def drIncomingLaw {n : ℕ} (hn : 0 < n) (j : ℕ) : FiniteLaw (Finset (Fin n)) :=
  parentSetLaw 1 j (drParentLaw hn j)

noncomputable def filecoinIncomingLaw {n : ℕ} (hn : 0 < n) (j : ℕ) : FiniteLaw (Finset (Fin n)) :=
  parentSetLaw 5 j (filecoinParentLaw hn j)

theorem drIncomingLaw_avoidance {n : ℕ} (hn : 2 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (drIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (4 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_one hn
  simpa [drIncomingLaw] using parentSetLaw_avoidance_harmonic (d := 1)
    (drParentLaw (by omega) j) (by positivity) (drParentLaw_weight_ge (by omega) hj) A

theorem filecoin_log_bound {n : ℕ} (hn : 5 ≤ n) :
    Real.logb 2 (5 * n : ℕ) ≤ 2 * Real.logb 2 n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmono : Real.logb 2 5 ≤ Real.logb 2 n :=
    (Real.logb_le_logb (by norm_num) (by norm_num) hnR).mpr (by exact_mod_cast hn)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.logb_mul (by norm_num) hnR.ne']
  linarith

theorem filecoinIncomingLaw_avoidance {n : ℕ} (hn : 5 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (filecoinIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (4 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_one (show 2 ≤ n by omega)
  have hlog5 := logb_two_ge_one (show 2 ≤ 5 * n by omega)
  have h := parentSetLaw_avoidance_harmonic (d := 5) (filecoinParentLaw (by omega) j)
    (by positivity) (filecoinParentLaw_weight_ge (by omega) hj) A
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hc : 1 / (4 * Real.logb 2 n) ≤ 5 * (1 / (4 * Real.logb 2 (5 * n : ℕ))) := by
    have hb := filecoin_log_bound hn
    rw [← mul_div_assoc, mul_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hw : 0 ≤ ∑ i ∈ A, harmonicAt n j i := by
    apply sum_nonneg
    intro i _
    unfold harmonicAt
    positivity
  exact mul_le_mul_of_nonneg_right (neg_le_neg hc) hw

end ProofOfSpace.DRSample

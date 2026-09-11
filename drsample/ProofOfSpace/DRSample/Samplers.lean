import ProofOfSpace.DRSample.ParentLaw
import ProofOfSpace.DRSample.ParentAvoidance

/-! # DRSample and Filecoin's indegree-six bucket sampler

Randomness means independent uniform bucket and distance choices. This is the
idealized graph distribution, not a claim about the fixed ChaCha seed used by
the deployed implementation.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem dr_bucket_cover (j : ℕ) : Nat.clog 2 (1 * j) ≤ Nat.clog 2 (j + 1) := by
  simpa only [one_mul] using Nat.clog_mono_right 2 (Nat.le_succ j)

theorem dr_bucket_count_pos {j : ℕ} (hj : 2 ≤ j) : 0 < Nat.clog 2 (j + 1) :=
  Nat.clog_pos (by norm_num) (by omega)

noncomputable def drParentLaw {n : ℕ} (hn : 0 < n) (j : ℕ) : FiniteLaw (Fin n) :=
  if hj : j < n then
    if hj2 : 2 ≤ j then contractedBucketLaw true 1 j (Nat.clog 2 (j + 1))
      (by norm_num) hj (by omega) (dr_bucket_count_pos hj2)
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
    ((Nat.clog 2 (j + 1) : ℕ) : ℝ) ≤ 2 * Real.logb 2 n := by
  by_cases hj0 : j = 0
  · have hlog := logb_two_ge_one (show 2 ≤ n by omega)
    simp only [hj0, Nat.zero_add, Nat.clog_one_right, Nat.cast_zero]
    linarith
  · have hbound := bucketCount_real_bound_sharp (show 2 ≤ j + 1 by omega)
      (show j + 1 ≤ n by omega)
    have hlog := logb_two_ge_one hn
    linarith

theorem drParentLaw_weight_ge {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (4 * Real.logb 2 n)) / (j - u.val : ℕ) ≤ (drParentLaw hn j).weight u := by
  have hj2 : 2 ≤ j := by omega
  have hn2 : 2 ≤ n := by omega
  rw [drParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge true 1 j _ (by norm_num) hj
    (by omega) (dr_bucket_count_pos hj2) (dr_bucket_cover j) u hu)
  rw [div_div]
  have hc := dr_bucket_count_le hj hn2
  have hB : (0 : ℝ) < (Nat.clog 2 (j + 1) : ℕ) := by exact_mod_cast dr_bucket_count_pos hj2
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

theorem logb_two_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).mpr
  norm_num
  exact_mod_cast hn

theorem dr_bucket_count_le_three_halves {j n : ℕ} (hj : j < n) (hn : 4 ≤ n) :
    ((Nat.clog 2 (j + 1) : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * Real.logb 2 n := by
  by_cases hj0 : j = 0
  · have hlog := logb_two_ge_one (show 2 ≤ n by omega)
    simp only [hj0, Nat.zero_add, Nat.clog_one_right, Nat.cast_zero]
    linarith
  · have hbound := bucketCount_real_bound_sharp (show 2 ≤ j + 1 by omega)
      (show j + 1 ≤ n by omega)
    have hlog := logb_two_ge_two hn
    linarith

theorem drParentLaw_weight_ge_three {n : ℕ} (hn : 4 ≤ n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (3 * Real.logb 2 n)) / (j - u.val : ℕ) ≤ (drParentLaw (by omega) j).weight u := by
  have hj2 : 2 ≤ j := by omega
  rw [drParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge true 1 j _ (by norm_num) hj
    (by omega) (dr_bucket_count_pos hj2) (dr_bucket_cover j) u hu)
  rw [div_div]
  have hc := dr_bucket_count_le_three_halves hj hn
  have hB : (0 : ℝ) < (Nat.clog 2 (j + 1) : ℕ) := by exact_mod_cast dr_bucket_count_pos hj2
  have hr : (0 : ℝ) < (j - u.val : ℕ) := by exact_mod_cast (show 0 < j - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem drIncomingLaw_avoidance_three {n : ℕ} (hn : 4 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (drIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (3 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_two hn
  simpa [drIncomingLaw] using parentSetLaw_avoidance_harmonic (d := 1)
    (drParentLaw (by omega) j) (by positivity) (drParentLaw_weight_ge_three hn hj) A

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

theorem filecoinIncomingLaw_avoidance_three {n : ℕ} (hn : 5 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (filecoinIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (3 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_one (show 2 ≤ n by omega)
  have hlog5 := logb_two_ge_one (show 2 ≤ 5 * n by omega)
  have h := parentSetLaw_avoidance_harmonic (d := 5) (filecoinParentLaw (by omega) j)
    (by positivity) (filecoinParentLaw_weight_ge (by omega) hj) A
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hc : 1 / (3 * Real.logb 2 n) ≤ 5 * (1 / (4 * Real.logb 2 (5 * n : ℕ))) := by
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

theorem dr_bucket_count_le_sharp {j n : ℕ} (hj : j < n) (hn : 2 ≤ n) :
    ((Nat.clog 2 (j + 1) : ℕ) : ℝ) ≤ Real.logb 2 n + 1 := by
  by_cases hj0 : j = 0
  · have hlog := logb_two_ge_one (show 2 ≤ n by omega)
    simp only [hj0, Nat.zero_add, Nat.clog_one_right, Nat.cast_zero]
    linarith
  · have hbound := bucketCount_real_bound_sharp (show 2 ≤ j + 1 by omega)
      (show j + 1 ≤ n by omega)
    exact hbound

theorem drParentLaw_weight_ge_sharp {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (Real.logb 2 n + 1)) / (j - u.val : ℕ) ≤ (drParentLaw hn j).weight u := by
  have hj2 : 2 ≤ j := by omega
  have hn2 : 2 ≤ n := by omega
  rw [drParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge_sharp true 1 j _ (by norm_num) hj
    (by omega) (dr_bucket_count_pos hj2) (dr_bucket_cover j) u hu)
  rw [div_div]
  have hc := dr_bucket_count_le_sharp hj hn2
  have hB : (0 : ℝ) < (Nat.clog 2 (j + 1) : ℕ) := by exact_mod_cast dr_bucket_count_pos hj2
  have hr : (0 : ℝ) < (j - u.val : ℕ) := by exact_mod_cast (show 0 < j - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem filecoinParentLaw_weight_ge_sharp {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 / (Real.logb 2 (5 * n : ℕ) + 1)) / (j - u.val : ℕ) ≤
      (filecoinParentLaw hn j).weight u := by
  have hj2 : 2 ≤ j := by omega
  have hv : 2 ≤ 5 * j := by omega
  have hB := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < 5 * j)
  rw [filecoinParentLaw, dif_pos hj, dif_pos hj2]
  apply le_trans _ (contractedBucketLaw_weight_ge_sharp false 5 j _ (by norm_num) hj hv hB le_rfl u hu)
  rw [div_div]
  have hc := bucketCount_real_bound_sharp hv (show 5 * j ≤ 5 * n by omega)
  have hBR : (0 : ℝ) < Nat.clog 2 (5 * j) := by exact_mod_cast hB
  have hr : (0 : ℝ) < (j - u.val : ℕ) := by exact_mod_cast (show 0 < j - u.val by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem drIncomingLaw_avoidance_sharp {n : ℕ} (hn : 2 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (drIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_one hn
  simpa [drIncomingLaw] using parentSetLaw_avoidance_harmonic (d := 1)
    (drParentLaw (by omega) j) (by positivity) (drParentLaw_weight_ge_sharp (by omega) hj) A

theorem filecoinIncomingLaw_avoidance_sharp {n : ℕ} (hn : 5 ≤ n) {j : ℕ} (hj : j < n)
    (A : Finset (Fin n)) :
    (filecoinIncomingLaw (by omega) j).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n j i) := by
  have hlog := logb_two_ge_one (show 2 ≤ n by omega)
  have hlog5 := logb_two_ge_one (show 2 ≤ 5 * n by omega)
  have h := parentSetLaw_avoidance_harmonic (d := 5) (filecoinParentLaw (by omega) j)
    (by positivity) (filecoinParentLaw_weight_ge_sharp (by omega) hj) A
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hc : 1 / (Real.logb 2 n + 1) ≤ 5 * (1 / (Real.logb 2 (5 * n : ℕ) + 1)) := by
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

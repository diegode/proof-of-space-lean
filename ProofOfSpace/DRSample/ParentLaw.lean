import ProofOfSpace.DRSample.BucketLaw
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Bucket distances mapped to graph parents -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem FiniteLaw.probability_ge_sum {α : Type*} [Fintype α] (p : FiniteLaw α)
    (Q : α → Prop) (s : Finset α) (hs : ∀ a ∈ s, Q a) :
    ∑ a ∈ s, p.weight a ≤ p.probability Q := by
  calc
    _ = ∑ a ∈ s, if Q a then p.weight a else 0 := by
      apply sum_congr rfl
      intro a ha
      simp [hs a ha]
    _ ≤ p.probability Q := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ s)
      intro a _ _
      exact ite_nonneg (p.nonneg a) le_rfl

def contractedParent {n : ℕ} (q j : ℕ) (hq : 0 < q) (hj : j < n)
    (r : Fin (q * j + 1)) : Fin n :=
  ⟨(q * j - r.val) / q, by
    have hle : (q * j - r.val) / q ≤ j := by
      calc (q * j - r.val) / q ≤ (q * j) / q := Nat.div_le_div_right (Nat.sub_le _ _)
        _ = j := Nat.mul_div_cancel_left j hq
    omega⟩

noncomputable def contractedBucketLaw {n : ℕ} (roundUp : Bool) (q j B : ℕ)
    (hq : 0 < q) (hj : j < n) (hv : 2 ≤ q * j) (hB : 0 < B) : FiniteLaw (Fin n) :=
  (bucketLaw roundUp (q * j) B hv hB).map (contractedParent q j hq hj)

def parentDistance {n : ℕ} (q j : ℕ) (hq : 0 < q) (u : Fin n) (hu : u.val + 2 ≤ j)
    (a : Fin q) : Fin (q * j + 1) :=
  ⟨q * (j - u.val) - a.val, by
    have hle : q * (j - u.val) ≤ q * j := Nat.mul_le_mul_left q (Nat.sub_le _ _)
    omega⟩

theorem parentDistance_ge_two {n : ℕ} (q j : ℕ) (hq : 0 < q)
    (u : Fin n) (hu : u.val + 2 ≤ j) (a : Fin q) :
    2 ≤ (parentDistance q j hq u hu a).val := by
  have hr : 2 ≤ j - u.val := by omega
  have ha := a.isLt
  dsimp [parentDistance]
  have hmul : 2 * q ≤ q * (j - u.val) := by nlinarith
  omega

theorem parentDistance_injective {n : ℕ} (q j : ℕ) (hq : 0 < q)
    (u : Fin n) (hu : u.val + 2 ≤ j) : Function.Injective (parentDistance q j hq u hu) := by
  intro a b heq
  have heq' := congrArg Fin.val heq
  dsimp [parentDistance] at heq'
  have ha := a.isLt
  have hb := b.isLt
  have hmul : q ≤ q * (j - u.val) := by
    have hr : 2 ≤ j - u.val := by omega
    nlinarith
  apply Fin.ext
  omega

theorem contractedParent_parentDistance {n : ℕ} (q j : ℕ) (hq : 0 < q) (hj : j < n)
    (u : Fin n) (hu : u.val + 2 ≤ j) (a : Fin q) :
    contractedParent q j hq hj (parentDistance q j hq u hu a) = u := by
  apply Fin.ext
  dsimp [contractedParent, parentDistance]
  have ha := a.isLt
  have hsum : q * j = q * u.val + q * (j - u.val) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hmul : q ≤ q * (j - u.val) := by
    have hr : 2 ≤ j - u.val := by omega
    nlinarith
  have he : q * j - (q * (j - u.val) - a.val) = q * u.val + a.val := by omega
  rw [he]
  exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

/-- Contracting `q` consecutive fine positions preserves the harmonic constant. -/
theorem contractedBucketLaw_weight_ge {n : ℕ} (roundUp : Bool) (q j B : ℕ)
    (hq : 0 < q) (hj : j < n) (hv : 2 ≤ q * j) (hB : 0 < B)
    (hcover : Nat.clog 2 (q * j) ≤ B) (u : Fin n) (hu : u.val + 2 ≤ j) :
    (1 : ℝ) / (2 * B * (j - u.val : ℕ)) ≤
      (contractedBucketLaw roundUp q j B hq hj hv hB).weight u := by
  let distances := univ.image (parentDistance q j hq u hu)
  have hcard : distances.card = q := by
    rw [card_image_of_injective _ (parentDistance_injective q j hq u hu), card_univ, Fintype.card_fin]
  have hprob := (bucketLaw roundUp (q * j) B hv hB).probability_ge_sum
    (fun r => contractedParent q j hq hj r = u) distances (by
      intro r hr
      obtain ⟨a, _, rfl⟩ := mem_image.mp hr
      exact contractedParent_parentDistance q j hq hj u hu a)
  have hlower : (∑ r ∈ distances, (1 : ℝ) / (2 * B * (q * (j - u.val) : ℕ))) ≤
      ∑ r ∈ distances, (bucketLaw roundUp (q * j) B hv hB).weight r := by
    apply sum_le_sum
    intro r hr
    obtain ⟨a, _, rfl⟩ := mem_image.mp hr
    apply le_trans _ (bucketLaw_weight_ge roundUp hv hB hcover _ (parentDistance_ge_two q j hq u hu a))
    apply one_div_le_one_div_of_le (by
      have := parentDistance_ge_two q j hq u hu a
      positivity)
    have hle : (parentDistance q j hq u hu a).val ≤ q * (j - u.val) := Nat.sub_le _ _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hrR : ((j - u.val : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show j - u.val ≠ 0 by omega)
  have hconstant : (∑ r ∈ distances, (1 : ℝ) / (2 * B * (q * (j - u.val) : ℕ))) =
      (1 : ℝ) / (2 * B * (j - u.val : ℕ)) := by
    rw [sum_const, nsmul_eq_mul, hcard, Nat.cast_mul]
    field_simp
  rw [hconstant] at hlower
  rw [← FiniteLaw.probability_singleton, contractedBucketLaw, FiniteLaw.probability_map]
  exact hlower.trans hprob

theorem bucketCount_real_bound {v N : ℕ} (hv : 2 ≤ v) (hvN : v ≤ N) :
    (Nat.clog 2 v : ℝ) ≤ 2 * Real.logb 2 N := by
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hlog : 1 ≤ Real.logb 2 v := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    simpa using (show (2 : ℝ) ≤ v by exact_mod_cast hv)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 v by linarith)
  have heq : Nat.ceil (Real.logb 2 (v : ℝ)) = Nat.clog 2 v := by
    simpa using Real.natCeil_logb_natCast 2 v
  rw [heq] at hceil
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmono : Real.logb 2 v ≤ Real.logb 2 N :=
    (Real.logb_le_logb (by norm_num) (by positivity) hN).mpr (by exact_mod_cast hvN)
  linarith

end ProofOfSpace.DRSample

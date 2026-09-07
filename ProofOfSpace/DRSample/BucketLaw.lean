import ProofOfSpace.DRSample.LawMap
import Mathlib.Data.Nat.Log

/-! # The bucket-distance distribution

The Boolean selects rounding up for DRSample and rounding down for Filecoin.
Buckets are indexed from one and their upper endpoint is capped at the source
metagraph position. Overlap of the last bucket is retained in the definition.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

def bucketUpper (v k : ℕ) : ℕ := min v (2 ^ k)
def bucketLower (roundUp : Bool) (v k : ℕ) : ℕ :=
  max 2 ((bucketUpper v k + if roundUp then 1 else 0) / 2)

def bucketDistances (roundUp : Bool) (v k : ℕ) : Finset (Fin (v + 1)) :=
  univ.filter fun r => bucketLower roundUp v k ≤ r.val ∧ r.val ≤ bucketUpper v k

theorem bucketUpper_ge_two {v k : ℕ} (hv : 2 ≤ v) (hk : 1 ≤ k) :
    2 ≤ bucketUpper v k := by
  apply le_min hv
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem bucketLower_le_upper (roundUp : Bool) {v k : ℕ} (hv : 2 ≤ v) (hk : 1 ≤ k) :
    bucketLower roundUp v k ≤ bucketUpper v k := by
  have hg := bucketUpper_ge_two hv hk
  unfold bucketLower
  apply max_le hg
  cases roundUp <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem bucketDistances_nonempty (roundUp : Bool) {v k : ℕ} (hv : 2 ≤ v) (hk : 1 ≤ k) :
    (bucketDistances roundUp v k).Nonempty := by
  refine ⟨⟨bucketUpper v k, ?_⟩, ?_⟩
  · have := min_le_left v (2 ^ k)
    unfold bucketUpper
    omega
  · exact mem_filter.mpr ⟨mem_univ _, bucketLower_le_upper roundUp hv hk, le_rfl⟩

theorem bucketDistances_card_le (roundUp : Bool) (v k : ℕ) :
    (bucketDistances roundUp v k).card ≤ bucketUpper v k := by
  have hsub : (bucketDistances roundUp v k).image Fin.val ⊆ Icc 1 (bucketUpper v k) := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
    have hh := (mem_filter.mp hq).2
    have h2 : 2 ≤ bucketLower roundUp v k := le_max_left _ _
    exact mem_Icc.mpr ⟨by omega, hh.2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at hc
  simpa using hc

noncomputable def bucketLaw (roundUp : Bool) (v B : ℕ) (hv : 2 ≤ v) (hB : 0 < B) :
    FiniteLaw (Fin (v + 1)) :=
  (FiniteLaw.uniformOn (univ : Finset (Fin B)) ⟨⟨0, hB⟩, mem_univ _⟩).bind fun k =>
    FiniteLaw.uniformOn (bucketDistances roundUp v (k.val + 1))
      (bucketDistances_nonempty roundUp hv (by omega))

theorem pow_clog_two_le_twice {r : ℕ} (hr : 2 ≤ r) : 2 ^ Nat.clog 2 r ≤ 2 * r := by
  have hk := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < r)
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < r)
  rw [Nat.pred_eq_sub_one] at hp
  have he : Nat.clog 2 r = (Nat.clog 2 r - 1) + 1 := by omega
  rw [he, pow_succ]
  nlinarith

/-- Every distance occurs in a bucket with at most twice that many choices. -/
theorem useful_bucket (roundUp : Bool) {v B r : ℕ} (hr : 2 ≤ r) (hrv : r ≤ v)
    (hB : Nat.clog 2 v ≤ B) :
    ∃ k : Fin B, (⟨r, by omega⟩ : Fin (v + 1)) ∈ bucketDistances roundUp v (k.val + 1) ∧
      (bucketDistances roundUp v (k.val + 1)).card ≤ 2 * r := by
  have hk0 := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < r)
  have hkB : Nat.clog 2 r ≤ B := (Nat.clog_mono_right 2 hrv).trans hB
  have he : Nat.clog 2 r - 1 + 1 = Nat.clog 2 r := by omega
  have hg0 : r ≤ bucketUpper v (Nat.clog 2 r) :=
    le_min hrv (Nat.le_pow_clog (by norm_num) r)
  have hg1 : bucketUpper v (Nat.clog 2 r) ≤ 2 * r :=
    (min_le_right _ _).trans (pow_clog_two_le_twice hr)
  refine ⟨⟨Nat.clog 2 r - 1, by omega⟩, ?_, ?_⟩
  · apply mem_filter.mpr
    simp only [he]
    refine ⟨mem_univ _, ?_, hg0⟩
    unfold bucketLower
    apply max_le hr
    cases roundUp <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · simp only [he]
    exact (bucketDistances_card_le _ _ _).trans hg1

/-- The exact finite bucket law has a harmonic pointwise lower bound. -/
theorem bucketLaw_weight_ge (roundUp : Bool) {v B : ℕ} (hv : 2 ≤ v) (hB : 0 < B)
    (hcover : Nat.clog 2 v ≤ B) (r : Fin (v + 1)) (hr : 2 ≤ r.val) :
    (1 : ℝ) / (2 * B * r.val) ≤ (bucketLaw roundUp v B hv hB).weight r := by
  obtain ⟨k, hmem, hcard⟩ := useful_bucket roundUp hr (by omega : r.val ≤ v) hcover
  have hcardpos := card_pos.mpr (bucketDistances_nonempty roundUp hv (show 1 ≤ k.val + 1 by omega))
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hrpos : (0 : ℝ) < r.val := by exact_mod_cast (show 0 < r.val by omega)
  have hcpos : (0 : ℝ) < (bucketDistances roundUp v (k.val + 1)).card := by exact_mod_cast hcardpos
  have hc : ((bucketDistances roundUp v (k.val + 1)).card : ℝ) ≤ 2 * r.val := by exact_mod_cast hcard
  have hbound := FiniteLaw.bind_weight_ge
    (FiniteLaw.uniformOn (univ : Finset (Fin B)) ⟨⟨0, hB⟩, mem_univ _⟩)
    (fun k => FiniteLaw.uniformOn (bucketDistances roundUp v (k.val + 1))
      (bucketDistances_nonempty roundUp hv (by omega))) k r
  change _ ≤ (bucketLaw roundUp v B hv hB).weight r at hbound
  simp only [FiniteLaw.uniformOn, mem_univ, ↓reduceIte, card_univ, Fintype.card_fin, hmem] at hbound
  apply le_trans _ hbound
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (mul_pos hBpos hcpos)
  nlinarith

end ProofOfSpace.DRSample

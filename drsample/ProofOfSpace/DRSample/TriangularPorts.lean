import ProofOfSpace.DRSample.TriangularGeometry
import ProofOfSpace.DRSample.MetaProbability

namespace ProofOfSpace.DRSample
open Finset Classical

def triangleOffsets (a k : ℕ) : Finset (Fin (10 * a)) := univ.filter fun p => k ≤ a + p.val

theorem triangleOffsets_card {a k : ℕ} (hk : k < 10 * a) :
    (triangleOffsets a k).card = 10 * a - (k - a) := by
  have hlo : k - a < 10 * a := by omega
  have he : triangleOffsets a k = Ici (⟨k - a, hlo⟩ : Fin (10 * a)) := by
    ext p
    simp only [triangleOffsets, mem_filter, mem_univ, true_and, mem_Ici]
    change k ≤ a + p.val ↔ k - a ≤ p.val
    omega
  rw [he, Fin.card_Ici]

theorem sum_range_sub_id (m a : ℕ) :
    ∑ k ∈ range (a + m), (k - a) = ∑ k ∈ range m, k := by
  rw [sum_range_add]
  have hz : ∑ k ∈ range a, (k - a) = 0 := sum_eq_zero fun k hk => by
    exact Nat.sub_eq_zero_of_le (mem_range.mp hk).le
  rw [hz, zero_add]
  apply sum_congr rfl
  intro k _
  omega

theorem triangleOffsets_mass {a : ℕ} (ha : 0 < a) :
    (119 / 800 : ℝ) * ((20 * a : ℕ) : ℝ) ^ 2 ≤
      ∑ k : Fin (10 * a), ((triangleOffsets a k).card : ℝ) := by
  have hs := sum_range_sub_id (9 * a) a
  rw [show a + 9 * a = 10 * a by omega] at hs
  have hsum : (∑ k : Fin (10 * a), (k.val - a)) * 2 = (9 * a) * (9 * a - 1) := by
    have he : (∑ k : Fin (10 * a), (k.val - a)) = ∑ k ∈ range (10 * a), (k - a) := by
      apply sum_bij (fun k _ => k.val)
      · intro k _; exact mem_range.mpr k.isLt
      · intro k _ l _ h; exact Fin.ext h
      · intro k hk; exact ⟨⟨k, mem_range.mp hk⟩, mem_univ _, rfl⟩
      · intros; rfl
    rw [he, hs, sum_range_id_mul_two]
  have hcast : (∑ k : Fin (10 * a), ((k.val - a : ℕ) : ℝ)) * 2 =
      (9 * (a : ℝ)) * (9 * a - 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) hsum
    push_cast at h
    rw [Nat.cast_sub (by omega : 1 ≤ 9 * a)] at h
    push_cast at h
    exact h
  have he : (∑ k : Fin (10 * a), ((triangleOffsets a k).card : ℝ)) =
      100 * (a : ℝ) ^ 2 - ∑ k : Fin (10 * a), ((k.val - a : ℕ) : ℝ) := by
    have hterm (k : Fin (10 * a)) : ((triangleOffsets a k).card : ℝ) =
        ((10 * a : ℕ) : ℝ) - ((k.val - a : ℕ) : ℝ) := by
      rw [triangleOffsets_card k.isLt, Nat.cast_sub (by omega : k.val - a ≤ 10 * a)]
    simp_rw [hterm]
    rw [sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he]
  push_cast
  nlinarith

def triangleSource {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (i : Fin M) (p : Fin (10 * a)) : Fin n :=
  ⟨t + i.val * (20 * a) + 10 * a + p.val, by
    have h := Nat.mul_le_mul_right (20 * a) (show i.val + 1 ≤ M from i.isLt)
    nlinarith [p.isLt]⟩

theorem triangleSource_injective {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) :
    Function.Injective (fun ip : Fin M × Fin (10 * a) => triangleSource hn ip.1 ip.2) := by
  intro x y he
  have hv := congrArg Fin.val he
  dsimp [triangleSource] at hv
  have hx := x.2.isLt
  have hy := y.2.isLt
  have hfirst : x.1 = y.1 := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := Nat.mul_le_mul_right (20 * a) (Nat.succ_le_iff.mpr h)
      nlinarith
    · have := Nat.mul_le_mul_right (20 * a) (Nat.succ_le_iff.mpr h)
      nlinarith
  have hsecond : x.2 = y.2 := by apply Fin.ext; rw [hfirst] at hv; omega
  exact Prod.ext hfirst hsecond

def trianglePorts {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (A : Finset (Fin M)) (k : ℕ) : Finset (Fin n) :=
  (A ×ˢ triangleOffsets a k).image fun ip => triangleSource hn ip.1 ip.2

theorem triangleSource_harmonic {n t a M j : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (i : Fin M) (hij : i.val + 2 ≤ j)
    (p : Fin (10 * a)) {k : ℕ} (hk : k < 10 * a) :
    (1 : ℝ) / (20 * a : ℕ) * harmonicAt M j i ≤
      harmonicAt n (t + j * (20 * a) + k) (triangleSource hn i p) := by
  have hmul := Nat.mul_le_mul_right (20 * a) hij
  have hp := p.isLt
  have hbefore : (triangleSource hn i p).val < t + j * (20 * a) + k := by
    dsimp [triangleSource]
    nlinarith
  have hd : t + j * (20 * a) + k - (triangleSource hn i p).val ≤
      (20 * a) * (j - i.val) := by
    have he : j - i.val + i.val = j := by omega
    have hmul : (20 * a) * (j - i.val) + i.val * (20 * a) = j * (20 * a) := by nlinarith
    dsimp [triangleSource]
    omega
  unfold harmonicAt
  rw [if_pos (show i.val < j by omega), if_pos hbefore, div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le
    (by exact_mod_cast (show 0 < t + j * (20 * a) + k - (triangleSource hn i p).val by omega))
  exact_mod_cast hd

theorem trianglePorts_harmonic {n t a M j : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (A : Finset (Fin M))
    (hA : ∀ i ∈ A, i.val + 2 ≤ j) {k : ℕ} (hk : k < 10 * a) :
    ((triangleOffsets a k).card : ℝ) / (20 * a : ℕ) * (∑ i ∈ A, harmonicAt M j i) ≤
      ∑ u ∈ trianglePorts hn A k, harmonicAt n (t + j * (20 * a) + k) u := by
  rw [trianglePorts, sum_image (fun x _ y _ he => triangleSource_injective ha hn he), sum_product]
  calc
    _ = ∑ i ∈ A, ∑ p ∈ triangleOffsets a k,
        (1 : ℝ) / (20 * a : ℕ) * harmonicAt M j i := by
      simp only [sum_const, nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← mul_sum]
      ring
    _ ≤ _ := sum_le_sum fun i hi => sum_le_sum fun p _ =>
      triangleSource_harmonic ha hn i (hA i hi) p hk

end ProofOfSpace.DRSample

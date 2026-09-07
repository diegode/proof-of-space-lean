import ProofOfSpace.DRSample.MetaLift
import ProofOfSpace.DRSample.Sequential

/-! # Harmonic mass between the first and last thirds of blocks -/
namespace ProofOfSpace.DRSample
open Finset Classical

def outgoingVertex {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (i : Fin M) (a : Fin (m / 3)) : Fin n :=
  ⟨i.val * m + (m - m / 3) + a.val, by
    have hi : i.val + 1 ≤ M := by omega
    have hmul := Nat.mul_le_mul_right m hi
    have ha := a.isLt
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega⟩

theorem outgoingVertex_bounds {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (i : Fin M) (a : Fin (m / 3)) :
    i.val * m ≤ (outgoingVertex hm hn i a).val ∧
      (outgoingVertex hm hn i a).val < (i.val + 1) * m := by
  have ha := a.isLt
  dsimp [outgoingVertex]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem outgoingVertex_injective {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n) :
    Function.Injective (fun p : Fin M × Fin (m / 3) => outgoingVertex hm hn p.1 p.2) := by
  intro x y heq
  have hx := outgoingVertex_bounds hm hn x.1 x.2
  have hy := outgoingVertex_bounds hm hn y.1 y.2
  have hval := congrArg Fin.val heq
  have hix : (outgoingVertex hm hn x.1 x.2).val / m = x.1.val :=
    Nat.div_eq_of_lt_le (by nlinarith [hx.2]) (by nlinarith [hx.1])
  have hiy : (outgoingVertex hm hn y.1 y.2).val / m = y.1.val :=
    Nat.div_eq_of_lt_le (by nlinarith [hy.2]) (by nlinarith [hy.1])
  have hfirst : x.1 = y.1 := Fin.ext (by rw [hval, hiy] at hix; exact hix.symm)
  have hsecond : x.2 = y.2 := by
    apply Fin.ext
    dsimp [outgoingVertex] at hval
    rw [hfirst] at hval
    omega
  exact Prod.ext hfirst hsecond

def outgoingPorts {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (A : Finset (Fin M)) : Finset (Fin n) :=
  (A ×ˢ univ).image fun p => outgoingVertex hm hn p.1 p.2

theorem port_distance {m i j u v : ℕ} (hm : 3 ≤ m) (hij : i + 2 ≤ j)
    (hu0 : i * m ≤ u) (hu1 : u < (i + 1) * m)
    (hv0 : j * m ≤ v) (hv1 : v < (j + 1) * m) :
    2 ≤ v - u ∧ v - u ≤ 2 * m * (j - i) := by
  have hgap : (i + 2) * m ≤ j * m := Nat.mul_le_mul_right m hij
  have huv : u + 2 ≤ v := by nlinarith
  have hsub : j - i + i = j := by omega
  have hmul : m * (j - i) + i * m = j * m := by nlinarith
  have hdiff : v - u + u = v := by omega
  have hr : 1 ≤ j - i := by omega
  constructor
  · omega
  · nlinarith

theorem harmonicAt_outgoing_ge {n m M j : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (i : Fin M) (hij : i.val + 2 ≤ j) (a : Fin (m / 3))
    (k : Fin m) :
    (1 : ℝ) / (2 * m) * harmonicAt M j i ≤
      harmonicAt n (j * m + k.val) (outgoingVertex hm hn i a) := by
  have hk := k.isLt
  have hu := outgoingVertex_bounds hm hn i a
  have hd := port_distance hm hij hu.1 hu.2 (Nat.le_add_right _ _)
    (show j * m + k.val < (j + 1) * m by nlinarith)
  unfold harmonicAt
  rw [if_pos (show i.val < j by omega), if_pos (show (outgoingVertex hm hn i a).val < j * m + k.val by omega)]
  rw [div_mul_div_comm, one_mul]
  have hp : (0 : ℝ) < (j * m + k.val - (outgoingVertex hm hn i a).val : ℕ) := by
    exact_mod_cast (show 0 < j * m + k.val - (outgoingVertex hm hn i a).val by omega)
  apply one_div_le_one_div_of_le hp
  exact_mod_cast hd.2

theorem outgoingPorts_harmonic_ge {n m M j : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (A : Finset (Fin M)) (hA : ∀ i ∈ A, i.val + 2 ≤ j) (k : Fin m) :
    ((m / 3 : ℕ) : ℝ) / (2 * m) * (∑ i ∈ A, harmonicAt M j i) ≤
      ∑ u ∈ outgoingPorts hm hn A, harmonicAt n (j * m + k.val) u := by
  rw [outgoingPorts, sum_image (fun x _ y _ he => outgoingVertex_injective hm hn he), sum_product]
  calc ((m / 3 : ℕ) : ℝ) / (2 * m) * (∑ i ∈ A, harmonicAt M j i)
      = ∑ i ∈ A, ∑ a : Fin (m / 3), (1 : ℝ) / (2 * m) * harmonicAt M j i := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp_rw [← mul_assoc]
        rw [← mul_sum]
        ring
    _ ≤ ∑ i ∈ A, ∑ a : Fin (m / 3), harmonicAt n (j * m + k.val) (outgoingVertex hm hn i a) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro a _
      exact harmonicAt_outgoing_ge hm hn i (hA i hi) a k

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.TriangularPorts
import ProofOfSpace.DRSample.MultiscaleSharp

namespace ProofOfSpace.DRSample
open Finset Classical

def triangleParents {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (j : ℕ) (row : Fin (20 * a) → Finset (Fin n)) : Finset (Fin M) :=
  univ.filter fun i => i.val < j ∧ (i.val + 1 = j ∨
    ∃ k : Fin (20 * a), k.val < 10 * a ∧
      ∃ p ∈ triangleOffsets a k.val, triangleSource hn i p ∈ row k)

noncomputable def triangleRowLaw {n : ℕ} (t a : ℕ)
    (p : ℕ → FiniteLaw (Finset (Fin n))) (j : ℕ) :
    FiniteLaw (Fin (20 * a) → Finset (Fin n)) :=
  FiniteLaw.pi fun k => p (t + j * (20 * a) + k.val)

theorem sum_if_fin_lt {m l : ℕ} (hl : l ≤ m) (f : ℕ → ℝ) :
    (∑ k : Fin m, if k.val < l then f k.val else 0) = ∑ k : Fin l, f k.val := by
  rw [sum_fin_nat m (fun k => if k < l then f k else 0), ← sum_filter]
  have he : (range m).filter (· < l) = range l := by ext k; simp; omega
  rw [he, sum_fin_nat]

theorem triangle_disjoint {n t a M j : ℕ} (hn : t + M * (20 * a) ≤ n)
    (A : Finset (Fin M)) (row : Fin (20 * a) → Finset (Fin n))
    (h : Disjoint (triangleParents hn j row) A) (k : Fin (20 * a)) (hk : k.val < 10 * a) :
    Disjoint (row k) (trianglePorts hn (A.filter fun i => i.val < j) k.val) := by
  apply disjoint_left.mpr
  intro u hu hp
  obtain ⟨⟨i, p⟩, hip, he⟩ := mem_image.mp hp
  obtain ⟨hi, hp⟩ := mem_product.mp hip
  obtain ⟨hiA, hij⟩ := mem_filter.mp hi
  apply (disjoint_left.mp h) _ hiA
  exact mem_filter.mpr ⟨mem_univ _, hij, Or.inr ⟨k, hk, p, hp, he ▸ hu⟩⟩

theorem triangleParents_avoidance {n t a M j : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (hj : j < M)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta : ℝ} (heta : 0 ≤ eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) (A : Finset (Fin M)) :
    (triangleRowLaw t a p j).probability (fun row => Disjoint (triangleParents hn j row) A) ≤
      Real.exp (-(eta * (119 / 800 : ℝ) * (20 * a : ℕ)) * ∑ i ∈ A, harmonicAt M j i) := by
  by_cases hpred : ∃ i ∈ A, i.val + 1 = j
  · obtain ⟨i, hi, hij⟩ := hpred
    have hnone : ∀ row, ¬ Disjoint (triangleParents hn j row) A := by
      intro row h
      exact (disjoint_left.mp h) (mem_filter.mpr ⟨mem_univ _, by omega, Or.inl hij⟩) hi
    have hz : (triangleRowLaw t a p j).probability
        (fun row => Disjoint (triangleParents hn j row) A) = 0 := by
      simp [FiniteLaw.probability, hnone]
    rw [hz]
    exact (Real.exp_pos _).le
  · have hA : ∀ i ∈ A.filter (fun i => i.val < j), i.val + 2 ≤ j := by
      intro i hi
      obtain ⟨hiA, hij⟩ := mem_filter.mp hi
      have hne : i.val + 1 ≠ j := fun h => hpred ⟨i, hiA, h⟩
      omega
    let w := ∑ i ∈ A, harmonicAt M j i
    have hw : 0 ≤ w := sum_nonneg fun i _ => by unfold harmonicAt; positivity
    have hstep (k : Fin (20 * a)) :
        (p (t + j * (20 * a) + k.val)).probability (fun parents => k.val < 10 * a →
          Disjoint parents (trianglePorts hn (A.filter fun i => i.val < j) k.val)) ≤
        Real.exp (if k.val < 10 * a then
          -(eta * (triangleOffsets a k.val).card / (20 * a : ℕ)) * w else 0) := by
      by_cases hk : k.val < 10 * a
      · simp only [hk, true_implies, ↓reduceIte]
        have hvn : t + j * (20 * a) + k.val < n := by
          have hmul := Nat.mul_le_mul_right (20 * a) (Nat.succ_le_iff.mpr hj)
          nlinarith [k.isLt]
        apply (havoid _ hvn _).trans
        apply Real.exp_le_exp.mpr
        have hgeo := trianglePorts_harmonic ha hn _ hA hk
        rw [harmonicAt_filter_earlier] at hgeo
        have h := mul_le_mul_of_nonpos_left hgeo (neg_nonpos.mpr heta)
        convert h using 1 <;> first | ring | rfl
      · simp [hk]
    have hmono := (triangleRowLaw t a p j).probability_mono (fun row h k hk =>
      triangle_disjoint (j := j) hn A row h k hk)
    apply hmono.trans
    rw [triangleRowLaw, FiniteLaw.probability_pi
      (fun k : Fin (20 * a) => p (t + j * (20 * a) + k.val))
      (fun k parents => k.val < 10 * a →
        Disjoint parents (trianglePorts hn (A.filter fun i => i.val < j) k.val))]
    apply (prod_le_prod (fun _ _ => FiniteLaw.probability_nonneg _ _)
      (fun k _ => hstep k)).trans
    rw [← Real.exp_sum, sum_if_fin_lt (by omega : 10 * a ≤ 20 * a)
      (fun k => -(eta * (triangleOffsets a k).card / (20 * a : ℕ)) * w)]
    apply Real.exp_le_exp.mpr
    have hsum : (∑ k : Fin (10 * a),
        -(eta * (triangleOffsets a k.val).card / (20 * a : ℕ)) * w) =
        -(eta * (∑ k : Fin (10 * a), ((triangleOffsets a k.val).card : ℝ)) /
          (20 * a : ℕ)) * w := by
      simp only [neg_mul, ← sum_neg_distrib, ← sum_mul, ← sum_div, ← mul_sum,
        ← neg_div]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right _ hw
    apply neg_le_neg
    have hB : (0 : ℝ) < (20 * a : ℕ) := by positivity
    apply (le_div_iff₀ hB).mpr
    have h := mul_le_mul_of_nonneg_left (triangleOffsets_mass ha) heta
    nlinarith

end ProofOfSpace.DRSample

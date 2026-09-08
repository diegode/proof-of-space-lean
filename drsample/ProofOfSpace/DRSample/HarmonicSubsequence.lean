import ProofOfSpace.DRSample.Pivot
import ProofOfSpace.DRSample.Retention

/-! # The harmonic increasing-subsequence inequality -/
namespace ProofOfSpace.DRSample
open Finset Classical

private theorem sum_left_reverse (lo j : ℕ) (hlo : lo ≤ j) (f : ℕ → ℝ) :
    ∑ i ∈ Ico lo j, f i = ∑ k ∈ range (j - lo), f (j - (k + 1)) := by
  refine sum_bij (fun i _ => j - (i + 1)) ?_ ?_ ?_ ?_
  · intro i hi
    have := mem_Ico.mp hi
    apply mem_range.mpr
    omega
  · intro i hi k hk heq
    have := mem_Ico.mp hi
    have := mem_Ico.mp hk
    omega
  · intro k hk
    have := mem_range.mp hk
    refine ⟨j - (k + 1), mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hi
    have := mem_Ico.mp hi
    congr 1
    omega

private theorem sum_right_shift (j hi : ℕ) (hj : j < hi) (f : ℕ → ℝ) :
    ∑ i ∈ Ico (j + 1) hi, f i = ∑ k ∈ range (hi - j - 1), f (j + k + 1) := by
  refine sum_bij (fun i _ => i - j - 1) ?_ ?_ ?_ ?_
  · intro i hiI
    have := mem_Ico.mp hiI
    apply mem_range.mpr
    omega
  · intro i hiI k hk heq
    have := mem_Ico.mp hiI
    have := mem_Ico.mp hk
    omega
  · intro k hk
    have := mem_range.mp hk
    refine ⟨j + k + 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hiI
    have := mem_Ico.mp hiI
    congr 1
    omega

def badLeft (a : ℕ → ℝ) (j k : ℕ) : Prop := a j ≤ a (j - (k + 1))
def badRight (a : ℕ → ℝ) (j k : ℕ) : Prop := a (j + k + 1) ≤ a j

noncomputable def harmonicWeight (a : ℕ → ℝ) (lo hi j : ℕ) : ℝ :=
  retention (badLeft a j) (j - lo) * retention (badRight a j) (hi - j - 1)

private theorem left_pivots (a : ℕ → ℝ) {lo hi j : ℕ} (hj : j ∈ Ico lo hi) :
    (∑ i ∈ Ico lo hi, if i < j ∧ a i < a j then harmonicWeight a (i + 1) hi j else 0) =
      retention (badRight a j) (hi - j - 1) *
        ∑ k ∈ range (j - lo), if badLeft a j k then 0 else retention (badLeft a j) k := by
  have hjlo := (mem_Ico.mp hj).1
  have hjhi := (mem_Ico.mp hj).2
  have hsub : Ico lo j ⊆ Ico lo hi := by
    intro i hiI
    exact mem_Ico.mpr ⟨(mem_Ico.mp hiI).1, (mem_Ico.mp hiI).2.trans hjhi⟩
  calc (∑ i ∈ Ico lo hi, if i < j ∧ a i < a j then harmonicWeight a (i + 1) hi j else 0)
      = ∑ i ∈ Ico lo j, if i < j ∧ a i < a j then harmonicWeight a (i + 1) hi j else 0 := by
        symm
        apply sum_subset hsub
        intro i hiI hin
        have hnot : ¬i < j := by
          intro hij
          exact hin (mem_Ico.mpr ⟨(mem_Ico.mp hiI).1, hij⟩)
        simp [hnot]
    _ = ∑ i ∈ Ico lo j, if a i < a j then harmonicWeight a (i + 1) hi j else 0 := by
      apply sum_congr rfl
      intro i hiI
      simp [(mem_Ico.mp hiI).2]
    _ = ∑ k ∈ range (j - lo), if a (j - (k + 1)) < a j then
        harmonicWeight a (j - (k + 1) + 1) hi j else 0 := sum_left_reverse lo j hjlo _
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      have hlen : j - (j - (k + 1) + 1) = k := by omega
      by_cases hbad : badLeft a j k
      · have hnot : ¬ a (j - (k + 1)) < a j := not_lt.mpr hbad
        simp [hbad, hnot]
      · have hgood : a (j - (k + 1)) < a j := lt_of_not_ge hbad
        simp [hbad, hgood, harmonicWeight, hlen, mul_comm]

private theorem right_pivots (a : ℕ → ℝ) {lo hi j : ℕ} (hj : j ∈ Ico lo hi) :
    (∑ i ∈ Ico lo hi, if j < i ∧ a j < a i then harmonicWeight a lo i j else 0) =
      retention (badLeft a j) (j - lo) *
        ∑ k ∈ range (hi - j - 1), if badRight a j k then 0 else retention (badRight a j) k := by
  have hjlo := (mem_Ico.mp hj).1
  have hjhi := (mem_Ico.mp hj).2
  have hsub : Ico (j + 1) hi ⊆ Ico lo hi := by
    intro i hiI
    have hi' := mem_Ico.mp hiI
    exact mem_Ico.mpr ⟨by omega, hi'.2⟩
  calc (∑ i ∈ Ico lo hi, if j < i ∧ a j < a i then harmonicWeight a lo i j else 0)
      = ∑ i ∈ Ico (j + 1) hi, if j < i ∧ a j < a i then harmonicWeight a lo i j else 0 := by
        symm
        apply sum_subset hsub
        intro i hiI hin
        have hnot : ¬j < i := by
          intro hij
          exact hin (mem_Ico.mpr ⟨by omega, (mem_Ico.mp hiI).2⟩)
        simp [hnot]
    _ = ∑ i ∈ Ico (j + 1) hi, if a j < a i then harmonicWeight a lo i j else 0 := by
      apply sum_congr rfl
      intro i hiI
      have hij : j < i := by have := (mem_Ico.mp hiI).1; omega
      simp [hij]
    _ = ∑ k ∈ range (hi - j - 1), if a j < a (j + k + 1) then
        harmonicWeight a lo (j + k + 1) j else 0 := sum_right_shift j hi hjhi _
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      have hlen : j + k + 1 - j - 1 = k := by omega
      by_cases hbad : badRight a j k
      · have hnot : ¬ a j < a (j + k + 1) := not_lt.mpr hbad
        simp [hbad, hnot]
      · have hgood : a j < a (j + k + 1) := lt_of_not_ge hbad
        simp [hbad, hgood, harmonicWeight, hlen]

/-- The binary-pivot recurrence for harmonic weights. -/
theorem harmonicWeight_pivot (a : ℕ → ℝ) (lo hi j : ℕ) (hj : j ∈ Ico lo hi) :
    (hi - lo : ℕ) * harmonicWeight a lo hi j ≤
      ∑ i ∈ Ico lo hi, pivotContribution a (harmonicWeight a) lo hi i j := by
  have hjlo := (mem_Ico.mp hj).1
  have hjhi := (mem_Ico.mp hj).2
  simp only [pivotContribution, sum_add_distrib]
  rw [show (∑ i ∈ Ico lo hi, if i = j then (1 : ℝ) else 0) = 1 by simp [hj],
    left_pivots a hj, right_pivots a hj]
  have hlen : hi - lo = (j - lo) + (hi - j - 1) + 1 := by omega
  rw [hlen]
  push_cast
  simpa only [harmonicWeight, add_comm, add_left_comm, add_assoc] using
    retention_pivot_bound (badLeft a j) (badRight a j) (j - lo) (hi - j - 1)

/-- Harmonic weights sum to at most the length of a longest increasing subsequence. -/
theorem sum_harmonicWeight_le_capacity (a : ℕ → ℝ) (lo hi : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Ico lo hi) :
    ∑ j ∈ T, harmonicWeight a lo hi j ≤ increasingCapacity a T :=
  increasingCapacity_of_pivot a (harmonicWeight a) (harmonicWeight_pivot a) lo hi T hT


/-- Reciprocal-distance mass of inconsistent comparisons at one index. -/
noncomputable def inconsistentCost (a : ℕ → ℝ) (lo hi j : ℕ) : ℝ :=
  (∑ i ∈ Ico lo j, if a j ≤ a i then (1 : ℝ) / (j - i : ℕ) else 0) +
  (∑ i ∈ Ico (j + 1) hi, if a i ≤ a j then (1 : ℝ) / (i - j : ℕ) else 0)

theorem harmonicWeight_eq_exp (a : ℕ → ℝ) {lo hi j : ℕ} (hj : j ∈ Ico lo hi) :
    harmonicWeight a lo hi j = Real.exp (-inconsistentCost a lo hi j) := by
  have hjlo := (mem_Ico.mp hj).1
  have hjhi := (mem_Ico.mp hj).2
  have hleft : (∑ i ∈ Ico lo j, if a j ≤ a i then (1 : ℝ) / (j - i : ℕ) else 0) =
      ∑ k ∈ range (j - lo), if badLeft a j k then (1 : ℝ) / (k + 1) else 0 := by
    rw [sum_left_reverse lo j hjlo]
    apply sum_congr rfl
    intro k hk
    have := mem_range.mp hk
    have hdiff : j - (j - (k + 1)) = k + 1 := by omega
    simp only [badLeft, hdiff, Nat.cast_add, Nat.cast_one]
    split_ifs with hcond <;> simp_all [badLeft, badRight]
  have hright : (∑ i ∈ Ico (j + 1) hi, if a i ≤ a j then (1 : ℝ) / (i - j : ℕ) else 0) =
      ∑ k ∈ range (hi - j - 1), if badRight a j k then (1 : ℝ) / (k + 1) else 0 := by
    rw [sum_right_shift j hi hjhi]
    apply sum_congr rfl
    intro k hk
    have hdiff : j + k + 1 - j = k + 1 := by omega
    simp only [badRight, hdiff, Nat.cast_add, Nat.cast_one]
    split_ifs with hcond <;> simp_all [badLeft, badRight]
  simp only [harmonicWeight, retention, inconsistentCost, hleft, hright, ← Real.exp_add, neg_add]

/-- The deterministic inequality proved using the auxiliary binary search tree
in the working note, here obtained by finite pivot averaging. -/
theorem sum_exp_inconsistentCost_le_capacity (a : ℕ → ℝ) (lo hi : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Ico lo hi) :
    ∑ j ∈ T, Real.exp (-inconsistentCost a lo hi j) ≤ increasingCapacity a T := by
  convert sum_harmonicWeight_le_capacity a lo hi T hT using 1
  apply sum_congr rfl
  intro j hj
  exact (harmonicWeight_eq_exp a (hT hj)).symm

end ProofOfSpace.DRSample

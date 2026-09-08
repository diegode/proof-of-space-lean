import ProofOfSpace.DRSample.Increasing

/-! # Binary-pivot averaging for increasing subsequences -/
namespace ProofOfSpace.DRSample
open Finset Classical

noncomputable def pivotContribution (a : ℕ → ℝ) (w : ℕ → ℕ → ℕ → ℝ)
    (lo hi i j : ℕ) : ℝ :=
  (if i = j then 1 else 0) +
  (if j < i ∧ a j < a i then w lo i j else 0) +
  (if i < j ∧ a i < a j then w (i + 1) hi j else 0)

/-- Any weights satisfying the pivot recurrence give a lower bound on the
maximum size of a strictly increasing subsequence. -/
theorem increasingCapacity_of_pivot (a : ℕ → ℝ) (w : ℕ → ℕ → ℕ → ℝ)
    (hpivot : ∀ lo hi j, j ∈ Ico lo hi →
      (hi - lo : ℕ) * w lo hi j ≤ ∑ i ∈ Ico lo hi, pivotContribution a w lo hi i j)
    (lo hi : ℕ) (T : Finset ℕ) (hT : T ⊆ Ico lo hi) :
    ∑ j ∈ T, w lo hi j ≤ (increasingCapacity a T : ℝ) := by
  generalize hN : hi - lo = N
  induction N using Nat.strong_induction_on generalizing lo hi T with
  | h N ih =>
    by_cases hlt : lo < hi
    · have hreward (i : ℕ) (hiI : i ∈ Ico lo hi) :
          ∑ j ∈ T, pivotContribution a w lo hi i j ≤ (increasingCapacity a T : ℝ) := by
        have hilo := (mem_Ico.mp hiI).1
        have hihi := (mem_Ico.mp hiI).2
        let Tl := T.filter fun j => j < i ∧ a j < a i
        let Tr := T.filter fun j => i < j ∧ a i < a j
        have hTl : Tl ⊆ Ico lo i := by
          intro j hj
          have hj' := mem_filter.mp hj
          exact mem_Ico.mpr ⟨(mem_Ico.mp (hT hj'.1)).1, hj'.2.1⟩
        have hTr : Tr ⊆ Ico (i + 1) hi := by
          intro j hj
          have hj' := mem_filter.mp hj
          exact mem_Ico.mpr ⟨by omega, (mem_Ico.mp (hT hj'.1)).2⟩
        have hl : ∑ j ∈ Tl, w lo i j ≤ (increasingCapacity a Tl : ℝ) :=
          ih (i - lo) (by omega) lo i Tl hTl rfl
        have hr : ∑ j ∈ Tr, w (i + 1) hi j ≤ (increasingCapacity a Tr : ℝ) :=
          ih (hi - (i + 1)) (by omega) (i + 1) hi Tr hTr rfl
        have hc := increasingCapacity_pivot a T i
        have hcR : (increasingCapacity a Tl : ℝ) + increasingCapacity a Tr +
            (if i ∈ T then 1 else 0) ≤ increasingCapacity a T := by
          exact_mod_cast hc
        simp only [pivotContribution, sum_add_distrib]
        have heq : (∑ j ∈ T, if i = j then (1 : ℝ) else 0) = if i ∈ T then 1 else 0 := by
          simp
        rw [heq]
        have hleft : (∑ j ∈ T, if j < i ∧ a j < a i then w lo i j else 0) =
            ∑ j ∈ Tl, w lo i j := (sum_filter _ _).symm
        have hright : (∑ j ∈ T, if i < j ∧ a i < a j then w (i + 1) hi j else 0) =
            ∑ j ∈ Tr, w (i + 1) hi j := (sum_filter _ _).symm
        rw [hleft, hright]
        linarith
      have hsum : (hi - lo : ℕ) * (∑ j ∈ T, w lo hi j) ≤
          (hi - lo : ℕ) * (increasingCapacity a T : ℝ) := by
        calc (hi - lo : ℕ) * (∑ j ∈ T, w lo hi j)
            = ∑ j ∈ T, (hi - lo : ℕ) * w lo hi j := mul_sum _ _ _
          _ ≤ ∑ j ∈ T, ∑ i ∈ Ico lo hi, pivotContribution a w lo hi i j :=
            sum_le_sum fun j hj => hpivot lo hi j (hT hj)
          _ = ∑ i ∈ Ico lo hi, ∑ j ∈ T, pivotContribution a w lo hi i j := sum_comm
          _ ≤ ∑ i ∈ Ico lo hi, (increasingCapacity a T : ℝ) := sum_le_sum hreward
          _ = (hi - lo : ℕ) * (increasingCapacity a T : ℝ) := by simp
      exact (mul_le_mul_iff_right₀ (by exact_mod_cast Nat.sub_pos_of_lt hlt)).mp hsum
    · have he : T = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro j hj
        have := mem_Ico.mp (hT hj)
        omega
      simp [he, increasingCapacity, Increasing]

end ProofOfSpace.DRSample

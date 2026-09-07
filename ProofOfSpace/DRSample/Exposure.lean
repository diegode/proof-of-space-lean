import ProofOfSpace.DRSample.Moment

/-! # One exposed destination

Earlier depth labels are arbitrary fixed data. Avoidance of deterministic sets
controls the forbidden mass evaluated at the actual new depth label.
-/
namespace ProofOfSpace.DRSample
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual depth recurrence for a surviving newly exposed destination. -/
def nextHeight (h : ι → ℕ) (parents : Finset ι) : ℕ := parents.sup h + 1

/-- Predecessors forbidden by a proposed upper bound on the new height. -/
def highPredecessors (h : ι → ℕ) (k : ℕ) : Finset ι :=
  univ.filter fun i => k ≤ h i

noncomputable def newForbiddenMass (h : ι → ℕ) (w : ι → ℝ) (parents : Finset ι) : ℝ :=
  ∑ i ∈ highPredecessors h (nextHeight h parents), w i

theorem nextHeight_pos (h : ι → ℕ) (parents : Finset ι) : 0 < nextHeight h parents := by
  simp [nextHeight]

theorem nextHeight_le_iff_disjoint (h : ι → ℕ) (parents : Finset ι)
    {k : ℕ} (hk : 0 < k) :
    nextHeight h parents ≤ k ↔ Disjoint parents (highPredecessors h k) := by
  rw [disjoint_left]
  constructor
  · intro hh i hi hhigh
    have hle := Finset.le_sup (f := h) hi
    have hge : k ≤ h i := (mem_filter.mp hhigh).2
    unfold nextHeight at hh
    omega
  · intro hd
    have hh : parents.sup h ≤ k - 1 := by
      apply Finset.sup_le
      intro i hi
      have hnot : ¬ k ≤ h i := by
        intro hge
        exact hd hi (mem_filter.mpr ⟨mem_univ _, hge⟩)
      omega
    unfold nextHeight
    omega

/-- A single destination's avoidance bound transfers to the random forbidden
mass at its actual height. No independence among edges to that destination is used. -/
theorem newForbiddenMass_tail (p : FiniteLaw (Finset ι)) (h : ι → ℕ) (w : ι → ℝ)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ A : Finset ι, p.probability (fun parents => Disjoint parents A) ≤
      Real.exp (-lambda * ∑ i ∈ A, w i)) (x : ℝ) :
    p.probability (fun parents => x ≤ newForbiddenMass h w parents) ≤ Real.exp (-lambda * x) := by
  classical
  let bad := univ.filter fun parents : Finset ι => x ≤ newForbiddenMass h w parents
  rcases bad.eq_empty_or_nonempty with hempty | hne
  · have hnone : ∀ parents, ¬ x ≤ newForbiddenMass h w parents := by
      intro parents hp
      have : parents ∈ bad := mem_filter.mpr ⟨mem_univ _, hp⟩
      simpa [hempty] using this
    simp only [FiniteLaw.probability, if_neg (hnone _), sum_const_zero]
    exact (Real.exp_pos _).le
  · obtain ⟨parents₀, hp₀, hmax⟩ := bad.exists_max_image (nextHeight h) hne
    have hmass : x ≤ newForbiddenMass h w parents₀ := (mem_filter.mp hp₀).2
    calc p.probability (fun parents => x ≤ newForbiddenMass h w parents)
        ≤ p.probability (fun parents =>
          Disjoint parents (highPredecessors h (nextHeight h parents₀))) := by
            apply p.probability_mono
            intro parents hp
            apply (nextHeight_le_iff_disjoint h parents (nextHeight_pos h parents₀)).mp
            exact hmax parents (mem_filter.mpr ⟨mem_univ _, hp⟩)
      _ ≤ Real.exp (-lambda * ∑ i ∈ highPredecessors h (nextHeight h parents₀), w i) :=
        havoid _
      _ ≤ Real.exp (-lambda * x) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hmass (neg_nonpos.mpr hlambda.le)

/-- The conditional exponential-moment estimate, with earlier labels fixed. -/
theorem newForbiddenMass_moment (p : FiniteLaw (Finset ι)) (h : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ A : Finset ι, p.probability (fun parents => Disjoint parents A) ≤
      Real.exp (-lambda * ∑ i ∈ A, w i)) :
    p.expectation (fun parents => Real.exp (lambda / 2 * newForbiddenMass h w parents)) ≤ 2 := by
  apply p.expectation_exp_le_two_of_tail _ lambda hlambda
  · intro parents
    exact sum_nonneg fun i _ => hw i
  · intro x _
    exact newForbiddenMass_tail p h w hlambda havoid x

end ProofOfSpace.DRSample

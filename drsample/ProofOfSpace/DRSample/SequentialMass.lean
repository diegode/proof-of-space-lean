import ProofOfSpace.DRSample.Sequential

/-! # The exposed increments sum to the actual forbidden mass -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem sum_fin_nat (M : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin M, f i.val) = ∑ i ∈ range M, f i := by
  apply sum_bij (fun i _ => i.val)
  · intro i _
    exact mem_range.mpr i.isLt
  · intro i _ j _ he
    exact Fin.ext he
  · intro i hi
    exact ⟨⟨i, mem_range.mp hi⟩, mem_univ _, rfl⟩
  · intros; rfl

theorem forbiddenMass_congr (U : Finset ℕ) {h h' : ℕ → ℕ}
    (hh : ∀ i ∈ U, h i = h' i) : forbiddenMass U h = forbiddenMass U h' := by
  unfold forbiddenMass
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro i hi
  simp only [pairMass, hh i hi, hh j hj]

theorem forbiddenMass_insert {U : Finset ℕ} {n : ℕ} (hU : U ⊆ range n)
    (h : ℕ → ℕ) :
    forbiddenMass (insert n U) h = forbiddenMass U h + ∑ i ∈ U, pairMass h i n := by
  have hnU : n ∉ U := fun hn => (lt_irrefl n) (mem_range.mp (hU hn))
  unfold forbiddenMass
  rw [sum_insert hnU, sum_insert hnU]
  have hself : pairMass h n n = 0 := by simp [pairMass]
  have hback : ∀ j ∈ U, pairMass h n j = 0 := by
    intro j hj
    have hjn := mem_range.mp (hU hj)
    simp [pairMass, show ¬ n < j by omega]
  simp only [hself, zero_add]
  have heq : (∑ j ∈ U, ∑ i ∈ insert n U, pairMass h i j) =
      ∑ j ∈ U, ∑ i ∈ U, pairMass h i j := by
    apply sum_congr rfl
    intro j hj
    rw [sum_insert hnU, hback j hj, zero_add]
  rw [heq, add_comm]

theorem exposedIncrement_eq_sum {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) (n + 1)) (hn : n < M) (hnS : n ∉ S) :
    exposedIncrement S n s =
      ∑ i ∈ range n \ S, pairMass (exposedLabels S (n + 1) s) i n := by
  have hnew : exposedLabels S (n + 1) s n =
      nextHeight (fun i : Fin M => exposedLabels S n s.1 i.val) s.2 := by
    simp [exposedLabels, hnS]
  have hnewpos : 0 < exposedLabels S (n + 1) s n :=
    exposedLabels_positive S s (by omega) hnS
  have hnot : ¬(n ∈ S ∨ M ≤ n) := not_or_intro hnS (Nat.not_le.mpr hn)
  rw [exposedIncrement, if_neg hnot, newForbiddenMass, highPredecessors, sum_filter]
  unfold harmonicAt
  let f := fun i => if nextHeight (fun i : Fin M => exposedLabels S n s.1 i.val) s.2 ≤
      exposedLabels S n s.1 i then if i < n then (1 : ℝ) / (n - i : ℕ) else 0 else 0
  change (∑ i : Fin M, f i.val) = _
  rw [sum_fin_nat M f]
  have hsub : range n \ S ⊆ range M := by
    intro i hi
    have := mem_range.mp (mem_sdiff.mp hi).1
    exact mem_range.mpr (by omega)
  have hzero : ∀ i ∈ range M, i ∉ range n \ S → f i = 0 := by
    intro i _ hi
    by_cases hin : i < n
    · have hiS : i ∈ S := by
        by_contra hiS
        exact hi (mem_sdiff.mpr ⟨mem_range.mpr hin, hiS⟩)
      have hdel := exposedLabels_deleted S s.1 hiS
      have hpos := nextHeight_pos (fun i : Fin M => exposedLabels S n s.1 i.val) s.2
      simp [f, hdel, show ¬ nextHeight (fun i : Fin M => exposedLabels S n s.1 i.val) s.2 ≤ 0 by omega]
    · simp [f, hin]
  rw [← sum_subset hsub hzero]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp (mem_sdiff.mp hi).1
  simp [f, pairMass, hin, exposedLabels, hnS, show i ≠ n by omega]

theorem forbiddenMass_exposed_step {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) (n + 1)) (hn : n < M) :
    forbiddenMass (range (n + 1) \ S) (exposedLabels S (n + 1) s) =
      forbiddenMass (range n \ S) (exposedLabels S n s.1) + exposedIncrement S n s := by
  have hagree : forbiddenMass (range n \ S) (exposedLabels S (n + 1) s) =
      forbiddenMass (range n \ S) (exposedLabels S n s.1) := by
    apply forbiddenMass_congr
    intro i hi
    have hin := mem_range.mp (mem_sdiff.mp hi).1
    simp [exposedLabels, show i ≠ n by omega]
  by_cases hnS : n ∈ S
  · have hrange : range (n + 1) \ S = range n \ S := by
      ext i
      simp only [mem_sdiff, mem_range]
      by_cases hi : i ∈ S
      · simp [hi]
      · have hne : i ≠ n := by intro he; exact hi (he ▸ hnS)
        simp [hi]
        omega
    rw [hrange, hagree]
    simp [exposedIncrement, hnS]
  · have hrange : range (n + 1) \ S = insert n (range n \ S) := by
      ext i
      simp only [mem_sdiff, mem_range, mem_insert]
      by_cases he : i = n
      · simp [he, hnS]
      · by_cases hi : i ∈ S <;> simp [he, hi] <;> omega
    rw [hrange, forbiddenMass_insert sdiff_subset, hagree, exposedIncrement_eq_sum S s hn hnS]

theorem accumulated_eq_forbiddenMass {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) n) (hn : n ≤ M) :
    accumulated (exposedIncrement S) n s = forbiddenMass (range n \ S) (exposedLabels S n s) := by
  induction n with
  | zero => simp [accumulated, forbiddenMass]
  | succ n ih => rw [accumulated, ih s.1 (by omega), forbiddenMass_exposed_step S s (by omega)]

end ProofOfSpace.DRSample

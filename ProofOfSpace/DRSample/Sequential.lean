import ProofOfSpace.DRSample.Exposure
import ProofOfSpace.DRSample.ProductLaw
import ProofOfSpace.DRSample.Mass
import ProofOfSpace.DRSample.Basic

/-! # Exposing actual depth labels in destination order -/
namespace ProofOfSpace.DRSample
open Finset Classical

def choiceAt {M : ℕ} : (n : ℕ) → SampleSpace (Finset (Fin M)) n → ℕ → Finset (Fin M)
  | 0, _, _ => ∅
  | n + 1, s, j => if j = n then s.2 else choiceAt n s.1 j

noncomputable def exposedLabels {M : ℕ} (S : Finset ℕ) :
    (n : ℕ) → SampleSpace (Finset (Fin M)) n → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, s, j => if j = n then
      if n ∈ S then 0 else nextHeight (fun i : Fin M => exposedLabels S n s.1 i.val) s.2
    else exposedLabels S n s.1 j

theorem exposedLabels_future {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) n) {j : ℕ} (hj : n ≤ j) :
    exposedLabels S n s j = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exposedLabels, if_neg (by omega)]
    exact ih s.1 (by omega)

theorem exposedLabels_deleted {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) n) {j : ℕ} (hj : j ∈ S) :
    exposedLabels S n s j = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases heq : j = n
    · subst j
      simp [exposedLabels, hj]
    · rw [exposedLabels, if_neg heq]
      exact ih s.1

theorem exposedLabels_positive {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) n) {j : ℕ} (hjn : j < n) (hj : j ∉ S) :
    0 < exposedLabels S n s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : j = n
    · subst j
      simpa [exposedLabels, hj] using nextHeight_pos (fun i : Fin M => exposedLabels S n s.1 i.val) s.2
    · rw [exposedLabels, if_neg heq]
      exact ih s.1 (by omega)

def exposedGraph {M : ℕ} (n : ℕ) (s : SampleSpace (Finset (Fin M)) n) : OrderedGraph M where
  edge i j := i.val < j.val ∧ i ∈ choiceAt n s j.val
  increasing h := h.1

theorem choiceAt_future {M n : ℕ} (s : SampleSpace (Finset (Fin M)) n)
    {j : ℕ} (hj : n ≤ j) : choiceAt n s j = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [choiceAt, if_neg (by omega)]
    exact ih s.1 (by omega)

theorem exposedGraph_mono {M n : ℕ} (s : SampleSpace (Finset (Fin M)) n)
    (a : Finset (Fin M)) {i j : Fin M} (h : (exposedGraph n s).edge i j) :
    (exposedGraph (n + 1) (s, a)).edge i j := by
  have hj : j.val ≠ n := by
    intro he
    have hchoice := choiceAt_future s (show n ≤ j.val by omega)
    have := h.2
    rw [hchoice] at this
    exact notMem_empty _ this
  exact ⟨h.1, by simpa [choiceAt, hj] using h.2⟩

/-- Every positive label has an actual surviving path of exactly that length. -/
theorem exposedLabels_path {M n : ℕ} (S : Finset ℕ)
    (s : SampleSpace (Finset (Fin M)) n) (hn : n ≤ M) (v : Fin M)
    (hv : 0 < exposedLabels S n s v.val) :
    ∃ P : List (Fin M), P ≠ [] ∧ P.IsChain (exposedGraph n s).edge ∧
      (∀ u ∈ P, u.val ∉ S) ∧ P.getLast? = some v ∧
      P.length = exposedLabels S n s v.val := by
  induction n generalizing v with
  | zero => simp [exposedLabels] at hv
  | succ n ih =>
    have hvS : v.val ∉ S := by
      intro hvS
      rw [exposedLabels_deleted S s hvS] at hv
      omega
    by_cases hvn : v.val = n
    · have hvalue : exposedLabels S (n + 1) s v.val =
          s.2.sup (fun i : Fin M => exposedLabels S n s.1 i.val) + 1 := by
        simp [exposedLabels, hvn, show n ∉ S from hvn ▸ hvS, nextHeight]
      set a := s.2.sup (fun i : Fin M => exposedLabels S n s.1 i.val) with ha
      by_cases ha0 : a = 0
      · refine ⟨[v], by simp, .singleton _, ?_, by simp, ?_⟩
        · simpa using hvS
        · simp [hvalue, ha0]
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        obtain ⟨u, hu, hau⟩ := (Finset.le_sup_iff hapos).mp (le_refl a)
        have huheight : exposedLabels S n s.1 u.val = a :=
          le_antisymm (Finset.le_sup (f := fun i : Fin M => exposedLabels S n s.1 i.val) hu) hau
        have hun : u.val < n := by
          by_contra! h
          rw [exposedLabels_future S s.1 h] at huheight
          omega
        obtain ⟨P, hne, hchain, havoid, hlast, hlen⟩ := ih s.1 (by omega) u (hapos.trans_le hau)
        have hchain' : P.IsChain (exposedGraph (n + 1) s).edge :=
          hchain.imp fun _ _ h => exposedGraph_mono s.1 s.2 h
        have huv : (exposedGraph (n + 1) s).edge u v :=
          ⟨by omega, by simpa [choiceAt, hvn] using hu⟩
        refine ⟨P ++ [v], by simp, hchain'.append (.singleton _) ?_, ?_, by simp, ?_⟩
        · simpa [hlast] using huv
        · intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact havoid w hw
          · simpa using List.mem_singleton.mp hw ▸ hvS
        · simp [hlen, huheight, hvalue]
    · have heq : exposedLabels S (n + 1) s v.val = exposedLabels S n s.1 v.val := by
        simp [exposedLabels, hvn]
      obtain ⟨P, hne, hchain, havoid, hlast, hlen⟩ := ih s.1 (by omega) v (heq ▸ hv)
      exact ⟨P, hne, hchain.imp (fun _ _ h => exposedGraph_mono s.1 s.2 h),
        havoid, hlast, hlen.trans heq.symm⟩

noncomputable def harmonicAt (M j : ℕ) (i : Fin M) : ℝ :=
  if i.val < j then 1 / (j - i.val : ℕ) else 0

noncomputable def exposedIncrement {M : ℕ} (S : Finset ℕ) (n : ℕ)
    (s : SampleSpace (Finset (Fin M)) (n + 1)) : ℝ :=
  if n ∈ S ∨ M ≤ n then 0 else
    newForbiddenMass (fun i : Fin M => exposedLabels S n s.1 i.val) (harmonicAt M n) s.2

theorem exposedIncrement_moment {M : ℕ} (p : ℕ → FiniteLaw (Finset (Fin M)))
    (S : Finset ℕ) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i))
    (n : ℕ) (past : SampleSpace (Finset (Fin M)) n) :
    (p n).expectation (fun a => Real.exp (lambda / 2 * exposedIncrement S n (past, a))) ≤
      if n ∈ S ∨ M ≤ n then 1 else 2 := by
  by_cases h : n ∈ S ∨ M ≤ n
  · simp only [exposedIncrement, if_pos h, mul_zero, Real.exp_zero,
      FiniteLaw.expectation_const]
    exact le_rfl
  · simp only [exposedIncrement, if_neg h]
    have hw : ∀ i : Fin M, 0 ≤ harmonicAt M n i := by
      intro i
      unfold harmonicAt
      positivity
    exact newForbiddenMass_moment (p n) _ _ hw hlambda (havoid n (by omega))

end ProofOfSpace.DRSample

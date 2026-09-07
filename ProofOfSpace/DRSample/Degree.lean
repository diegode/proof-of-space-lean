import ProofOfSpace.DRSample.FiniteRobustness

/-! # The Filecoin law produces graphs of indegree at most six -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem FiniteLaw.map_support {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (f : α → β) (Q : β → Prop) (hQ : ∀ a, Q (f a))
    (b : β) (hb : (p.map f).weight b ≠ 0) : Q b := by
  by_contra hnot
  have heq : ∀ a, b ≠ f a := fun a he => hnot (he ▸ hQ a)
  apply hb
  simp [map, bind, pure, heq]

theorem FiniteLaw.probability_and_of_support {α : Type*} [Fintype α] (p : FiniteLaw α)
    (Q R : α → Prop) (hQ : ∀ a, p.weight a ≠ 0 → Q a) :
    p.probability (fun a => Q a ∧ R a) = p.probability R := by
  unfold probability
  apply sum_congr rfl
  intro a _
  by_cases ha : p.weight a = 0
  · simp [ha]
  · simp [hQ a ha]

theorem parentSetLaw_support {n d v : ℕ} (p : FiniteLaw (Fin n))
    (parents : Finset (Fin n)) (hp : (parentSetLaw d v p).weight parents ≠ 0) :
    parents.card ≤ d + 1 ∧ ∀ u : Fin n, u.val + 1 = v → u ∈ parents := by
  exact FiniteLaw.map_support _ _ (fun parents =>
    parents.card ≤ d + 1 ∧ ∀ u : Fin n, u.val + 1 = v → u ∈ parents)
    (fun draws => ⟨sampledParents_card v draws, mem_sampledParents_line draws⟩) parents hp

theorem independentSamples_get_support {α : Type*} [Fintype α]
    (p : ℕ → FiniteLaw α) (fallback : α) {R j : ℕ} (s : SampleSpace α R)
    (hs : (independentSamples p R).weight s ≠ 0) (hj : j < R) :
    (p j).weight (getSample fallback R s j) ≠ 0 := by
  induction R with
  | zero => omega
  | succ R ih =>
    have hweights : (independentSamples p R).weight s.1 * (p R).weight s.2 ≠ 0 := hs
    have hp := (mul_ne_zero_iff.mp hweights).1
    have hq := (mul_ne_zero_iff.mp hweights).2
    by_cases he : j = R
    · subst j
      simpa [getSample] using hq
    · rw [getSample, if_neg he]
      exact ih s.1 hp (by omega)

theorem rowLaw_get_support {n m R : ℕ} (p : ℕ → FiniteLaw (Finset (Fin n)))
    (s : SampleSpace (Fin m → Finset (Fin n)) R)
    (hs : (independentSamples (rowLaw m p) R).weight s ≠ 0) {j : ℕ} (hj : j < R) (k : Fin m) :
    (p (j * m + k.val)).weight (getSample (fun _ => ∅) R s j k) ≠ 0 := by
  have hrow := independentSamples_get_support (rowLaw m p) (fun _ => ∅) s hs hj
  change (∏ k : Fin m, (p (j * m + k.val)).weight (getSample (fun _ => ∅) R s j k)) ≠ 0 at hrow
  exact (prod_ne_zero_iff.mp hrow) k (mem_univ k)

def IndegreeAtMost {n : ℕ} (G : OrderedGraph n) (d : ℕ) : Prop :=
  ∀ v : Fin n, (G.parents v).card ≤ d

theorem rowGraph_indegree_of_support {n m d : ℕ} (hm : 0 < m)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (hparents : ∀ v < n, ∀ parents, (p v).weight parents ≠ 0 →
      parents.card ≤ d ∧ ∀ u : Fin n, u.val + 1 = v → u ∈ parents)
    (s : SampleSpace (Fin m → Finset (Fin n)) (n / m + 1))
    (hs : (graphLaw m p).weight s ≠ 0) :
    IndegreeAtMost (rowGraph hm (n / m + 1) s) d := by
  intro v
  let k : Fin m := ⟨v.val % m, Nat.mod_lt _ hm⟩
  have hj : v.val / m < n / m + 1 := by
    have hle : v.val / m ≤ n / m := Nat.div_le_div_right v.isLt.le
    omega
  have hsupport := rowLaw_get_support p s hs hj k
  have hindex : v.val / m * m + k.val = v.val := by
    dsimp [k]
    simpa only [Nat.mul_comm] using Nat.div_add_mod v.val m
  rw [hindex] at hsupport
  obtain ⟨hcard, hline⟩ := hparents v.val v.isLt _ hsupport
  apply (card_le_card (show (rowGraph hm (n / m + 1) s).parents v ⊆
    getSample (fun _ => ∅) (n / m + 1) s (v.val / m) k from ?_)).trans hcard
  intro u hu
  have hedge := OrderedGraph.mem_parents.mp hu
  rcases hedge.2 with hu | hu
  · exact hline u hu
  · exact hu

theorem filecoin_bucket6_indegree {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : SampleSpace (Fin m → Finset (Fin n)) (n / m + 1))
    (hs : (graphLaw m (filecoinIncomingLaw hn)).weight s ≠ 0) :
    IndegreeAtMost (rowGraph hm (n / m + 1) s) 6 := by
  apply rowGraph_indegree_of_support hm (filecoinIncomingLaw hn) _ s hs
  intro v _ parents hp
  exact parentSetLaw_support (filecoinParentLaw hn v) parents hp

theorem filecoin_bucket6_finite_with_degree {n m : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n) :
    (graphLaw m (filecoinIncomingLaw (by omega))).probability (fun s =>
      IndegreeAtMost (rowGraph (by omega) (n / m + 1) s) 6 ∧
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) ((n / m) / 96)
        (((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * Real.logb 2 n / (3 * m)))) m) ≥
      1 - Real.exp (-(2 - Real.log 3) * (n / m : ℕ)) := by
  rw [FiniteLaw.probability_and_of_support _ _ _ (filecoin_bucket6_indegree (by omega) (by omega))]
  exact filecoin_bucket6_finite hm hmn

end ProofOfSpace.DRSample

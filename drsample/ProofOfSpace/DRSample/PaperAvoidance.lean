import ProofOfSpace.DRSample.GeneralParameters

namespace ProofOfSpaceStatement
open Finset Filter ProofOfSpace.DRSample

private def toFiniteLaw {α : Type*} [Fintype α] (p : FiniteDistribution α) : FiniteLaw α :=
  ⟨p.weight, p.nonneg, p.total⟩

private theorem incomingGraph_statement {n : ℕ} (sets : Fin n → Finset (Fin n))
    (e b : ℕ) (d : ℝ) :
    BlockDepthRobust (incomingGraph sets) e d b ↔ GraphBlockDepthRobust (incomingEdge sets) e d b := by
  classical
  simp only [BlockDepthRobust, HasPath, incomingGraph, incomingEdge, GraphBlockDepthRobust,
    blockDeleted, mem_filter, mem_univ, true_and, not_exists, not_and]
  rfl

/-- Lemma `lem:sampler-avoidance`. The constants depend only on `β`, and the
threshold on the number of vertices can also depend on `ε`. The product bound
and robustness hold with the same deterministic parameters `e,b`. -/
theorem sampler_avoidance {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e b : ℕ,
          c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          c * (L / ε) ≤ b ∧ (b : ℝ) ≤ C * (L / ε) ∧ β * n ≤ (e : ℝ) * b ∧
          ∀ p : Fin n → FiniteDistribution (Finset (Fin n)),
            SupportedIncomingEdges p → HarmonicAvoidance p →
            incomingProbability p (fun sets => GraphBlockDepthRobust (incomingEdge sets)
              e (c * n / (Real.logb 2 n) ^ ε) b) ≥
            1 - Real.exp (-c * (ε * n / L)) := by
  classical
  obtain ⟨c, C, hc, hC, hparams⟩ := eventually_avoidance_product hβ hβ1
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε hε1
  filter_upwards [hparams ε hε hε1] with n hn
  obtain ⟨hn, e, b, heLo, heHi, hbLo, hbHi, heb, hrobust⟩ := hn
  refine ⟨e, b, heLo, heHi, hbLo, hbHi, heb, ?_⟩
  intro p _hgraph havoid
  let law (v : ℕ) : FiniteLaw (Finset (Fin n)) :=
    if hv : v < n then toFiniteLaw (p ⟨v, hv⟩) else FiniteLaw.pure ∅
  have hlaw : ∀ v < n, ∀ U : Finset (Fin n),
      (law v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u) := by
    intro v hv U
    let A := U.filter fun u => u.val < v
    have h := havoid ⟨v, hv⟩ A (fun u hu => (mem_filter.mp hu).2)
    have hsum : (∑ u ∈ A, (1 : ℝ) / (v - u.val : ℕ)) = ∑ u ∈ U, harmonicAt n v u := by
      simp only [A, sum_filter, harmonicAt]
    rw [hsum] at h
    apply le_trans ?_ h
    change (law v).probability (fun parents => Disjoint parents U) ≤
      (toFiniteLaw (p ⟨v, hv⟩)).probability (fun parents => Disjoint parents A)
    simp only [law, dif_pos hv]
    apply FiniteLaw.probability_mono
    intro parents hparents
    exact hparents.mono_right (filter_subset _ _)
  have h := hrobust law hlaw
  simp_rw [incomingGraph_statement] at h
  have heq : (FiniteLaw.pi (fun v : Fin n => law v.val)).probability
      (fun sets => GraphBlockDepthRobust (incomingEdge sets) e (c * n / (Real.logb 2 n) ^ ε) b) =
      incomingProbability p
        (fun sets => GraphBlockDepthRobust (incomingEdge sets) e (c * n / (Real.logb 2 n) ^ ε) b) := by
    simp only [FiniteLaw.probability, FiniteLaw.pi, law, dif_pos (Fin.isLt _),
      toFiniteLaw, incomingProbability]
  rw [heq] at h
  exact h

end ProofOfSpaceStatement

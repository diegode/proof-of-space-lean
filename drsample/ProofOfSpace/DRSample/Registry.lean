import ProofOfSpace.DRSample.DistributionMap
import ProofOfSpace.DRSample.Statement

/-! # Connecting the self-contained DRSample statement to the multiscale proof -/
namespace ProofOfSpace.DRSample
open Finset Classical Filter
open ProofOfSpaceStatement

/-- The public bucket formula is exactly the finite sampler's parent law. -/
theorem drParentLaw_weight_statement {n : ℕ} (hn : 0 < n) (v u : Fin n) :
    (drParentLaw hn v.val).weight u = drsampleParentProbability v u := by
  by_cases hv : 2 ≤ v.val
  · rw [← FiniteLaw.probability_singleton, drParentLaw, dif_pos v.isLt, dif_pos hv,
      contractedBucketLaw, FiniteLaw.probability_map, bucketLaw, FiniteLaw.probability_bind]
    simp only [drsampleParentProbability, if_pos hv, FiniteLaw.expectation,
      FiniteLaw.uniformOn, mem_univ, ↓reduceIte, card_univ, Fintype.card_fin]
    apply sum_congr rfl
    intro k _
    congr 1
    have hcard : (bucketDistances true (1 * v.val) (k.val + 1)).card =
        (drsampleBucket v.val (k.val + 1)).card := by
      rw [Nat.one_mul]
      rfl
    simp only [FiniteLaw.probability, hcard, drsampleBucket, sum_filter]
    apply Fintype.sum_equiv (finCongr (show 1 * v.val + 1 = v.val + 1 by omega))
    intro r
    simp only [contractedParent, Fin.ext_iff, one_mul, Nat.div_one,
      bucketDistances, bucketLower, bucketUpper, ↓reduceIte, mem_filter, mem_univ, true_and]
    dsimp only [finCongr, Equiv.coe_fn_mk, Fin.cast]
    change (if v.val - r.val = u.val then
      if max 2 ((min v.val (2 ^ (k.val + 1)) + 1) / 2) ≤ r.val ∧
          r.val ≤ min v.val (2 ^ (k.val + 1)) then
        (1 : ℝ) / (drsampleBucket v.val (k.val + 1)).card else 0 else 0) =
      (if max 2 ((min v.val (2 ^ (k.val + 1)) + 1) / 2) ≤ r.val ∧
          r.val ≤ min v.val (2 ^ (k.val + 1)) then
        if v.val - r.val = u.val then
          (1 : ℝ) / (drsampleBucket v.val (k.val + 1)).card else 0 else 0)
    by_cases hp : v.val - r.val = u.val <;>
      by_cases hb : max 2 ((min v.val (2 ^ (k.val + 1)) + 1) / 2) ≤ r.val ∧
        r.val ≤ min v.val (2 ^ (k.val + 1)) <;> simp [hp, hb]
  · simp [drParentLaw, v.isLt, hv, drsampleParentProbability,
      FiniteLaw.pure, Fin.ext_iff]

/-- Independent choices under the public finite-sum formula have total mass one. -/
theorem drsampleProbability_eq {n : ℕ} (hn : 0 < n)
    (event : (Fin n → Fin n) → Prop) :
    drsampleProbability n event =
      (FiniteLaw.pi (fun v : Fin n => drParentLaw hn v.val)).probability event := by
  unfold drsampleProbability FiniteLaw.probability FiniteLaw.pi
  simp_rw [drParentLaw_weight_statement hn]

theorem drsampleProbability_total {n : ℕ} (hn : 0 < n) :
    drsampleProbability n (fun _ => True) = 1 := by
  rw [drsampleProbability_eq hn, FiniteLaw.probability_true]

/-- One parent draw, represented either as a single value or a one-coordinate function. -/
theorem drIncomingLaw_as_map {n : ℕ} (hn : 0 < n) (v : ℕ) :
    drIncomingLaw hn v = (drParentLaw hn v).map
      (fun u => sampledParents v (fun _ : Fin 1 => u)) := by
  apply FiniteLaw.ext_weights
  intro parents
  unfold drIncomingLaw parentSetLaw FiniteLaw.map FiniteLaw.bind FiniteLaw.pi
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n))
  intro draws
  simp only [Fin.prod_univ_one]
  congr 2

/-- The graph attached to incoming parent sets, with the predecessor edges included. -/
def incomingGraph {n : ℕ} (sets : Fin n → Finset (Fin n)) : OrderedGraph n where
  edge u v := u < v ∧ (u.val + 1 = v.val ∨ u ∈ sets v)
  increasing h := h.1

theorem graphLaw_probability_as_pi {n m : ℕ} (hm : 0 < m)
    (p : ℕ → FiniteLaw (Finset (Fin n))) (event : OrderedGraph n → Prop) :
    (graphLaw m p).probability (fun s => event (rowGraph hm (n / m + 1) s)) =
      (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets => event (incomingGraph sets)) := by
  rw [← graphLaw_as_pi hm p, FiniteLaw.probability_map]
  rfl

theorem incomingGraph_block_statement {n : ℕ} (parents : Fin n → Fin n) (e b : ℕ) (d : ℝ) :
    BlockDepthRobust (incomingGraph (fun v => sampledParents v.val (fun _ : Fin 1 => parents v)))
      e d b ↔ DRSampleBlockDepthRobust parents e d b := by
  have hedge : (incomingGraph (fun v => sampledParents v.val (fun _ : Fin 1 => parents v))).edge =
      drsampleEdge parents := by
    funext u v
    simp [incomingGraph, sampledParents, drsampleEdge, eq_comm]
    tauto
  simp only [BlockDepthRobust, HasPath, hedge, DRSampleBlockDepthRobust,
    blockDeleted, mem_filter, mem_univ, true_and, not_exists, not_and]

end ProofOfSpace.DRSample

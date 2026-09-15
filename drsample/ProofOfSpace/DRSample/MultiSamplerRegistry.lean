import ProofOfSpace.DRSample.Registry
import ProofOfSpace.DRSample.BucketSample

namespace ProofOfSpace.DRSample
open Finset Classical ProofOfSpaceStatement

theorem bucketParentLaw_weight_statement {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (v u : Fin n) :
    (bucketParentLaw hn hr v.val).weight u = bucketSampleParentProbability r v u := by
  by_cases hv : 2 ≤ v.val
  · rw [← FiniteLaw.probability_singleton, bucketParentLaw, dif_pos v.isLt, dif_pos hv,
      contractedBucketLaw, FiniteLaw.probability_map, bucketLaw, FiniteLaw.probability_bind]
    simp only [bucketSampleParentProbability, if_pos hv, FiniteLaw.expectation,
      FiniteLaw.uniformOn, mem_univ, ↓reduceIte, card_univ, Fintype.card_fin]
    apply sum_congr rfl
    intro k _
    congr 1
    have hcard : (bucketDistances false (r * v.val) (k.val + 1)).card =
        (bucketSampleBucket (r * v.val) (k.val + 1)).card := rfl
    simp only [FiniteLaw.probability, hcard, bucketSampleBucket, sum_filter]
    apply sum_congr rfl
    intro s _
    simp only [contractedParent, Fin.ext_iff, bucketDistances, bucketLower,
      bucketUpper, ↓reduceIte, mem_filter, mem_univ, true_and]
    by_cases hp : (r * v.val - s.val) / r = u.val <;>
      by_cases hb : max 2 (min (r * v.val) (2 ^ (k.val + 1)) / 2) ≤ s.val ∧
        s.val ≤ min (r * v.val) (2 ^ (k.val + 1)) <;> simp [hp, hb] <;> aesop <;> omega
  · simp [bucketParentLaw, v.isLt, hv, bucketSampleParentProbability, FiniteLaw.pure, Fin.ext_iff]

theorem multiSampleProbability_eq {n r : ℕ} (p : Fin n → FiniteLaw (Fin n))
    (event : (Fin n → Fin r → Fin n) → Prop) :
    multiSampleProbability n r (fun v u => (p v).weight u) event =
      (FiniteLaw.pi (fun v : Fin n => FiniteLaw.pi (fun _ : Fin r => p v))).probability event := rfl

theorem bucketSampleProbability_eq {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (event : (Fin n → Fin r → Fin n) → Prop) :
    bucketSampleProbability n r event =
      (FiniteLaw.pi (fun v : Fin n =>
        FiniteLaw.pi (fun _ : Fin r => bucketParentLaw hn hr v.val))).probability event := by
  rw [← multiSampleProbability_eq]
  simp_rw [bucketParentLaw_weight_statement]
  rfl

theorem bucketSampleProbability_total {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    bucketSampleProbability n r (fun _ => True) = 1 := by
  rw [bucketSampleProbability_eq hn hr, FiniteLaw.probability_true]

theorem incomingGraph_multi_statement {n r : ℕ} (parents : Fin n → Fin r → Fin n)
    (e b : ℕ) (d : ℝ) :
    BlockDepthRobust (incomingGraph (fun v => sampledParents v.val (parents v))) e d b ↔
      MultiSampleBlockDepthRobust parents e d b := by
  have he : (incomingGraph (fun v => sampledParents v.val (parents v))).edge =
      multiSampleEdge parents := by
    funext u v
    simp [incomingGraph, sampledParents, multiSampleEdge]
    tauto
  simp only [BlockDepthRobust, HasPath, he, MultiSampleBlockDepthRobust,
    blockDeleted, mem_filter, mem_univ, true_and, not_exists, not_and]

theorem parentSetLaw_block_probability {n r : ℕ} (p : Fin n → FiniteLaw (Fin n))
    (e b : ℕ) (d : ℝ) :
    (FiniteLaw.pi (fun v : Fin n => parentSetLaw r v.val (p v))).probability
      (fun sets => BlockDepthRobust (incomingGraph sets) e d b) =
    (FiniteLaw.pi (fun v : Fin n => FiniteLaw.pi (fun _ : Fin r => p v))).probability
      (fun parents => MultiSampleBlockDepthRobust parents e d b) := by
  simp only [parentSetLaw]
  rw [← FiniteLaw.pi_map, FiniteLaw.probability_map]
  simp_rw [incomingGraph_multi_statement]

end ProofOfSpace.DRSample

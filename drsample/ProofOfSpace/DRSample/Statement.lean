import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-! # DRSample: the finite graph distribution and block depth robustness

Vertices are numbered from zero. At each vertex `v ≥ 2`, independently choose
one of `ceil(log₂(v+1))` buckets uniformly, then a distance uniformly from
that bucket. Include the resulting parent edge and every predecessor edge.
The capped buckets and upward rounding below specify the distribution exactly.
-/
namespace ProofOfSpaceStatement
open Finset Filter

/-- Distances in bucket `k`, capped at the number `v` of earlier vertices.
The lower endpoint is rounded upward and excludes distances zero and one. -/
def drsampleBucket (v k : ℕ) : Finset (Fin (v + 1)) :=
  univ.filter fun r => max 2 ((min v (2 ^ k) + 1) / 2) ≤ r.val ∧
    r.val ≤ min v (2 ^ k)

/-- Probability that the single random parent of `v` is `u`.
Vertices zero and one use the dummy parent zero; the graph also has line edges. -/
noncomputable def drsampleParentProbability {n : ℕ} (v u : Fin n) : ℝ := by
  classical
  exact if 2 ≤ v.val then
    ∑ k : Fin (Nat.clog 2 (v.val + 1)),
      ((1 : ℝ) / (Nat.clog 2 (v.val + 1) : ℕ)) *
        ∑ r ∈ drsampleBucket v.val (k.val + 1),
          if v.val - r.val = u.val then
            (1 : ℝ) / (drsampleBucket v.val (k.val + 1)).card else 0
  else if u.val = 0 then 1 else 0

/-- Probability of an event under independent parent choices at all vertices.
This is the ordinary finite sum of the event's product probabilities. -/
noncomputable def drsampleProbability (n : ℕ) (event : (Fin n → Fin n) → Prop) : ℝ := by
  classical
  exact ∑ parents : Fin n → Fin n,
    if event parents then ∏ v : Fin n, drsampleParentProbability v (parents v) else 0

/-- The ordered DRSample graph: the predecessor and the chosen random parent. -/
def drsampleEdge {n : ℕ} (parents : Fin n → Fin n) (u v : Fin n) : Prop :=
  u < v ∧ (u.val + 1 = v.val ∨ parents v = u)

/-- Deleting at most `e` left intervals of width `b` leaves a directed path of
at least `d` vertices. Intervals end at the chosen endpoints, may overlap, and
are truncated at vertex zero. Endpoints are chosen after sampling the graph. -/
def DRSampleBlockDepthRobust {n : ℕ} (parents : Fin n → Fin n)
    (e : ℕ) (d : ℝ) (b : ℕ) : Prop :=
  ∀ endpoints : Finset (Fin n), endpoints.card ≤ e →
    ∃ path : List (Fin n), path ≠ [] ∧ path.IsChain (drsampleEdge parents) ∧
      (∀ u ∈ path, ∀ v ∈ endpoints, ¬ (u ≤ v ∧ v.val < u.val + b)) ∧
      d ≤ (path.length : ℝ)

/-- Fine distances in a BucketSample bucket, with its downward-rounded lower endpoint. -/
def bucketSampleBucket (p k : ℕ) : Finset (Fin (p + 1)) :=
  univ.filter fun s => max 2 (min p (2 ^ k) / 2) ≤ s.val ∧ s.val ≤ min p (2 ^ k)

/-- One BucketSample draw at the shared fine position `r v`. -/
noncomputable def bucketSampleParentProbability {n : ℕ} (r : ℕ) (v u : Fin n) : ℝ := by
  classical
  exact if 2 ≤ v.val then
    ∑ k : Fin (Nat.clog 2 (r * v.val)),
      ((1 : ℝ) / Nat.clog 2 (r * v.val)) *
        ∑ s ∈ bucketSampleBucket (r * v.val) (k.val + 1),
          if (r * v.val - s.val) / r = u.val then
            (1 : ℝ) / (bucketSampleBucket (r * v.val) (k.val + 1)).card else 0
  else if u.val = 0 then 1 else 0

/-- Product probability over all destinations and all independent parent draws. -/
noncomputable def multiSampleProbability (n r : ℕ) (p : Fin n → Fin n → ℝ)
    (event : (Fin n → Fin r → Fin n) → Prop) : ℝ := by
  classical
  exact ∑ parents : Fin n → Fin r → Fin n,
    if event parents then ∏ v : Fin n, ∏ j : Fin r, p v (parents v j) else 0

noncomputable def bucketSampleProbability (n r : ℕ)
    (event : (Fin n → Fin r → Fin n) → Prop) : ℝ :=
  multiSampleProbability n r (bucketSampleParentProbability r) event

/-- The predecessor edge together with the `r` chosen parent edges. -/
def multiSampleEdge {n r : ℕ} (parents : Fin n → Fin r → Fin n) (u v : Fin n) : Prop :=
  u < v ∧ (u.val + 1 = v.val ∨ ∃ j : Fin r, parents v j = u)

def MultiSampleBlockDepthRobust {n r : ℕ} (parents : Fin n → Fin r → Fin n)
    (e : ℕ) (d : ℝ) (b : ℕ) : Prop :=
  ∀ endpoints : Finset (Fin n), endpoints.card ≤ e →
    ∃ path : List (Fin n), path ≠ [] ∧ path.IsChain (multiSampleEdge parents) ∧
      (∀ u ∈ path, ∀ v ∈ endpoints, ¬ (u ≤ v ∧ v.val < u.val + b)) ∧
      d ≤ (path.length : ℝ)

end ProofOfSpaceStatement

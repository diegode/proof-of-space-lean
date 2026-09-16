import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

/-! # Current paper statements with completed Lean proofs

This is the Mathlib-only statement surface. Each intentional placeholder has
an independently checked proof in `Solution`. See README.md for the full paper
inventory; the cited BRG pebbling corollary is outside scope.
-/
namespace ProofOfSpaceStatement
open Finset Filter

def drsampleBucket (v k : ℕ) : Finset (Fin (v + 1)) :=
  univ.filter fun r => max 2 ((min v (2 ^ k) + 1) / 2) ≤ r.val ∧
    r.val ≤ min v (2 ^ k)

noncomputable def drsampleParentProbability {n : ℕ} (v u : Fin n) : ℝ := by
  classical
  exact if 2 ≤ v.val then
    ∑ k : Fin (Nat.clog 2 (v.val + 1)),
      ((1 : ℝ) / (Nat.clog 2 (v.val + 1) : ℕ)) *
        ∑ r ∈ drsampleBucket v.val (k.val + 1),
          if v.val - r.val = u.val then
            (1 : ℝ) / (drsampleBucket v.val (k.val + 1)).card else 0
  else if u.val = 0 then 1 else 0

noncomputable def drsampleProbability (n : ℕ) (event : (Fin n → Fin n) → Prop) : ℝ := by
  classical
  exact ∑ parents : Fin n → Fin n,
    if event parents then ∏ v : Fin n, drsampleParentProbability v (parents v) else 0

/-- The ordered DRSample graph: the predecessor and the chosen random parent. -/
def drsampleEdge {n : ℕ} (parents : Fin n → Fin n) (u v : Fin n) : Prop :=
  u < v ∧ (u.val + 1 = v.val ∨ parents v = u)

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

open Finset

def IsOrdered {n : ℕ} (edge : Fin n → Fin n → Prop) : Prop :=
  ∀ u v, edge u v → u < v

def ContainsLine {n : ℕ} (edge : Fin n → Fin n → Prop) : Prop :=
  ∀ u v, u.val + 1 = v.val → edge u v

def AvoidingPath {n : ℕ} (edge : Fin n → Fin n → Prop)
    (D : Finset (Fin n)) (path : List (Fin n)) : Prop :=
  path.IsChain edge ∧ ∀ v ∈ path, v ∉ D

def GraphBlockDepthRobust {n : ℕ} (edge : Fin n → Fin n → Prop)
    (e : ℕ) (d : ℝ) (b : ℕ) : Prop :=
  ∀ endpoints : Finset (Fin n), endpoints.card ≤ e →
    ∃ path : List (Fin n), path ≠ [] ∧ path.IsChain edge ∧
      (∀ u ∈ path, ∀ v ∈ endpoints, ¬ (u ≤ v ∧ v.val < u.val + b)) ∧
      d ≤ (path.length : ℝ)

def DepthAtMost {n : ℕ} (edge : Fin n → Fin n → Prop)
    (D : Finset (Fin n)) (d : ℕ) : Prop :=
  ∀ path, AvoidingPath edge D path → path.length ≤ d

def StartsLongPath {n : ℕ} (edge : Fin n → Fin n → Prop)
    (D : Finset (Fin n)) (d : ℝ) (v : Fin n) : Prop :=
  ∃ path : List (Fin n), AvoidingPath edge D path ∧
    path.head? = some v ∧ d ≤ (path.length : ℝ)

def EndsLongPath {n : ℕ} (edge : Fin n → Fin n → Prop)
    (D : Finset (Fin n)) (d : ℝ) (v : Fin n) : Prop :=
  ∃ path : List (Fin n), AvoidingPath edge D path ∧
    path.getLast? = some v ∧ d ≤ (path.length : ℝ)

def FractionalDepthRobust {n : ℕ} (edge : Fin n → Fin n → Prop)
    (e : ℕ) (d fPlus fMinus : ℝ) : Prop := by
  classical
  exact ∀ D : Finset (Fin n), D.card ≤ e →
    fPlus * n ≤ ((univ.filter (StartsLongPath edge D d)).card : ℝ) ∧
    fMinus * n ≤ ((univ.filter (EndsLongPath edge D d)).card : ℝ)

def IndegreeAtMost {n : ℕ} (edge : Fin n → Fin n → Prop) (Δ : ℕ) : Prop := by
  classical
  exact ∀ v, (univ.filter fun u => edge u v).card ≤ Δ

/-- Normalized real weights for one finite random choice. -/
structure FiniteDistribution (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

noncomputable def finiteProbability {α : Type*} [Fintype α]
    (p : FiniteDistribution α) (event : α → Prop) : ℝ := by
  classical
  exact ∑ a, if event a then p.weight a else 0

/-- Independent incoming-edge sets at distinct destinations. -/
noncomputable def incomingProbability {n : ℕ}
    (p : Fin n → FiniteDistribution (Finset (Fin n)))
    (event : (Fin n → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact ∑ sets, if event sets then ∏ v, (p v).weight (sets v) else 0

def incomingEdge {n : ℕ} (sets : Fin n → Finset (Fin n)) (u v : Fin n) : Prop :=
  u < v ∧ (u.val + 1 = v.val ∨ u ∈ sets v)

/-- The distributions describe the whole incoming-edge set, including line edges. -/
def SupportedIncomingEdges {n : ℕ}
    (p : Fin n → FiniteDistribution (Finset (Fin n))) : Prop :=
  ∀ v parents, 0 < (p v).weight parents →
    (∀ u ∈ parents, u < v) ∧ (∀ u : Fin n, u.val + 1 = v.val → u ∈ parents)

/-- Equation `eq:harmonic-avoidance` for distributions of whole incoming-edge sets. -/
def HarmonicAvoidance {n : ℕ}
    (p : Fin n → FiniteDistribution (Finset (Fin n))) : Prop :=
  ∀ v (A : Finset (Fin n)), (∀ u ∈ A, u < v) →
    finiteProbability (p v) (fun parents => Disjoint parents A) ≤
    Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ A, (1 : ℝ) / (v.val - u.val : ℕ))

/-- The reciprocal-distance cost `c_j` in `lem:dr-subsequence`. -/
noncomputable def comparisonCost (a : ℕ → ℤ) (n j : ℕ) : ℝ :=
  (∑ i ∈ Ico 0 j, if a j ≤ a i then (1 : ℝ) / (j - i : ℕ) else 0) +
  ∑ i ∈ Ico (j + 1) n, if a i ≤ a j then (1 : ℝ) / (i - j : ℕ) else 0

/-- The inconsistency mass `w` in `lem:dr-labels`. -/
noncomputable def labelMass (U : Finset ℕ) (h : ℕ → ℕ) : ℝ :=
  ∑ j ∈ U, ∑ i ∈ U, if i < j ∧ h j ≤ h i then (1 : ℝ) / (j - i : ℕ) else 0

abbrev LabelArray (n : ℕ) := Finset (Fin n) → Fin n → ℕ

noncomputable def labelProbability {n : ℕ} (p : PMF (LabelArray n))
    (event : LabelArray n → Prop) : ℝ :=
  (p.toOuterMeasure {h | event h}).toReal

def EarlierLabels {n : ℕ} (S : Finset (Fin n)) (j : Fin n)
    (past : Fin n → ℕ) (h : LabelArray n) : Prop :=
  ∀ i, i ∉ S → i < j → h S i = past i

def ConditionalHeightBound {n : ℕ} (p : PMF (LabelArray n)) (lambda : ℝ) : Prop :=
  ∀ S j, j ∉ S → ∀ past : Fin n → ℕ,
    0 < labelProbability p (EarlierLabels S j past) → ∀ k : ℕ, 0 < k →
    labelProbability p (fun h => EarlierLabels S j past h ∧ h S j ≤ k) ≤
      Real.exp (-lambda * ∑ i ∈ univ.filter (fun i => i ∉ S ∧ i < j ∧ k ≤ past i),
        (1 : ℝ) / (j.val - i.val : ℕ)) * labelProbability p (EarlierLabels S j past)

/-- Paper result `thm:dr-conjecture2`. -/
theorem drsample_conjecture2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e b : ℕ,
          c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          c * (L / ε) ≤ b ∧ (b : ℝ) ≤ C * (L / ε) ∧
          drsampleProbability n (fun parents => DRSampleBlockDepthRobust parents
            e (c * n / (Real.logb 2 n) ^ ε) b) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  sorry

/-- Paper result `lem:sampler-avoidance`. -/
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
  sorry

/-- Paper result `cor:bucket-optimal`. -/
theorem bucketSample_block_robustness :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ, 1 ≤ r → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e b : ℕ,
          c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          c * (L / ε) ≤ b ∧ (b : ℝ) ≤ C * (L / ε) ∧
          bucketSampleProbability n r (fun parents => MultiSampleBlockDepthRobust parents
            e (c * n / (Real.logb 2 n) ^ ε) b) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  sorry

/-- Paper result `thm:block-to-fractional` (Blocki--Zhou, Theorem 4). -/
theorem block_to_fractional {n e b : ℕ} {edge : Fin n → Fin n → Prop}
    (_hordered : IsOrdered edge) (hline : ContainsLine edge)
    (hb : 1 ≤ b) (hbn : b ≤ n) {d : ℝ} (_hd : 0 < d)
    (hrobust : GraphBlockDepthRobust edge e d b) :
    FractionalDepthRobust edge (e / 2) d 0 ((e : ℝ) * b / (2 * n)) := by
  sorry

/-- Paper result `cor:bucket-fractional`, for DRSample. -/
theorem drsample_fractional_robustness {f : ℝ} (hf : 0 < f) (hfHalf : f < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e : ℕ, c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          drsampleProbability n (fun parents => FractionalDepthRobust (drsampleEdge parents)
            e (c * n / (Real.logb 2 n) ^ ε) f f) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  sorry

/-- Paper result `cor:bucket-fractional`, for every positive number of draws. -/
theorem bucketSample_fractional_robustness {f : ℝ} (hf : 0 < f) (hfHalf : f < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ, 1 ≤ r → ∀ᶠ n : ℕ in atTop,
        let L := Real.logb 2 n / Real.logb 2 (Real.logb 2 n)
        ∃ e : ℕ, c * (ε * n / L) ≤ e ∧ (e : ℝ) ≤ C * (ε * n / L) ∧
          bucketSampleProbability n r (fun parents =>
            FractionalDepthRobust (multiSampleEdge parents)
              e (c * n / (Real.logb 2 n) ^ ε) f f) ≥
          1 - Real.exp (-c * (ε * n / L)) := by
  sorry

/-- Paper result `lem:dr-subsequence`. -/
theorem dr_subsequence {n : ℕ} (_hn : 1 ≤ n) (a : ℕ → ℤ)
    (T : Finset ℕ) (hT : T ⊆ range n) :
    ∃ I ⊆ T, (∀ i ∈ I, ∀ j ∈ I, i < j → a i < a j) ∧
      (∑ j ∈ T, Real.exp (-comparisonCost a n j)) ≤ (I.card : ℝ) := by
  sorry

/-- Paper result `lem:dr-labels`. -/
theorem dr_labels {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d : ℕ, 1 ≤ n → ∀ S : Finset ℕ,
      S ⊆ range n → (S.card : ℝ) ≤ α * n → ∀ h : ℕ → ℕ,
      (∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) →
      (n : ℝ) / c * Real.exp (-c * labelMass (range n \ S) h / n) ≤ d := by
  sorry

theorem valiant_depth_reduction {n Δ : ℕ} (hn : 2 ≤ n) (_hΔ : 2 ≤ Δ)
    {edge : Fin n → Fin n → Prop} (hordered : IsOrdered edge)
    (hdegree : IndegreeAtMost edge Δ) {k : ℕ} (hk : k < Nat.clog 2 n) :
    ∃ S : Finset (Fin n), S.card ≤ Δ * n * k / Nat.clog 2 n ∧
      DepthAtMost edge S (2 ^ (Nat.clog 2 n - k)) := by
  sorry

theorem balanced_robustness_optimality (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ edge : Fin n → Fin n → Prop, IsOrdered edge → IndegreeAtMost edge Δ →
      ∀ e b : ℕ, 1 ≤ e → 1 ≤ b → ∀ d : ℝ, 0 < d →
        GraphBlockDepthRobust edge e d b →
        min (e : ℝ) d ≤ C * n / (Real.logb 2 n / Real.logb 2 (Real.logb 2 n)) ∧
          (b : ℝ) < (n : ℝ) / e := by
  sorry

theorem conditional_multiscale {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ lambda : ℝ, 0 < lambda →
      ∀ p : PMF (LabelArray n),
      (∀ h ∈ p.support, ∀ S j, j ∉ S → 0 < h S j) → ConditionalHeightBound p lambda →
      labelProbability p (fun h => ∀ S : Finset (Fin n), (S.card : ℝ) ≤ α * n →
        (n : ℝ) / c * Real.exp (-c / lambda) ≤
          ((univ.filter (fun j => j ∉ S)).sup (h S) : ℕ)) ≥
        1 - Real.exp (-(2 - Real.log 3) * n) := by
  sorry
end ProofOfSpaceStatement

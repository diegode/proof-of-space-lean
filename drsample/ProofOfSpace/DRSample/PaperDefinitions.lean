import ProofOfSpace.DRSample.Statement
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Definitions for the current robustness section and appendix

Graphs use the topological order on `Fin n`. Paths count vertices, and the
empty path has length zero. The sampler definitions are in `Statement`.
-/
namespace ProofOfSpaceStatement
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

/-- Definition `def:fractional-dr`: both directional guarantees hold after
every allowed deletion, on the same graph. -/
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

/-- Reverse exactly `k` binary digits, using zero-based integer encodings. -/
def reverseBits (k v : ℕ) : ℕ :=
  ∑ i ∈ range k, (v / 2 ^ i % 2) * 2 ^ (k - 1 - i)

/-- The BRG overlay from BHKLXZ19, Definition 4. For `n = 2^k`, retain the
original graph on the first `n` vertices, add the full line on `2n` vertices,
and join the first layer to the second by reversal of `k` binary digits. -/
def bitReversalOverlay {n : ℕ} (edge : Fin n → Fin n → Prop)
    (u v : Fin (2 * n)) : Prop :=
  u.val + 1 = v.val ∨
  (∃ i j : Fin n, i.val = u.val ∧ j.val = v.val ∧ edge i j) ∨
  (u.val < n ∧ n ≤ v.val ∧ u.val = reverseBits (Nat.log 2 n) (v.val - n))

/-- Parallel black pebbling: only newly placed pebbles require parents in the
previous configuration. Retention and removal are unrestricted. -/
def ParallelPebbling {n : ℕ} (edge : Fin n → Fin n → Prop)
    (T : ℕ) (P : ℕ → Finset (Fin n)) : Prop :=
  P 0 = ∅ ∧ ∀ t < T, ∀ v ∈ P (t + 1), v ∉ P t → ∀ u, edge u v → u ∈ P t

/-- A lower bound for every pebbling reaching the last vertex, equivalently
for the minimum cumulative cost of reaching the sink of an ordered line DAG. -/
def ParallelCumulativeCostAtLeast {n : ℕ} (edge : Fin n → Fin n → Prop)
    (cost : ℝ) : Prop :=
  ∀ T P, ParallelPebbling edge T P →
    (∃ v : Fin n, v.val + 1 = n ∧ v ∈ P T) →
    cost ≤ (∑ t ∈ range (T + 1), ((P t).card : ℝ))

/-- The reciprocal-distance cost `c_j` in `lem:dr-subsequence`. -/
noncomputable def comparisonCost (a : ℕ → ℤ) (n j : ℕ) : ℝ :=
  (∑ i ∈ Ico 0 j, if a j ≤ a i then (1 : ℝ) / (j - i : ℕ) else 0) +
  ∑ i ∈ Ico (j + 1) n, if a i ≤ a j then (1 : ℝ) / (i - j : ℕ) else 0

/-- The inconsistency mass `w` in `lem:dr-labels`. -/
noncomputable def labelMass (U : Finset ℕ) (h : ℕ → ℕ) : ℝ :=
  ∑ j ∈ U, ∑ i ∈ U, if i < j ∧ h j ≤ h i then (1 : ℝ) / (j - i : ℕ) else 0

/-- Countably supported laws suffice for the joint tuple of all integer labels.
The labels for distinct deletion sets are on one common probability space. -/
abbrev LabelArray (n : ℕ) := Finset (Fin n) → Fin n → ℕ

noncomputable def labelProbability {n : ℕ} (p : PMF (LabelArray n))
    (event : LabelArray n → Prop) : ℝ :=
  (p.toOuterMeasure {h | event h}).toReal

def EarlierLabels {n : ℕ} (S : Finset (Fin n)) (j : Fin n)
    (past : Fin n → ℕ) (h : LabelArray n) : Prop :=
  ∀ i, i ∉ S → i < j → h S i = past i

/-- Equation `eq:dr-conditional-height`, written by multiplying through by
the positive probability of the tuple of earlier labels. -/
def ConditionalHeightBound {n : ℕ} (p : PMF (LabelArray n)) (lambda : ℝ) : Prop :=
  ∀ S j, j ∉ S → ∀ past : Fin n → ℕ,
    0 < labelProbability p (EarlierLabels S j past) → ∀ k : ℕ, 0 < k →
    labelProbability p (fun h => EarlierLabels S j past h ∧ h S j ≤ k) ≤
      Real.exp (-lambda * ∑ i ∈ univ.filter (fun i => i ∉ S ∧ i < j ∧ k ≤ past i),
        (1 : ℝ) / (j.val - i.val : ℕ)) * labelProbability p (EarlierLabels S j past)

end ProofOfSpaceStatement

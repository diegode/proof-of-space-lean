import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.List.Chain
import Mathlib.Probability.Distributions.Uniform

/-!
# Probabilistic latency hardness for the Chung-8 stack

This is the statement of record for the Palomar submission. It imports only Mathlib and
states the latency theorem for an explicit random Chung interlayer: eight independently
uniform perfect matchings on a layer of `n` vertices. One sampled interlayer is reused
between every consecutive pair of layers. This is sufficient because the latency proof
only needs the same deterministic expansion property at every layer.

The degree-eight expansion profile is an explicit rational Chung polygon. The theorem
does not assume that the sampled interlayer expands. Instead, it lifts any deterministic
consequence of that expansion to a conclusion whose failure probability is at most
`chung8FailureBound n`, the exact finite union bound for the sampled eight-tuple of
permutations. Filecoin-specific storage and pebbling assumptions belong in the
specialized latency corollary, not in this probabilistic construction theorem.
-/

namespace ProofOfSpaceStatement

open Finset Set
open scoped ENNReal

/-! ### The random Chung-8 interlayer -/

/-- Eight independently sampled perfect matchings between two `n`-vertex layers. -/
structure ChungInterlayer (n : ℕ) where
  perm : Fin 8 → Equiv.Perm (Fin n)
deriving Fintype

instance (n : ℕ) : Nonempty (ChungInterlayer n) :=
  ⟨⟨fun _ => Equiv.refl (Fin n)⟩⟩

namespace ChungInterlayer

/-- The uniform law on eight-tuples of permutations. -/
noncomputable def uniformLaw (n : ℕ) : PMF (ChungInterlayer n) :=
  PMF.uniformOfFintype (ChungInterlayer n)

end ChungInterlayer

/-- Probability assigned to a predicate by a probability mass function. -/
noncomputable def probabilityOf {A : Type*} (p : PMF A) (Q : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if Q a then p a else 0

/-- A finite event holds with failure probability at most `δ`. -/
def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (Q : A → Prop)
    (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p Q

/-! ### The finite-size Chung-8 expansion profile and exact failure bound -/

/-- The affine line through `(a,u)` and `(b,v)`. -/
noncomputable def chord (a u b v x : ℝ) : ℝ :=
  u + (v - u) / (b - a) * (x - a)

/-- The rational degree-eight expansion polygon used by the Filecoin specialization. -/
noncomputable def chung8Beta (x : ℝ) : ℝ :=
  min (chord 0 0 (5089 / 100000) (1 / 5) x)
    (min (chord (5089 / 100000) (1 / 5) (46 / 625) (1331 / 5000) x)
    (min (chord (46 / 625) (1331 / 5000) (74 / 625) (3031 / 8000) x)
    (min (chord (74 / 625) (3031 / 8000) (811 / 5000) (4663 / 10000) x)
    (min (chord (811 / 5000) (4663 / 10000) (571 / 2500) (1143 / 2000) x)
    (min (chord (571 / 2500) (1143 / 2000) (3201 / 10000) (6799 / 10000) x)
    (min (chord (3201 / 10000) (6799 / 10000) (857 / 2000) (1929 / 2500) x)
    (min (chord (857 / 2000) (1929 / 2500) (5337 / 10000) (4189 / 5000) x)
    (min (chord (5337 / 10000) (4189 / 5000) (4969 / 8000) (551 / 625) x)
    (min (chord (4969 / 8000) (551 / 625) (3669 / 5000) (579 / 625) x)
    (min (chord (3669 / 5000) (579 / 625) (4 / 5) (94911 / 100000) x)
      (chord (4 / 5) (94911 / 100000) 1 1 x)))))))))))

namespace ChungInterlayer

/-- Distinct predecessors reached from a set of children. -/
def neighborhood {n : ℕ} (P : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  T.biUnion fun v => Finset.univ.image fun j : Fin 8 => P.perm j v

/-- The deterministic Chung-8 expansion event. -/
def Expands {n : ℕ} (P : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n),
    chung8Beta ((T.card : ℝ) / n) * n ≤ (P.neighborhood T).card

end ChungInterlayer

/-- The largest neighbourhood size still counted as a failure for a `k`-set. -/
noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (chung8Beta ((k : ℝ) / n) * n) - 1 else 0

/-- The exact union-bound failure probability for a random Chung-8 interlayer. -/
noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ((∑ k ∈ Finset.Ico 1 (n + 1), n.choose k *
        (n.choose (chung8FailureProfile n k) *
          ((chung8FailureProfile n k).descFactorial k * Nat.factorial (n - k)) ^ 8) : ℕ) :
      ℝ≥0∞) /
    ((Nat.factorial n ^ 8 : ℕ) : ℝ≥0∞)


/-! ### Latency data used by the Filecoin specialization -/

/-- Within-layer edges and a static pebbling snapshot. Layers and vertical edges are
constructed below rather than supplied as assumptions. -/
structure LatencyData (ℓ : ℕ) where
  n : ℕ
  /-- The path fraction `α_π` produced by within-layer depth robustness. -/
  αpi : ℝ
  /-- The per-layer red-pebble budget `δ`, as a fraction of the layer width. -/
  δ : ℝ
  /-- The within-layer robustness threshold `π`: deleting at most `(1 - π) n` nodes of a
  layer still leaves an intra-layer path on `α_π n` surviving nodes. -/
  pi : ℝ
  /-- The total black-pebble budget `ρ = 1 - ε_space`, as a fraction of the layer width. -/
  ρ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def LatencyData.layer {ℓ : ℕ} (M : LatencyData ℓ) (d : ℕ) :
    Finset (ℕ × Fin M.n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin M.n => (d, i)) else ∅

def LatencyData.depth {ℓ : ℕ} (M : LatencyData ℓ) (v : ℕ × Fin M.n) : ℕ := v.1

def LatencyData.intraEdge {ℓ : ℕ} (M : LatencyData ℓ) (d : ℕ)
    (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d ∧ v.1 = d ∧ d < ℓ ∧ M.intra u.2 v.2

/-- Vertical edges supplied by the sampled eight-tuple of permutations. -/
def LatencyData.interEdge {ℓ : ℕ} (M : LatencyData ℓ)
    (P : ChungInterlayer M.n) (d : ℕ)
    (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d + 1 ∧ v.1 = d ∧ d + 1 < ℓ ∧
    ∃ j : Fin 8, u.2 = P.perm j v.2

def LatencyData.edge {ℓ : ℕ} (M : LatencyData ℓ) (P : ChungInterlayer M.n)
    (u v : ℕ × Fin M.n) : Prop :=
  (∃ d, M.intraEdge d u v) ∨ (∃ d, M.interEdge P d u v)

/-- The remaining literature-level inputs, after the Chung profile and vertical graph
construction have been made explicit. The numeric parameters they quantify over are
fields of `LatencyData`: the depth-robustness threshold `M.pi`, the per-layer red budget
`M.δ`, and the total black budget `M.ρ`. Filecoin's values for them are pinned in the
specialization below, not here. -/
class LiteratureHypotheses {ℓ : ℕ} (M : LatencyData ℓ) : Prop where
  intra_rank : ∀ {u v}, M.intra u v → u.val < v.val
  depth_robust : ∀ X : Finset (Fin M.n),
    ((X.card : ℝ) ≤ (1 - M.pi) * M.n) →
    ∃ p : List (Fin M.n), p ≠ [] ∧ p.IsChain M.intra ∧
      (∀ v ∈ p, v ∉ X) ∧ M.αpi * M.n ≤ (p.length : ℝ)
  black_subset : ∀ d, M.black d ⊆ M.layer d
  red_subset : ∀ d, M.red d ⊆ M.layer d
  black_total : ∀ m,
    ∑ d ∈ Finset.range m, ((M.black d).card : ℝ) / M.n ≤ M.ρ
  red_bound : ∀ d, ((M.red d).card : ℝ) ≤ M.δ * M.n
  n_pos : 0 < M.n

/-- The existence of an unpebbled dependency path of at least `L` nodes. -/
def LatencyEvent {ℓ : ℕ} (M : LatencyData ℓ) (A : Finset (ℕ × Fin M.n))
    (L : ℝ) (P : ChungInterlayer M.n) : Prop :=
  ∃ u a, a ∈ A ∧ ∃ Q : List (ℕ × Fin M.n),
    Q ≠ [] ∧ Q.IsChain (M.edge P) ∧
    (∀ v ∈ Q, v ∉ M.black (M.depth v) ∧ v ∉ M.red (M.depth v)) ∧
    Q.head? = some u ∧ Q.getLast? = some a ∧
    L ≤ (Q.length : ℝ)

/--
**Probabilistic Chung-8 latency lower bound.**

A uniformly sampled eight-tuple of permutations satisfies every deterministic consequence
of the Chung-8 expansion event with failure probability bounded by the exact finite union
bound `chung8FailureBound M.n`.
-/
theorem latency_chung8_whp
    {ℓ : ℕ} (M : LatencyData ℓ) (A : Finset (ℕ × Fin M.n)) (L : ℝ)
    (hdet : ∀ P : ChungInterlayer M.n, P.Expands → LatencyEvent M A L P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (LatencyEvent M A L) (chung8FailureBound M.n) := by
  sorry

/--
**The Filecoin 15-layer specialization.**

This is where the Filecoin values enter: the depth-robustness pair `π = 4/5`,
`α_π = 1/5`, the per-layer red budget `δ = 189/5000`, the black budget `ρ = 4/5`, and the
adjusted challenge weight `ζ_δ = 4311/5000` obtained from `ζ`, `ρ`, and `δ`. The theorem
uses the generic Chung-8 high-probability result above after proving deterministically
that expansion implies the displayed latency event.
-/
theorem chung8_latency_15
    (M : LatencyData 15) [LiteratureHypotheses M]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hαpi : M.αpi = (1 : ℝ) / 5)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hpi : M.pi = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hweight : (4311 : ℝ) / 5000 ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (LatencyEvent M A
        ((1 : ℝ) / 5 * M.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * M.n))
      (chung8FailureBound M.n) := by
  sorry

end ProofOfSpaceStatement

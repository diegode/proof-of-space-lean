import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Uniform

/-! # Latency amplification: public statement surface

Reyzin's `π`, `απ`, and challenge `S`, with gain defined at the chosen footprint size.
Proofs are in `Solution.lean` and `ProofOfSpace/`.
-/

namespace ProofOfSpaceStatement

open Finset Set
open scoped ENNReal

structure ChungInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)
deriving Fintype

instance (n : ℕ) : Nonempty (ChungInterlayer n) := ⟨⟨Equiv.refl _⟩⟩

namespace ChungInterlayer

noncomputable def uniformLaw (n : ℕ) : PMF (ChungInterlayer n) :=
  PMF.uniformOfFintype (ChungInterlayer n)

def ports {n : ℕ} (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

def neighborhood {n : ℕ} (p : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  (ports T).image fun q => (p.perm q).2

end ChungInterlayer

noncomputable def probabilityOf {A : Type*} (p : PMF A) (Q : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if Q a then p a else 0

def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (Q : A → Prop)
    (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p Q

/-- Reyzin's degree-eight union-bound exponent, in nats. -/
noncomputable def chungExponent8 (x y : ℝ) : ℝ :=
  Real.binEntropy x + Real.binEntropy y +
    8 * (y * Real.binEntropy (x / y) - Real.binEntropy x)

/-- A symmetric relative exponent margin. It is invariant under Chung's
anti-diagonal reflection `(x,y) ↦ (1-y,1-x)` and remains meaningful at every
interior pair. -/
noncomputable def chung8Level (x y : ℝ) : ℝ :=
  min (Real.binEntropy x) (Real.binEntropy y) / 2 ^ (23 : ℕ)

/-- The degree-eight Chung expansion function, defined directly by its entropy formula. -/
noncomputable def chung8Beta (x : ℝ) : ℝ :=
  if x = 1 then 1
  else sSup {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x y}

/-- The largest integer neighbourhood size still counted as a failure. -/
noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (chung8Beta ((k : ℝ) / n) * n) - 1 else 0

namespace ChungInterlayer

/-- Chung-8 expansion demanded only of source sets whose density lies in `[a, b]`.
The deterministic argument queries expansion at densities bounded away from zero, so
the assumption—and the union bound paying for it—need not cover vanishing densities,
where a Chung profile costs a birthday collision rather than an exponentially small
event. -/
def ExpandsOn {n : ℕ} (p : ChungInterlayer n) (a b : ℝ) : Prop :=
  ∀ T : Finset (Fin n), a ≤ (T.card : ℝ) / n → (T.card : ℝ) / n ≤ b →
    chung8FailureProfile n T.card < (p.neighborhood T).card

end ChungInterlayer

/-- The probability that all source ports land among the target ports. -/
noncomputable def chung8PortHitProb (n k m : ℕ) : ℝ≥0∞ :=
  ((8 * m).descFactorial (8 * k) : ℝ≥0∞) /
    ((8 * n).descFactorial (8 * k) : ℝ≥0∞)

/-- The exact port-model union bound for the functional Chung-8 profile, over the
source densities in `[a, b]`. -/
noncomputable def chung8FailureBound (n : ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b),
    (n.choose k : ℝ≥0∞) *
      ((n.choose (chung8FailureProfile n k) : ℝ≥0∞) *
        chung8PortHitProb n k (chung8FailureProfile n k))

/-- The exact Chung-8 union bound on `[a, b]` is at most two to the minus lambda. -/
class ChungSecurityConditions (n : ℕ) (lambda : ℕ) (a b : ℝ) : Prop where
  n_pos : 0 < n
  a_pos : 0 < a
  security : chung8FailureBound n a b ≤ (2 : ℝ≥0∞)⁻¹ ^ lambda

/-- A static black/red pebbling position and its latency parameters on an `ℓ`-layer
stacked graph of width `n`. The width is a parameter, not a field, so that one
probability space `ChungInterlayer n` serves every game. -/
structure PebblingGame (ℓ n : ℕ) where
  απ : ℝ
  π : ℝ
  δ : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

variable {ℓ n : ℕ}

def PebblingGame.layer (_G : PebblingGame ℓ n) (i : ℕ) : Finset (ℕ × Fin n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin n => (i, v)) else ∅

def PebblingGame.depth (_G : PebblingGame ℓ n) (v : ℕ × Fin n) : ℕ := v.1

def PebblingGame.intraEdge (G : PebblingGame ℓ n) (i : ℕ)
    (u v : ℕ × Fin n) : Prop :=
  u.1 = i ∧ v.1 = i ∧ i < ℓ ∧ G.intra u.2 v.2

def PebblingGame.interEdge (_G : PebblingGame ℓ n)
    (p : ChungInterlayer n) (i : ℕ) (u v : ℕ × Fin n) : Prop :=
  u.1 = i + 1 ∧ v.1 = i ∧ i + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin n)), (p.perm q).2 = u.2

def PebblingGame.edge (G : PebblingGame ℓ n) (p : ChungInterlayer n)
    (u v : ℕ × Fin n) : Prop :=
  (∃ i, G.intraEdge i u v) ∨ (∃ i, G.interEdge p i u v)

/-- Structural graph assumptions and pebble-budget constraints for an admissible game. -/
class PebblingGame.IsAdmissible (G : PebblingGame ℓ n) : Prop where
  intra_rank : ∀ {u v}, G.intra u v → u.val < v.val
  /-- Reyzin parameters: density `π` of survivors guarantees `απ * n` path vertices. -/
  depth_robust : ∀ X : Finset (Fin n), G.π * n ≤ (X.card : ℝ) →
    ∃ P : List (Fin n), P ≠ [] ∧ P.IsChain G.intra ∧
      (∀ v ∈ P, v ∈ X) ∧ G.απ * n ≤ (P.length : ℝ)
  black_subset : ∀ i, G.black i ⊆ G.layer i
  red_subset : ∀ i, G.red i ⊆ G.layer i
  black_total : ∀ m,
    ∑ i ∈ Finset.range m, ((G.black i).card : ℝ) / n ≤ G.ρ
  red_bound : ∀ i, ((G.red i).card : ℝ) ≤ G.δ * n
  n_pos : 0 < n

/-- The game has an unpebbled directed path of length at least `L` ending in `S`. -/
def PebblingGame.HasUnpebbledPathTo (G : PebblingGame ℓ n)
    (S : Finset (ℕ × Fin n))
    (L : ℝ) (p : ChungInterlayer n) : Prop :=
  ∃ v ∈ S, ∃ P : List (ℕ × Fin n),
    P ≠ [] ∧ P.IsChain (G.edge p) ∧
    (∀ w ∈ P, w ∉ G.black (G.depth w) ∧ w ∉ G.red (G.depth w)) ∧
    P.getLast? = some v ∧ L ≤ (P.length : ℝ)

/-- A latency event is uniform over admissible positions and challenges, both of
which may be chosen after observing the sampled wiring. -/
def PebblingGame.LatencyEvent (ℓ n : ℕ) (απ δ π ρ ζ L : ℝ)
    (p : ChungInterlayer n) : Prop :=
  ∀ G : PebblingGame ℓ n, G.απ = απ → G.δ = δ → G.π = π → G.ρ = ρ → G.ζ = ζ →
    PebblingGame.IsAdmissible G →
    ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 → ζ ≤ (S.card : ℝ) / n →
      G.HasUnpebbledPathTo S L p

-- Intentional statement placeholders, checked against Solution by Comparator.
set_option warn.sorry false

/-- Latency amplification. The gain `g` is defined at density `m/n`; the interval
hypothesis requires at least this gain at every queried density. -/
theorem pebbling_latency {ℓ n : ℕ} (W : ChungInterlayer n)
    (β : ℝ → ℝ) (απ π : ℝ) (m s z : ℕ) (δ ρ ζ : ℝ) :
    let σ := (s : ℝ) / n
    let g := β ((m : ℝ) / n) - δ - (m : ℝ) / n
    let I := Icc (min (ζ - δ) (β ((m : ℝ) / n) - δ) - ρ) ((m : ℝ) / n)
    let q := min (Nat.ceil (απ * n))
      (Nat.ceil (απ * n) + m + 1 - (Nat.ceil (π * n) + s))
    Nat.ceil (π * n) ≤ m → 1 ≤ q → 1 ≤ z → 0 < g →
    ρ < min (ζ - δ) (β ((m : ℝ) / n) - δ) → σ ∈ I →
    MonotoneOn β I → (∀ x ∈ I, g ≤ β x - δ - x) →
    2 * g ≤ β σ - δ - min (ζ - δ) (β ((m : ℝ) / n) - δ) + ρ →
    (∀ X : Finset (Fin n), (X.card : ℝ) / n ∈ I →
      β ((X.card : ℝ) / n) * n ≤ (W.neighborhood X).card) →
    ρ + g + max ((m : ℝ) / n - (ζ - δ)) (g + β ((m : ℝ) / n) - β σ) +
      ((z : ℝ) - 1) * (g + β ((m : ℝ) / n) - β σ) < g * ℓ →
    PebblingGame.LatencyEvent ℓ n απ δ π ρ ζ
      (Nat.ceil (απ * n) + ((z : ℝ) - 1) * q) W := by sorry

/-- The same latency theorem on one uniform Chung port permutation, simultaneously
for all admissible positions and challenge sets `S`. -/
theorem chung8_pebbling_latency_whp {ℓ n : ℕ} (lambda : ℕ) (u v : ℝ)
    [ChungSecurityConditions n lambda u v]
    (β : ℝ → ℝ) (απ π : ℝ) (m s z : ℕ) (δ ρ ζ : ℝ) :
    let σ := (s : ℝ) / n
    let g := β ((m : ℝ) / n) - δ - (m : ℝ) / n
    let I := Icc (min (ζ - δ) (β ((m : ℝ) / n) - δ) - ρ) ((m : ℝ) / n)
    let q := min (Nat.ceil (απ * n))
      (Nat.ceil (απ * n) + m + 1 - (Nat.ceil (π * n) + s))
    Nat.ceil (π * n) ≤ m → 1 ≤ q → 1 ≤ z → 0 < g →
    ρ < min (ζ - δ) (β ((m : ℝ) / n) - δ) → σ ∈ I → I ⊆ Icc u v →
    MonotoneOn β I → (∀ x ∈ I, g ≤ β x - δ - x) →
    2 * g ≤ β σ - δ - min (ζ - δ) (β ((m : ℝ) / n) - δ) + ρ →
    (∀ x ∈ I, β x ≤ chung8Beta x) →
    ρ + g + max ((m : ℝ) / n - (ζ - δ)) (g + β ((m : ℝ) / n) - β σ) +
      ((z : ℝ) - 1) * (g + β ((m : ℝ) / n) - β σ) < g * ℓ →
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n απ δ π ρ ζ
        (Nat.ceil (απ * n) + ((z : ℝ) - 1) * q))
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by sorry

/-- Eighteen layers give more than `0.2n` latency at the Filecoin parameters,
including finite-width rounding and the explicit Chung security assumption. -/
theorem chung8_pebbling_latency_18 (n lambda : ℕ) (hn : 10000 ≤ n)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent 18 n (1 / 5) (189 / 5000) (4 / 5) (4 / 5) (9 / 10)
        (41 / 200 * n)) ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by sorry

end ProofOfSpaceStatement

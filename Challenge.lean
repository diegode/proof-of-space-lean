import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung-8 pebbling latency: statement surface

The random interlayer is the model used by Reyzin: one uniform permutation of all
`8n` ports. This file contains only the definitions needed to state the generic
high-probability latency theorem and its 14-layer Filecoin specialization.

Both public theorems are *uniform*: the wiring is sampled first, and the event
whose probability is bounded quantifies over every admissible pebbling position
and every challenge set. The pebble sets are chosen with the wiring in hand, so
the game may not be fixed before the sample.
-/

namespace ProofOfSpaceStatement

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
class ChungSecurityConditions (n : ℕ) (lambda a b : ℝ) : Prop where
  n_pos : 0 < n
  a_pos : 0 < a
  security :
    chung8FailureBound n a b ≤ ENNReal.ofReal (Real.exp (-lambda * Real.log 2))

/-- A static black/red pebbling position and its latency parameters on an `ℓ`-layer
stacked graph of width `n`. The width is a parameter, not a field, so that one
probability space `ChungInterlayer n` serves every game. -/
structure PebblingGame (ℓ n : ℕ) where
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

variable {ℓ n : ℕ}

def PebblingGame.layer (_G : PebblingGame ℓ n) (i : ℕ) : Finset (ℕ × Fin n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin n => (i, v)) else ∅

def PebblingGame.depth (_G : PebblingGame ℓ n) (v : ℕ × Fin n) : ℕ := v.1

/-- The latency supplied by `z` completed links with source weight `sigma`. -/
def PebblingGame.latencyLength (G : PebblingGame ℓ n) (σ : ℝ) (z : ℕ) : ℝ :=
  G.απ * n + ((z : ℝ) - 1) * (G.απ - σ) * n

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
  depth_robust : ∀ X : Finset (Fin n),
    ((X.card : ℝ) ≤ (1 - G.π) * n) →
    ∃ P : List (Fin n), P ≠ [] ∧ P.IsChain G.intra ∧
      (∀ v ∈ P, v ∉ X) ∧ G.απ * n ≤ (P.length : ℝ)
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

/-- The latency conclusion, as an event on the sampled wiring: every admissible game
of these parameters and every challenge set of weight `ζ` in layer zero has an
unpebbled path of the stated length. -/
def PebblingGame.LatencyEvent (ℓ n z : ℕ) (απ δ π ρ ζ σ : ℝ)
    (p : ChungInterlayer n) : Prop :=
  ∀ G : PebblingGame ℓ n, G.απ = απ → G.δ = δ → G.π = π → G.ρ = ρ → G.ζ = ζ →
    PebblingGame.IsAdmissible G →
    ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 → ζ ≤ (S.card : ℝ) / n →
      G.HasUnpebbledPathTo S (G.latencyLength σ z) p

/-- The parameter tuples for which Chung-8 expansion on `[a, b]` deterministically
supplies `z` links. This is a semantic, proof-independent description of the covered
region: it quantifies over every wiring that expands and every admissible game with
the displayed fundamental parameters. -/
def Chung8LatencyRegion (ℓ n z : ℕ) (απ δ π ρ ζ σ a b : ℝ) : Prop :=
  σ < απ ∧
    ∀ p : ChungInterlayer n, p.ExpandsOn a b →
      PebblingGame.LatencyEvent ℓ n z απ δ π ρ ζ σ p

-- The public challenge theorem bodies are intentionally omitted; see `README.md`.
set_option warn.sorry false

/-- The high-probability Chung-8 latency theorem for every tuple in the semantic
latency region. All game parameters, the expansion range, and the certified link
count remain symbolic. -/
theorem chung8_pebbling_latency_whp
    {ℓ n : ℕ} (lambda a b : ℝ) [ChungSecurityConditions n lambda a b]
    (z : ℕ) (απ δ π ρ ζ σ : ℝ)
    (hregion : Chung8LatencyRegion ℓ n z απ δ π ρ ζ σ a b) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n z απ δ π ρ ζ σ)
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

/-- The 14-layer Filecoin latency lower bound at `lambda` bits of security: an
unpebbled path of length `0.2816 n`. -/
theorem chung8_pebbling_latency_14
    {n : ℕ} (lambda : ℝ) (hn : 1000 ≤ n)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun p : ChungInterlayer n =>
        ∀ G : PebblingGame 14 n,
          G.απ = (1 : ℝ) / 5 → G.δ = (189 : ℝ) / 5000 → G.π = (4 : ℝ) / 5 →
          G.ρ = (4 : ℝ) / 5 → G.ζ = (9 : ℝ) / 10 →
          PebblingGame.IsAdmissible G →
          ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 →
            (9 : ℝ) / 10 ≤ (S.card : ℝ) / n →
              G.HasUnpebbledPathTo S ((176 : ℝ) / 625 * n) p)
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

end ProofOfSpaceStatement

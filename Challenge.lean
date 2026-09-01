import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung-8 pebbling latency: statement surface

The random interlayer is the model used by Reyzin: one uniform permutation of all
`8n` ports. This file contains only the definitions needed to state the generic
high-probability latency theorem and its 15-layer Filecoin specialization.
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

def Expands {n : ℕ} (p : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty →
    chung8FailureProfile n T.card < (p.neighborhood T).card

end ChungInterlayer

/-- The probability that all source ports land among the target ports. -/
noncomputable def chung8PortHitProb (n k m : ℕ) : ℝ≥0∞ :=
  ((8 * m).descFactorial (8 * k) : ℝ≥0∞) /
    ((8 * n).descFactorial (8 * k) : ℝ≥0∞)

/-- The exact port-model union bound for the functional Chung-8 profile. -/
noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => 1 / (n : ℝ) ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1),
    (n.choose k : ℝ≥0∞) *
      ((n.choose (chung8FailureProfile n k) : ℝ≥0∞) *
        chung8PortHitProb n k (chung8FailureProfile n k))

/-- The exact Chung-8 union bound is at most two to the minus lambda. -/
class ChungSecurityConditions (n : ℕ) (lambda : ℝ) : Prop where
  n_pos : 0 < n
  security :
    chung8FailureBound n ≤ ENNReal.ofReal (Real.exp (-lambda * Real.log 2))

/-- A static black/red pebbling position and its latency parameters on an `ℓ`-layer
stacked graph. -/
structure PebblingGame (ℓ : ℕ) where
  n : ℕ
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (G : PebblingGame ℓ) (i : ℕ) :
    Finset (ℕ × Fin G.n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin G.n => (i, v)) else ∅

def PebblingGame.depth {ℓ : ℕ} (G : PebblingGame ℓ) (v : ℕ × Fin G.n) : ℕ := v.1

/-- The latency supplied by `z` completed links with source weight `sigma`. -/
def PebblingGame.latencyLength {ℓ : ℕ} (G : PebblingGame ℓ) (σ : ℝ) (z : ℕ) : ℝ :=
  G.απ * G.n + ((z : ℝ) - 1) * (G.απ - σ) * G.n

def PebblingGame.intraEdge {ℓ : ℕ} (G : PebblingGame ℓ) (i : ℕ)
    (u v : ℕ × Fin G.n) : Prop :=
  u.1 = i ∧ v.1 = i ∧ i < ℓ ∧ G.intra u.2 v.2

def PebblingGame.interEdge {ℓ : ℕ} (G : PebblingGame ℓ)
    (p : ChungInterlayer G.n) (i : ℕ) (u v : ℕ × Fin G.n) : Prop :=
  u.1 = i + 1 ∧ v.1 = i ∧ i + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin G.n)), (p.perm q).2 = u.2

def PebblingGame.edge {ℓ : ℕ} (G : PebblingGame ℓ) (p : ChungInterlayer G.n)
    (u v : ℕ × Fin G.n) : Prop :=
  (∃ i, G.intraEdge i u v) ∨ (∃ i, G.interEdge p i u v)

/-- Structural graph assumptions and pebble-budget constraints for an admissible game. -/
class PebblingGame.IsAdmissible {ℓ : ℕ} (G : PebblingGame ℓ) : Prop where
  intra_rank : ∀ {u v}, G.intra u v → u.val < v.val
  depth_robust : ∀ X : Finset (Fin G.n),
    ((X.card : ℝ) ≤ (1 - G.π) * G.n) →
    ∃ P : List (Fin G.n), P ≠ [] ∧ P.IsChain G.intra ∧
      (∀ v ∈ P, v ∉ X) ∧ G.απ * G.n ≤ (P.length : ℝ)
  black_subset : ∀ i, G.black i ⊆ G.layer i
  red_subset : ∀ i, G.red i ⊆ G.layer i
  black_total : ∀ m,
    ∑ i ∈ Finset.range m, ((G.black i).card : ℝ) / G.n ≤ G.ρ
  red_bound : ∀ i, ((G.red i).card : ℝ) ≤ G.δ * G.n
  n_pos : 0 < G.n

/-- The game has an unpebbled directed path of length at least `L` ending in `S`. -/
def PebblingGame.HasUnpebbledPathTo {ℓ : ℕ} (G : PebblingGame ℓ)
    (S : Finset (ℕ × Fin G.n))
    (L : ℝ) (p : ChungInterlayer G.n) : Prop :=
  ∃ u v, v ∈ S ∧ ∃ P : List (ℕ × Fin G.n),
    P ≠ [] ∧ P.IsChain (G.edge p) ∧
    (∀ w ∈ P, w ∉ G.black (G.depth w) ∧ w ∉ G.red (G.depth w)) ∧
    P.head? = some u ∧ P.getLast? = some v ∧ L ≤ (P.length : ℝ)

/-- The parameter tuples for which Chung-8 expansion deterministically supplies `z`
links. This is a semantic, proof-independent description of the covered region: it
quantifies over every admissible game with the displayed fundamental parameters. -/
def Chung8LatencyRegion (ℓ z : ℕ) (απ δ π ρ ζ σ : ℝ) : Prop :=
  σ < απ ∧
    ∀ (G : PebblingGame ℓ), G.απ = απ → G.δ = δ → G.π = π → G.ρ = ρ → G.ζ = ζ →
      PebblingGame.IsAdmissible G →
      ∀ (S : Finset (ℕ × Fin G.n)), S ⊆ G.layer 0 →
        G.ζ ≤ (S.card : ℝ) / G.n →
        ∀ p : ChungInterlayer G.n, p.Expands →
          G.HasUnpebbledPathTo S (G.latencyLength σ z) p

-- The public challenge theorem bodies are intentionally omitted; see `README.md`.
set_option warn.sorry false

/-- The high-probability Chung-8 latency theorem for every tuple in the semantic
latency region. All game parameters and the certified link count remain symbolic. -/
theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (lambda : ℝ) (G : PebblingGame ℓ)
    [PebblingGame.IsAdmissible G] [ChungSecurityConditions G.n lambda]
    (z : ℕ) (σ : ℝ)
    (hregion : Chung8LatencyRegion ℓ z G.απ G.δ G.π G.ρ G.ζ σ)
    (S : Finset (ℕ × Fin G.n)) (hS : S ⊆ G.layer 0)
    (hweight : G.ζ ≤ (S.card : ℝ) / G.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S (G.latencyLength σ z))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

/-- The 15-layer Filecoin latency lower bound at `lambda` bits of security. -/
theorem chung8_pebbling_latency_15
    (lambda : ℝ) (G : PebblingGame 15) [PebblingGame.IsAdmissible G]
    [ChungSecurityConditions G.n lambda]
    (S : Finset (ℕ × Fin G.n)) (hS : S ⊆ G.layer 0)
    (hαπ : G.απ = (1 : ℝ) / 5)
    (hδ : G.δ = (189 : ℝ) / 5000)
    (hπ : G.π = (4 : ℝ) / 5)
    (hρ : G.ρ = (4 : ℝ) / 5)
    (hζ : G.ζ = (9 : ℝ) / 10)
    (hweight : G.ζ ≤ (S.card : ℝ) / G.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S (G.latencyLength ((74 : ℝ) / 625) 2))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

end ProofOfSpaceStatement

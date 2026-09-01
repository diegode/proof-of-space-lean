import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung-8 pebbling latency: statement surface

The random interlayer is the model used by Reyzin: one uniform permutation of all
`8n` ports. This file contains only the definitions needed to state the generic
high-probability lifting theorem and its 15-layer Filecoin specialization.
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

noncomputable def chung8PebblingAlphaMin : ℝ := 961821 / 74555000
noncomputable def chung8PebblingAlphaMax : ℝ := 14155 / 14911
noncomputable def chung8AlphaMin : ℝ := chung8PebblingAlphaMin / 2
noncomputable def chung8AlphaMax : ℝ := 14533 / 14911
noncomputable def epsilonChung : ℝ := 1 / 2 ^ (22 : ℕ)
noncomputable def chung8Delta : ℝ := 189 / 10000
noncomputable def chung8DeltaN (n : ℕ) : ℝ := chung8Delta - 1 / n

/-- Reyzin's degree-eight fixed-pair exponent, in nats. -/
noncomputable def chungExponent8 (x y : ℝ) : ℝ :=
  Real.binEntropy x + Real.binEntropy y +
    8 * (y * Real.binEntropy (x / y) - Real.binEntropy x)

/-- An integer neighbourhood size admissible for the exponential union bound. -/
def chung8AdmissibleFailure (n k m : ℕ) : Prop :=
  k < m ∧ m < n ∧
  chung8AlphaMin ≤ 1 - (m : ℝ) / n ∧
  chung8DeltaN n ≤ (m : ℝ) / n - (k : ℝ) / n ∧
  chungExponent8 ((k : ℝ) / n) ((m : ℝ) / n) ≤
    -epsilonChung * Real.log 2

/-- The largest integer failure size certified directly by Reyzin's exponent and the
finite-grid margin conditions. -/
noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  by classical exact ((Finset.range n).filter (chung8AdmissibleFailure n k)).sup id

namespace ChungInterlayer

def Expands {n : ℕ} (p : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n),
    chung8AlphaMin ≤ (T.card : ℝ) / n →
    (T.card : ℝ) / n ≤ chung8AlphaMax →
    chung8FailureProfile n T.card < (p.neighborhood T).card

end ChungInterlayer

/-- The simplified expansion-failure bound, with `ε_chung` measured in bits. -/
noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (1 / 8) /
        (2 * Real.pi * chung8AlphaMin * Real.sqrt (chung8DeltaN n)) *
      Real.exp (-(n : ℝ) * epsilonChung * Real.log 2))

/-- Positivity and one-grid-step conditions required by the finite-size profile. -/
class ChungExpansionConditions (n : ℕ) : Prop where
  n_pos : 0 < n
  delta_pos : 0 < chung8DeltaN n
  grid_buffer : 1 / (n : ℝ) ≤ chung8AlphaMax - chung8PebblingAlphaMax

/-- Reyzin's sufficient graph-width condition for `lambda` bits of security. -/
class ChungSecurityConditions (n : ℕ) (lambda : ℝ) : Prop
    extends ChungExpansionConditions n where
  security :
    (lambda - 12 / 5 - Real.logb 2 chung8AlphaMin -
      Real.logb 2 (chung8DeltaN n) / 2) / epsilonChung < n

/-- A static black/red pebbling position on an `ℓ`-layer stacked graph. -/
structure PebblingGame (ℓ : ℕ) where
  n : ℕ
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (G : PebblingGame ℓ) (i : ℕ) :
    Finset (ℕ × Fin G.n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin G.n => (i, v)) else ∅

def PebblingGame.depth {ℓ : ℕ} (G : PebblingGame ℓ) (v : ℕ × Fin G.n) : ℕ := v.1

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

-- The public challenge theorem bodies are intentionally omitted; see `README.md`.
set_option warn.sorry false

/-- Certified Chung expansion lifts a deterministic pebbling conclusion to high probability. -/
theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (G : PebblingGame ℓ) [ChungExpansionConditions G.n]
    (S : Finset (ℕ × Fin G.n)) (L : ℝ)
    (hdet : ∀ p : ChungInterlayer G.n, p.Expands → G.HasUnpebbledPathTo S L p) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S L) (chung8FailureBound G.n) := by
  sorry

/-- The 15-layer Filecoin latency lower bound at `lambda` bits of security. -/
theorem chung8_pebbling_latency_15
    (lambda : ℝ) (G : PebblingGame 15) [PebblingGame.IsAdmissible G]
    [ChungSecurityConditions G.n lambda]
    (S : Finset (ℕ × Fin G.n)) (hS : S ⊆ G.layer 0)
    (hred : ∀ v ∈ S, v ∉ G.red 0)
    (hαπ : G.απ = (1 : ℝ) / 5)
    (hδ : G.δ = (189 : ℝ) / 5000)
    (hπ : G.π = (4 : ℝ) / 5)
    (hρ : G.ρ = (4 : ℝ) / 5)
    (hweight : (4311 : ℝ) / 5000 ≤ (S.card : ℝ) / G.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S
        ((1 : ℝ) / 5 * G.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * G.n))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

end ProofOfSpaceStatement

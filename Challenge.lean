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

/-- The relative exponent level, meaningful at every interior density. -/
noncomputable def chung8Level (x : ℝ) : ℝ :=
  Real.binEntropy x / 2 ^ (23 : ℕ)

/-- The degree-eight Chung expansion function, defined directly by its entropy formula. -/
noncomputable def chung8Beta (x : ℝ) : ℝ :=
  if x = 1 then 1
  else sSup {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x}

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
  σ : ℝ
  ζδ : ℝ
  αg : ℝ
  αmin : ℝ
  αmax : ℝ
  mid : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (G : PebblingGame ℓ) (i : ℕ) :
    Finset (ℕ × Fin G.n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin G.n => (i, v)) else ∅

def PebblingGame.depth {ℓ : ℕ} (G : PebblingGame ℓ) (v : ℕ × Fin G.n) : ℕ := v.1

/-- The latency supplied by `z` completed links of the chain construction. -/
def PebblingGame.latencyLength {ℓ : ℕ} (G : PebblingGame ℓ) (z : ℕ) : ℝ :=
  G.απ * G.n + ((z : ℝ) - 1) * (G.απ - G.σ) * G.n

/-- The non-chain overhead and link count from the minimum-link definition in
`thm:latency`, specialized only to the fixed Chung-8 curve. -/
noncomputable def PebblingGame.latencyConstants {ℓ : ℕ} (G : PebblingGame ℓ) : ℕ × ℕ :=
  let gainD := fun x ↦ chung8Beta x - G.δ - x
  let betaD := fun x ↦ chung8Beta x - G.δ
  let gpi := gainD G.π
  let piBar := 1 - chung8Beta G.π
  let zetaFloor := G.ζδ - G.ρ
  let gtilde := min (gainD zetaFloor) gpi
  let sigmaHat := min G.σ (1 - chung8Beta G.σ)
  let lam := min piBar sigmaHat
  let ghat := min gpi (gainD G.σ / 2)
  let infertileCap := fun h ↦ Nat.ceil ((G.ρ - (G.ζδ - G.π)) / h)
  let blockedCap := fun g ↦ Nat.ceil (G.ρ / g) - 1
  let sCap := infertileCap gtilde + blockedCap ghat
  let growthSpan := fun x ↦ max 1 ⌊(G.π - G.σ + x) / ghat⌋₊
  let asymptoticGrowth := max 1 ((G.π - G.σ) / ghat)
  let growthPot := fun split v ↦
    (min v split - G.σ) / (2 * ghat) + (max v split - split) / ghat
  let growthConst := min asymptoticGrowth (growthPot G.mid G.π + 1)
  let h₁ := growthConst + 1
  let ledgerSlack := 2 * G.ρ / ghat
  let gmin := min ghat gtilde
  let jointSlack := 2 * G.ρ / gmin
  let searchHead := max 0 (1 + (G.π - G.ζδ) / gtilde)
  let spendCap := ⌈G.ρ / ghat⌉₊
  let growthCap := growthSpan G.ρ
  let h₀ := growthCap + 2 * spendCap
  let bMax := blockedCap (betaD G.π - lam)
  let s₀ := sCap + bMax * h₀
  let jointEntry :=
    if bMax = 0 then ⌈((ℓ : ℝ) - searchHead - jointSlack) / h₁⌉₊ else 0
  let z := max 1 (max
    ⌈((ℓ : ℝ) - sCap - ledgerSlack - bMax * h₁) / (((bMax : ℝ) + 1) * h₁)⌉₊
    (max jointEntry ((ℓ - s₀) / ((bMax + 1) * h₀) + 1)))
  (s₀, z)

noncomputable def PebblingGame.latencyOverhead {ℓ : ℕ} (G : PebblingGame ℓ) : ℕ :=
  G.latencyConstants.1

noncomputable def PebblingGame.latencyLinks {ℓ : ℕ} (G : PebblingGame ℓ) : ℕ :=
  G.latencyConstants.2

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

/-- The scalar and tracking assumptions of `thm:latency`, for the fixed Chung-8 curve. -/
class ChungLatencyConditions {ℓ : ℕ} (G : PebblingGame ℓ) : Prop where
  beta_maps : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → chung8Beta x ∈ Set.Icc (0 : ℝ) 1
  beta_zero : chung8Beta 0 = 0
  beta_mono : StrictMonoOn chung8Beta (Set.Icc (0 : ℝ) 1)
  beta_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) chung8Beta
  beta_expands : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → x < chung8Beta x
  beta_reversal : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 →
    chung8Beta (1 - chung8Beta x) = 1 - x
  alphaG_mem : G.αg ∈ Set.Ioo (0 : ℝ) 1
  alphaG_max : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → x ≠ G.αg →
    chung8Beta x - x < chung8Beta G.αg - G.αg
  delta_nonneg : 0 ≤ G.δ
  rho_pos : 0 < G.ρ
  pi_mem : G.π ∈ Set.Ioo (0 : ℝ) 1
  alphaG_lt_pi : G.αg < G.π
  gpi_pos : 0 < chung8Beta G.π - G.δ - G.π
  alphaMin_mem : G.αmin ∈ Set.Icc (0 : ℝ) G.αg
  alphaMax_mem : G.αmax ∈ Set.Icc G.αg 1
  gain_min : chung8Beta G.αmin - G.δ - G.αmin = 0
  gain_max : chung8Beta G.αmax - G.δ - G.αmax = 0
  sigma_gt : G.αmin < G.σ
  sigma_lt : G.σ < G.π
  mid_ge : G.σ ≤ G.mid
  mid_le : G.mid ≤ G.π
  mid_gain : 2 * min (chung8Beta G.π - G.δ - G.π)
      ((chung8Beta G.σ - G.δ - G.σ) / 2) ≤
    chung8Beta G.mid - G.δ - G.mid
  entry : G.αmin < G.ζδ - G.ρ
  zeta_le : G.ζδ ≤ G.αmax
  sigma_lt_alphaPi : G.σ < G.απ
  inside : G.latencyOverhead < ℓ

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

/-- The Chung-8 high-probability form of `thm:latency`. -/
theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (lambda : ℝ) (G : PebblingGame ℓ)
    [PebblingGame.IsAdmissible G] [ChungSecurityConditions G.n lambda]
    [ChungLatencyConditions G]
    (S : Finset (ℕ × Fin G.n)) (hS : S ⊆ G.layer 0)
    (hred : ∀ v ∈ S, v ∉ G.red 0)
    (hweight : G.ζδ ≤ (S.card : ℝ) / G.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S (G.latencyLength G.latencyLinks))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
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
    (hσ : G.σ = (74 : ℝ) / 625)
    (hζδ : G.ζδ = (4311 : ℝ) / 5000)
    (hweight : G.ζδ ≤ (S.card : ℝ) / G.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw G.n)
      (G.HasUnpebbledPathTo S (G.latencyLength 2))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  sorry

end ProofOfSpaceStatement

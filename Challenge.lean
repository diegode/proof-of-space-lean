import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung-8 pebbling latency: statement surface

The random interlayer is the model used by Reyzin: one uniform permutation of all
`8n` ports. This file contains only the definitions needed to state the two generic
high-probability latency theorems and their Filecoin specializations.

`chung8_pebbling_latency_whp` prices a chosen number of chain links and its
14-layer instance `chung8_pebbling_latency_14` gives `0.2816 n`;
`chung8_pebbling_latency_full_asymptotic` eliminates the link count in favour of a
slope in the layer count, and its instance `chung8_pebbling_latency_asymptotic`
gives `0.0425 (ℓ - 21.2) n` for every `ℓ ≥ 22`. The generic pair differs only in the
robustness threshold `π` at which `IsAdmissible.depth_robust` is read and in the
payoff per link; neither implies the other.

All four public theorems are *uniform*: the wiring is sampled first, and the event
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
class ChungSecurityConditions (n : ℕ) (lambda : ℕ) (a b : ℝ) : Prop where
  n_pos : 0 < n
  a_pos : 0 < a
  security : chung8FailureBound n a b ≤ (2 : ℝ≥0∞)⁻¹ ^ lambda

/-! ### Expansion profiles

The deterministic argument runs on any expansion profile with the properties below.  They
are the expansion calculus of the analysis: the profile maps the unit interval to itself,
fixes `0`, is strictly increasing, concave and expanding, satisfies Chung's reversal law,
has a unique gain maximiser `αg`, and has the two zeros of the adjusted gain
`gain_δ(x) = β(x) - δ - x` as `αmin` and `αmax`.  Only `le_chung8` mentions the sampled
wiring: it is what makes the profile realizable by the uniform port permutation, and it
is why the degree-eight failure bound pays for the event. -/
structure ExpansionProfile where
  /-- The expansion function of the vertical edges. -/
  β : ℝ → ℝ
  /-- The red-pebble fraction the profile is certified at. -/
  δ : ℝ
  /-- The intra-layer robustness threshold. -/
  π : ℝ
  /-- The unique maximiser of the gain `β - id`. -/
  αg : ℝ
  /-- The low zero of the adjusted gain. -/
  αmin : ℝ
  /-- The high zero of the adjusted gain. -/
  αmax : ℝ
  β_maps : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → β x ∈ Set.Icc (0 : ℝ) 1
  β_zero : β 0 = 0
  β_strictMonoOn : StrictMonoOn β (Set.Icc (0 : ℝ) 1)
  β_concaveOn : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) β
  β_expands : ∀ ⦃x⦄, x ∈ Set.Ioo (0 : ℝ) 1 → x < β x
  β_reversal : ∀ ⦃x⦄, x ∈ Set.Ioo (0 : ℝ) 1 → β (1 - β x) = 1 - x
  αg_mem : αg ∈ Set.Ioo (0 : ℝ) 1
  αg_max : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → x ≠ αg → β x - x < β αg - αg
  δ_nonneg : 0 ≤ δ
  π_mem : π ∈ Set.Ioo (0 : ℝ) 1
  αg_lt_π : αg < π
  /-- `δ` is small enough that the fertile gain `g_π` is positive. -/
  gpi_pos : 0 < β π - δ - π
  αmin_mem : αmin ∈ Set.Icc (0 : ℝ) αg
  αmax_mem : αmax ∈ Set.Icc αg 1
  gainD_αmin : β αmin - δ - αmin = 0
  gainD_αmax : β αmax - δ - αmax = 0
  /-- The sampled degree-eight wiring realizes the profile. -/
  le_chung8 : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → β x ≤ chung8Beta x

namespace ExpansionProfile

variable (E : ExpansionProfile)

/-- `gain_δ(x) = β(x) - δ - x`. -/
def gainD (x : ℝ) : ℝ := E.β x - E.δ - x

/-- `β_δ(x) = β(x) - δ`, one level of growth against a full red layer. -/
def betaD (x : ℝ) : ℝ := E.β x - E.δ

/-- `g_π = gain_δ(π)`, the gain at the fertility threshold. -/
def gpi : ℝ := E.gainD E.π

/-- `π̄ = 1 - β(π)`, the lower member of the equal-gain mirror pair. -/
def piBar : ℝ := 1 - E.β E.π

/-- `π̂ = min{π̄, σ, 1 - β(σ)}`: the weight a tracked source cannot be pushed below. -/
noncomputable def floor (σ : ℝ) : ℝ := min E.piBar (min σ (1 - E.β σ))

/-- `ĝ = min{g_π, gain_δ(σ)/2}`: the gain the tracking argument runs at. -/
noncomputable def trackingGain (σ : ℝ) : ℝ := min E.gpi (E.gainD σ / 2)

end ExpansionProfile

/-! ### Certified level budgets

A level budget is a reference trajectory for the profile together with the certificate
that prices one step of the search along it.  The trajectory is a finite increasing
sequence from the tracking floor to the fertility threshold, each step within one free
level of growth and each bucket at least `ĝ` wide; `refPotOf` interpolates it, measuring
in levels how far a weight has climbed.  The certificate turns that into the three prices
the layer count is spent on. -/

/-- The piecewise-linear interpolation of `x k ↦ k`: how many free levels of the
trajectory the weight `v` has already covered. -/
noncomputable def refPotOf (m : ℕ) (x : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, max 0 (min 1 ((v - x k) / (x (k + 1) - x k)))

/-- A **certified level budget** for the profile `E` at source weight `σ`, valid for black
weights up to `ρmax`. -/
structure LevelBudget (E : ExpansionProfile) (σ : ℝ) where
  /-- The largest black weight the blocked-range clauses are certified for. -/
  ρmax : ℝ
  σ_gt : E.αmin < σ
  σ_lt : σ < E.π
  /-- A doubled-gain midpoint: `gain_δ ≥ 2 ĝ` still holds there, and concavity spreads it
  over `[σ, mid]`. -/
  mid : ℝ
  mid_ge : σ ≤ mid
  mid_le : mid ≤ E.π
  mid_gain : 2 * E.trackingGain σ ≤ E.gainD mid
  /-- The number of buckets of the reference trajectory. -/
  m : ℕ
  /-- Its points. -/
  x : ℕ → ℝ
  m_pos : 0 < m
  base : x 0 ≤ E.floor σ
  width : ∀ k, k < m → E.trackingGain σ ≤ x (k + 1) - x k
  step : ∀ k, k < m → x (k + 1) ≤ E.betaD (x k)
  mem : ∀ k, k ≤ m → x k ∈ Set.Icc (0 : ℝ) 1
  top : E.π ≤ x m
  /-- Levels charged per unit of black weight, in units of `1/ĝ`. -/
  lam : ℝ
  /-- Bound on the potential a subfertile weight is short of saturation. -/
  loss : ℝ
  /-- The expandability slack the search runs at. -/
  cs : ℝ
  /-- The width of the top bucket. -/
  wtop : ℝ
  /-- The top-bucket chord slope of `β_δ`, per unit of potential. -/
  kappa : ℝ
  /-- Slope and offset of the blocked-range drop. -/
  a2 : ℝ
  b2 : ℝ
  one_le_lam : 1 ≤ lam
  loss_nonneg : 0 ≤ loss
  one_le_cs : 1 ≤ cs
  wtop_pos : 0 < wtop
  kappa_nonneg : 0 ≤ kappa
  loss_ge : ∀ v, x 0 ≤ v → v ≤ E.π → refPotOf m x v - ((m : ℝ) - 1) ≤ loss
  topLip : ∀ u v : ℝ, x m ≤ u → v ≤ u →
    refPotOf m x u - refPotOf m x v ≤ (u - v) / wtop
  chord : ∀ v : ℝ, x (m - 1) ≤ v → v ≤ E.π →
    x m + kappa * (refPotOf m x v - ((m : ℝ) - 1)) ≤ E.betaD v
  ghat_le_lam_wtop : E.trackingGain σ ≤ lam * wtop
  inf_rate : ∀ θ s : ℝ, 0 ≤ θ → θ ≤ loss → 0 ≤ s →
    (x m - E.π) + kappa * θ ≤ s → θ + (s - kappa * θ) / wtop ≤ lam * s / E.trackingGain σ
  blockDrop : ∀ y : ℝ, (1 + cs) * E.trackingGain σ ≤ y → y ≤ ρmax →
    ((m : ℝ)) - refPotOf m x (E.betaD E.π - y) ≤ a2 * y + b2
  blockDrop_one : ∀ y : ℝ, (1 + cs) * E.trackingGain σ ≤ y → 1 ≤ a2 * y + b2
  blk_rate : ∀ y w : ℝ, (1 + cs) * E.trackingGain σ ≤ y → y ≤ ρmax → 0 ≤ w →
    (y / E.trackingGain σ - cs + 1) + (a2 * y + b2 - 1) + w / E.trackingGain σ
      ≤ -loss + lam * (y + w) / E.trackingGain σ

namespace LevelBudget

variable {E : ExpansionProfile} {σ : ℝ} (L : LevelBudget E σ)

/-- What the initial search costs, in layers, at red-free challenge weight `w`. -/
noncomputable def searchCost (w : ℝ) : ℝ := ((L.m : ℝ) - refPotOf L.m L.x w) + L.loss

/-- What one further chain link costs, in layers. -/
noncomputable def linkCost : ℝ := ((L.m : ℝ) - refPotOf L.m L.x σ) + L.loss

/-- What one unit of black-pebble weight costs, in layers. -/
noncomputable def chargeRate : ℝ := L.lam / E.trackingGain σ

end LevelBudget

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

-- The public challenge theorem bodies are intentionally omitted; see `README.md`.
set_option warn.sorry false

/-- **The latency theorem for any expansion profile with a certified level budget.**

The wiring is sampled first, and the event quantifies over every admissible game with the
displayed parameters and every challenge set of weight `ζ`.  Nothing about the degree-eight
Chung construction enters except through `E.le_chung8`, which is what the union bound pays
for; everything else is a property of the profile `E` and of the level budget `L`.

The parameters are tied together only by relations among themselves: the red fraction and
the robustness threshold must be within what the profile is certified for, the challenge
weight must clear the tracking floor after the whole black budget is spent and stay inside
the active interval, the source weight must clear the expandability slack, and the layer
count must cover

    `L.searchCost (ζ - δ) + (z - 1) · L.linkCost + L.chargeRate · ρ < ℓ`,

the initial search, one further chain link, and the black weight, each priced in layers by
the budget. -/
theorem chung8_pebbling_latency_whp
    {ℓ n : ℕ} (lambda : ℕ) (a b : ℝ) [ChungSecurityConditions n lambda a b]
    (E : ExpansionProfile) (σ : ℝ) (L : LevelBudget E σ)
    (απ δ π ρ ζ : ℝ) (z : ℕ) (hz : 1 ≤ z)
    (ha : a ≤ E.αmin) (hb : E.αmax + 1 / n ≤ b)
    (hδ : δ ≤ E.δ) (hπ : π ≤ E.π)
    (hρ : 0 ≤ ρ) (hρtop : ρ ≤ L.ρmax)
    (hentry : E.piBar + ρ < ζ - δ) (hζ : ζ - δ ≤ E.αmax)
    (hnobreak : ρ < E.betaD E.π - E.floor σ)
    (hslack : E.floor σ + (L.cs - 1) * E.trackingGain σ ≤ σ)
    (hσαπ : σ < απ)
    (hlevels : L.searchCost (ζ - δ) + ((z : ℝ) - 1) * L.linkCost
      + L.chargeRate * ρ < (ℓ : ℝ)) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n z απ δ π ρ ζ σ)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  sorry

/-- The 14-layer Filecoin latency lower bound at `lambda` bits of security: an
unpebbled path of length `0.2816 n`.  It is the point
`(απ, δ, π, ρ, ζ, σ, z, ℓ) = (0.2, 0.0378, 0.8, 0.8, 0.9, 0.1184, 2, 14)`
of `chung8_pebbling_latency_whp`, whose level condition there reads `13.928 < 14`. -/
theorem chung8_pebbling_latency_14
    {n : ℕ} (lambda : ℕ) (hn : 1000 ≤ n)
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
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  sorry

/-- **The asymptotic latency theorem, at full link payoff.**

The same probability event, the same certified level budget and the same three prices as
`chung8_pebbling_latency_whp`.  Two things change.

The graph hypothesis is stronger: the game's robustness threshold must clear the
profile's by the source weight, `π + σ ≤ E.π`.  `IsAdmissible.depth_robust` is the same
deletion-form statement as before — it is read at a smaller `π`, so it demands a path of
length `απ n` after `(1 - π) n` nodes are deleted rather than after `(1 - E.π) n`.

In exchange every completed chain link contributes a whole `απ n` instead of
`(απ - σ) n`.  A footprint of weight `E.π` then contains `σ n` distinct nodes that each
*begin* a path of length `απ n` inside it, so the source of a link no longer consists of
prefix nodes carrying only the suffix behind them.  The path length is therefore linear
in the layer count, with slope `απ / L.linkCost`: there is no link count to choose, and
no `σ < απ` to assume.  The level condition is what is left of the one above after the
link count is eliminated,

    `L.searchCost (ζ - δ) + L.chargeRate · ρ < ℓ`,

the initial search and the whole black budget, each priced in layers by the budget. -/
theorem chung8_pebbling_latency_full_asymptotic
    {ℓ n : ℕ} (lambda : ℕ) (a b : ℝ) [ChungSecurityConditions n lambda a b]
    (E : ExpansionProfile) (σ : ℝ) (L : LevelBudget E σ)
    (απ δ π ρ ζ : ℝ)
    (ha : a ≤ E.αmin) (hb : E.αmax + 1 / n ≤ b)
    (hδ : δ ≤ E.δ) (hπ : π + σ ≤ E.π)
    (hρ : 0 ≤ ρ) (hρtop : ρ ≤ L.ρmax)
    (hentry : E.piBar + ρ < ζ - δ) (hζ : ζ - δ ≤ E.αmax)
    (hnobreak : ρ < E.betaD E.π - E.floor σ)
    (hslack : E.floor σ + (L.cs - 1) * E.trackingGain σ ≤ σ)
    (hαπ : 0 ≤ απ) (hspan : 0 < L.linkCost)
    (hlevels : L.searchCost (ζ - δ) + L.chargeRate * ρ < (ℓ : ℝ)) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun p : ChungInterlayer n =>
        ∀ G : PebblingGame ℓ n, G.απ = απ → G.δ = δ → G.π = π → G.ρ = ρ → G.ζ = ζ →
          PebblingGame.IsAdmissible G →
          ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 → ζ ≤ (S.card : ℝ) / n →
            G.HasUnpebbledPathTo S
              (((ℓ : ℝ) - L.searchCost (ζ - δ) - L.chargeRate * ρ) / L.linkCost
                * απ * n) p)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  sorry

/-- The asymptotic Filecoin latency lower bound at `lambda` bits of security, **at
Filecoin's own robustness threshold**: an unpebbled path of length
`0.0425 (ℓ - 21.2) n`, at every layer count from twenty-two on.  It is the point
`(απ, δ, π, ρ, ζ, σ) = (0.2, 0.0378, 0.8, 0.8, 0.9, 0.0886)` of
`chung8_pebbling_latency_full_asymptotic`, whose level condition there reads
`21.1249 < ℓ`.

`IsAdmissible.depth_robust` is read here at the same `π = 4/5` as
`chung8_pebbling_latency_14`: deleting any `0.2 n` nodes of a layer must still leave an
intra-layer path on `0.2 n` nodes.  The two theorems make the *same* graph assumption, so
this one is a genuine strengthening for large `ℓ` — the bound grows by `0.0425 n` per
layer against `0.02135 n`, 1.99 times the slope.  What pays for it is the profile's
fertility threshold, raised from `4/5` to `0.8886` so that `π + σ` meets it: a footprint
of that weight contains `0.0886 n` nodes that each begin a whole `0.2 n` path, by depth
robustness at `4/5`.  The price is a larger head, `21.2` against `10.09`, because the
raised threshold lowers the tracking gain from `0.11131` to `0.04525`; the bound passes
`0.2 n` at `ℓ = 26`, first passes the `z`-link bound of `chung8_pebbling_latency_14` at
`ℓ = 40`, and is ahead of it at every layer count from `ℓ = 42` on. -/
theorem chung8_pebbling_latency_asymptotic
    {ℓ n : ℕ} (lambda : ℕ) (hn : 1000 ≤ n) (hℓ : 22 ≤ ℓ)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun p : ChungInterlayer n =>
        ∀ G : PebblingGame ℓ n,
          G.απ = (1 : ℝ) / 5 → G.δ = (189 : ℝ) / 5000 → G.π = (4 : ℝ) / 5 →
          G.ρ = (4 : ℝ) / 5 → G.ζ = (9 : ℝ) / 10 →
          PebblingGame.IsAdmissible G →
          ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 →
            (9 : ℝ) / 10 ≤ (S.card : ℝ) / n →
              G.HasUnpebbledPathTo S
                ((17 : ℝ) / 400 * ((ℓ : ℝ) - 106 / 5) * n) p)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  sorry

end ProofOfSpaceStatement

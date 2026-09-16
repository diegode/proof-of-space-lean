import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-! # Latency amplification for a static black/red pebbling position

The only advertised theorem is `pebbling_latency`. It derives a long unpebbled
path from ordinary within-layer depth robustness, interval expansion, and
pebble budgets. Path lengths count vertices. Its definitions are repeated in
the proof development so this statement imports Mathlib alone.
-/

namespace ProofOfSpaceStatement
open Finset Set

/-- A permutation wiring the eight ports at each vertex between adjacent layers. -/
structure ChungInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)

namespace ChungInterlayer

/-- The eight ports attached to every vertex in a set. -/
def ports {n : ℕ} (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

/-- Vertices reached by applying the port permutation to this set. -/
def neighborhood {n : ℕ} (p : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  (ports T).image fun q => (p.perm q).2

end ChungInterlayer

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

/-- The vertices in layer `i`, or the empty set outside the stack. -/
def PebblingGame.layer (_G : PebblingGame ℓ n) (i : ℕ) : Finset (ℕ × Fin n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin n => (i, v)) else ∅

/-- The layer index of a vertex. -/
def PebblingGame.depth (_G : PebblingGame ℓ n) (v : ℕ × Fin n) : ℕ := v.1

/-- An edge inside layer `i` of the stack. -/
def PebblingGame.intraEdge (G : PebblingGame ℓ n) (i : ℕ)
    (u v : ℕ × Fin n) : Prop :=
  u.1 = i ∧ v.1 = i ∧ i < ℓ ∧ G.intra u.2 v.2

/-- An edge from layer `i+1` to layer `i`, prescribed by the port wiring. -/
def PebblingGame.interEdge (_G : PebblingGame ℓ n)
    (p : ChungInterlayer n) (i : ℕ) (u v : ℕ × Fin n) : Prop :=
  u.1 = i + 1 ∧ v.1 = i ∧ i + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin n)), (p.perm q).2 = u.2

/-- The union of within-layer edges and port-wired interlayer edges. -/
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

/-- Linear interpolation along a finite free trajectory. Only the interval
between the first and final knots is used. -/
noncomputable def referenceScale (y : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | t + 1, x => if x ≤ y 1 then (x - y 0) / (y 1 - y 0)
      else 1 + referenceScale (fun i => y (i + 1)) t x

/-- Reference-trajectory latency with explicit accounting for repairs.
`a` is the band floor and `t` is its free fertility time. The correction
`max 0 (rho-kappa+2g)` pays for repairs; no optimality claim is assumed. -/
theorem pebbling_latency {ℓ n : ℕ} (W : ChungInterlayer n)
    (β : ℝ → ℝ) (απ π a : ℝ) (m s z t : ℕ) (δ ρ ζ : ℝ) :
    let p := (m : ℝ) / n
    let σ := (s : ℝ) / n
    let g := β p - δ - p
    let y := fun i : ℕ => (fun x => β x - δ)^[i] a
    let D := referenceScale y t p - referenceScale y t σ
    let D₀ := referenceScale y t p - referenceScale y t (min p (ζ - δ))
    let κ := β σ - δ - a
    let q := min (Nat.ceil (απ * n))
      (Nat.ceil (απ * n) + m + 1 - (Nat.ceil (π * n) + s))
    Nat.ceil (π * n) ≤ m → 1 ≤ q → 1 ≤ z → 0 < g → 0 < a →
    ρ + a ≤ min (ζ - δ) (β p - δ) → σ ∈ Ico a p →
    MonotoneOn β (Icc a p) → ConcaveOn ℝ (Icc a p) β →
    g ≤ β a - δ - a → 2 * g ≤ β σ - δ - σ →
    (∀ i < t, y i < p) → p ≤ y t →
    (∀ X : Finset (Fin n), (X.card : ℝ) / n ∈ Icc a p →
      β ((X.card : ℝ) / n) * n ≤ (W.neighborhood X).card) →
    ρ + max 0 (ρ - κ + 2 * g) + g * (1 + D₀ + ((z : ℝ) - 1) * (1 + D)) < g * ℓ →
    PebblingGame.LatencyEvent ℓ n απ δ π ρ ζ
      (Nat.ceil (απ * n) + ((z : ℝ) - 1) * q) W := by
  sorry

end ProofOfSpaceStatement

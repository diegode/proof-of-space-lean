import Mathlib.Data.Real.Basic
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

end ProofOfSpaceStatement

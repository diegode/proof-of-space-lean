import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.List.Chain
import Mathlib.Data.Real.Basic

/-!
# Latency hardness for stacked proof-of-space graphs

This is the statement of record for the Palomar submission. It imports only Mathlib and
states the concrete latency theorem without importing the proof development.

There are `M.ℓ` layers of `M.n` vertices. `M.intra` and `M.inter` are horizontal and
vertical dependency edges; `M.pred` expands subsets of one layer into predecessors in
the next. The `M.black` and `M.red` sets form a static storage snapshot, bounded globally
and per layer respectively. Under the scalar, expansion, and depth-robustness assumptions
in `LiteratureHypotheses M`, every sufficiently large red-free set in layer zero has an
unpebbled directed path of the stated length in its reachability footprint.

The conclusion is a graph-theoretic sequential-dependency certificate. The last
cryptographic step interpreting such a path as recomputation latency is not formalized.
The theorem is conditional on expansion and depth robustness; it does not construct a
deployed graph satisfying those assumptions.
-/

namespace ProofOfSpaceStatement

open Finset Set

universe u

/--
The data occurring in the latency statement, separated from the assumptions made about
it. `s₀` is the non-chain overhead and `z` is the certified segment count.
-/
structure LatencyData (V : Type u) where
  ℓ : ℕ
  n : ℕ
  β : ℝ → ℝ
  αg : ℝ
  δ : ℝ
  pi : ℝ
  ρ : ℝ
  ζδ : ℝ
  αmin : ℝ
  αmax : ℝ
  σ : ℝ
  mid : ℝ
  αpi : ℝ
  layer : ℕ → Finset V
  depth : V → ℕ
  rank : V → ℕ
  intra : ℕ → V → V → Prop
  inter : ℕ → V → V → Prop
  pred : ℕ → Finset V → Finset V
  black : ℕ → Finset V
  red : ℕ → Finset V
  s₀ : ℕ
  z : ℕ

/--
The conditional hypotheses used by `latency_general`.

Bundling them as a typeclass keeps the theorem signature readable while leaving the
dependency explicit at every use site as `[LiteratureHypotheses M]`. No instance of this
class is assumed globally.
-/
class LiteratureHypotheses {V : Type u} (M : LatencyData V) : Prop where
  β_maps : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → M.β x ∈ Icc (0 : ℝ) 1
  β_zero : M.β 0 = 0
  β_mono : StrictMonoOn M.β (Icc (0 : ℝ) 1)
  β_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) M.β
  β_expands : ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → x < M.β x
  β_reversal : ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → M.β (1 - M.β x) = 1 - x
  αg_mem : M.αg ∈ Ioo (0 : ℝ) 1
  αg_max : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → x ≠ M.αg →
    M.β x - x < M.β M.αg - M.αg
  δ_nonneg : 0 ≤ M.δ
  ρ_nonneg : 0 ≤ M.ρ
  pi_mem : M.pi ∈ Ioo (0 : ℝ) 1
  αg_lt_pi : M.αg < M.pi
  gpi_pos : 0 < M.β M.pi - M.δ - M.pi
  αmin_mem : M.αmin ∈ Icc (0 : ℝ) M.αg
  αmax_mem : M.αmax ∈ Icc M.αg 1
  gain_min : M.β M.αmin - M.δ - M.αmin = 0
  gain_max : M.β M.αmax - M.δ - M.αmax = 0
  σ_gt : M.αmin < M.σ
  σ_lt : M.σ < M.pi
  mid_ge : M.σ ≤ M.mid
  mid_le : M.mid ≤ M.pi
  mid_gain : 2 * min (M.β M.pi - M.δ - M.pi)
      ((M.β M.σ - M.δ - M.σ) / 2) ≤ M.β M.mid - M.δ - M.mid
  entry : M.αmin < M.ζδ - M.ρ
  ζδ_le : M.ζδ ≤ M.αmax
  layer_mem : ∀ {d : ℕ} {v : V},
    v ∈ M.layer d ↔ M.depth v = d ∧ d < M.ℓ
  layer_card : ∀ {d : ℕ}, d < M.ℓ → (M.layer d).card = M.n
  intra_mem : ∀ {d : ℕ} {u v : V},
    M.intra d u v → u ∈ M.layer d ∧ v ∈ M.layer d
  inter_mem : ∀ {d : ℕ} {u v : V},
    M.inter d u v → u ∈ M.layer (d + 1) ∧ v ∈ M.layer d
  intra_rank : ∀ {d : ℕ} {u v : V}, M.intra d u v → M.rank u < M.rank v
  inter_rank : ∀ {d : ℕ} {u v : V}, M.inter d u v → M.rank u < M.rank v
  pred_subset : ∀ {d : ℕ} {T : Finset V}, M.pred d T ⊆ M.layer (d + 1)
  pred_edge : ∀ {d : ℕ} {T : Finset V} {u : V},
    u ∈ M.pred d T → ∃ v ∈ T, M.inter d u v
  expansion : ∀ {d : ℕ} {T : Finset V}, d + 1 < M.ℓ → T ⊆ M.layer d →
    M.β ((T.card : ℝ) / M.n) * M.n ≤ (M.pred d T).card
  depth_robust : ∀ {d : ℕ}, d < M.ℓ → ∀ F : Finset V, F ⊆ M.layer d →
    M.pi * M.n ≤ (F.card : ℝ) → ∃ p : List V,
      p ≠ [] ∧ p.IsChain (M.intra d) ∧
        (∀ v ∈ p, v ∈ F) ∧ M.αpi * M.n ≤ (p.length : ℝ)
  black_subset : ∀ d, M.black d ⊆ M.layer d
  red_subset : ∀ d, M.red d ⊆ M.layer d
  black_total : ∀ m,
    ∑ d ∈ Finset.range m, ((M.black d).card : ℝ) / M.n ≤ M.ρ
  red_bound : ∀ d, ((M.red d).card : ℝ) ≤ M.δ * M.n
  n_pos : 0 < M.n
  ρ_pos : 0 < M.ρ
  σ_lt_αpi : M.σ < M.αpi
  constants : (M.s₀, M.z) =
    let gainD := fun x ↦ M.β x - M.δ - x
    let betaD := fun x ↦ M.β x - M.δ
    let gpi := gainD M.pi
    let piBar := 1 - M.β M.pi
    let zetaFloor := M.ζδ - M.ρ
    let gtilde := min (gainD zetaFloor) gpi
    let sigmaHat := min M.σ (1 - M.β M.σ)
    let lam := min piBar sigmaHat
    let ghat := min gpi (gainD M.σ / 2)
    let infertileCap := fun h ↦ Nat.ceil ((M.ρ - (M.ζδ - M.pi)) / h)
    let blockedCap := fun g ↦ Nat.ceil (M.ρ / g) - 1
    let sCap := infertileCap gtilde + blockedCap ghat
    let growthSpan := fun x ↦ max 1 ⌊(M.pi - M.σ + x) / ghat⌋₊
    let asymptoticGrowth := max 1 ((M.pi - M.σ) / ghat)
    let growthPot := fun split v ↦
      (min v split - M.σ) / (2 * ghat) + (max v split - split) / ghat
    let growthConst := min asymptoticGrowth (growthPot M.mid M.pi + 1)
    let h₁ := growthConst + 1
    let ledgerSlack := 2 * M.ρ / ghat
    let gmin := min ghat gtilde
    let jointSlack := 2 * M.ρ / gmin
    let searchHead := max 0 (1 + (M.pi - M.ζδ) / gtilde)
    let spendCap := ⌈M.ρ / ghat⌉₊
    let growthCap := growthSpan M.ρ
    let h₀ := growthCap + 2 * spendCap
    let bMax := blockedCap (betaD M.pi - lam)
    let s₀' := sCap + bMax * h₀
    let jointEntry :=
      if bMax = 0 then ⌈((M.ℓ : ℝ) - searchHead - jointSlack) / h₁⌉₊ else 0
    let z' := max 1 (max
      ⌈((M.ℓ : ℝ) - sCap - ledgerSlack - bMax * h₁) / (((bMax : ℝ) + 1) * h₁)⌉₊
      (max jointEntry ((M.ℓ - s₀') / ((bMax + 1) * h₀) + 1)))
    (s₀', z')
  inside : M.s₀ < M.ℓ

/--
**Concrete latency lower bound.**

Assuming the explicit conditional interface `[LiteratureHypotheses M]`, the conclusion
exhibits the path itself as a nonempty list: consecutive vertices are dependency edges,
all vertices are unpebbled, the path starts at `u`, ends in the target set `A`, and has
at least the displayed number of vertices.
-/
theorem latency_general {V : Type u}
    (M : LatencyData V) [LiteratureHypotheses M]
    (A : Finset V) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hweight : M.ζδ ≤ (A.card : ℝ) / M.n) :
    ∃ u a, a ∈ A ∧ ∃ Q : List V,
      Q ≠ [] ∧
      Q.IsChain (fun x y ↦ (∃ d, M.intra d x y) ∨ (∃ d, M.inter d x y)) ∧
      (∀ v ∈ Q, v ∉ M.black (M.depth v) ∧ v ∉ M.red (M.depth v)) ∧
      Q.head? = some u ∧ Q.getLast? = some a ∧
      M.αpi * M.n + ((M.z : ℝ) - 1) * (M.αpi - M.σ) * M.n ≤
        (Q.length : ℝ) := by
  sorry

end ProofOfSpaceStatement

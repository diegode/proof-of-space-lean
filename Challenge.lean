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

There are `ℓ` layers of `n` vertices. `intra` and `inter` are horizontal and vertical
dependency edges; `pred` expands subsets of one layer into predecessors in the next.
The `black` and `red` sets form a static storage snapshot, bounded globally and per
layer respectively. Under the displayed scalar, expansion, and depth-robustness
hypotheses, every sufficiently large red-free set in layer zero has an unpebbled
directed path of the stated length in its reachability footprint.

The conclusion is a graph-theoretic sequential-dependency certificate. The last
cryptographic step interpreting such a path as recomputation latency is not formalized.
The theorem is conditional on expansion and depth robustness; it does not construct a
deployed graph satisfying those assumptions.
-/

namespace ProofOfSpaceStatement

open Finset Set

universe u


/--
**Concrete latency lower bound.**

The first block of hypotheses gives the expansion profile `β`, its adjusted-gain
interval, and the source-tracking parameters. The second describes the layered graph,
including the ordinary survivor-set formulation of depth robustness. The third is the
static pebbling. `hconstants` spells out the two derived natural-number constants used
by the theorem: the non-chain overhead `s₀` and certified segment count `z`.

The conclusion exhibits the path itself as a nonempty list: consecutive vertices are
dependency edges, all vertices are unpebbled, the path starts at `u`, ends in the target
set `A`, and has at least the displayed number of vertices.
-/
theorem latency_general
    {V : Type u} {ℓ n : ℕ}
    (β : ℝ → ℝ) (αg δ pi ρ ζδ αmin αmax : ℝ)
    (hβmaps : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → β x ∈ Icc (0 : ℝ) 1)
    (hβzero : β 0 = 0)
    (hβmono : StrictMonoOn β (Icc (0 : ℝ) 1))
    (hβconcave : ConcaveOn ℝ (Icc (0 : ℝ) 1) β)
    (hβexpands : ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → x < β x)
    (hβreversal : ∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → β (1 - β x) = 1 - x)
    (hαgmem : αg ∈ Ioo (0 : ℝ) 1)
    (hαgmax : ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 → x ≠ αg → β x - x < β αg - αg)
    (hδ : 0 ≤ δ) (hρnonneg : 0 ≤ ρ)
    (hpimem : pi ∈ Ioo (0 : ℝ) 1) (hαgpi : αg < pi)
    (hgpi : 0 < β pi - δ - pi)
    (hαminmem : αmin ∈ Icc (0 : ℝ) αg)
    (hαmaxmem : αmax ∈ Icc αg 1)
    (hgainmin : β αmin - δ - αmin = 0)
    (hgainmax : β αmax - δ - αmax = 0)
    (σ mid : ℝ) (hσmin : αmin < σ) (hσpi : σ < pi)
    (hσmid : σ ≤ mid) (hmidpi : mid ≤ pi)
    (hmidgain : 2 * min (β pi - δ - pi) ((β σ - δ - σ) / 2) ≤ β mid - δ - mid)
    (hentry : αmin < ζδ - ρ) (hζmax : ζδ ≤ αmax)
    (αpi : ℝ) (layer : ℕ → Finset V) (depth rank : V → ℕ)
    (intra inter : ℕ → V → V → Prop) (pred : ℕ → Finset V → Finset V)
    (hlayer : ∀ {d : ℕ} {v : V}, v ∈ layer d ↔ depth v = d ∧ d < ℓ)
    (hlayercard : ∀ {d : ℕ}, d < ℓ → (layer d).card = n)
    (hintramem : ∀ {d : ℕ} {u v : V}, intra d u v → u ∈ layer d ∧ v ∈ layer d)
    (hintermem : ∀ {d : ℕ} {u v : V}, inter d u v → u ∈ layer (d + 1) ∧ v ∈ layer d)
    (hintrarank : ∀ {d : ℕ} {u v : V}, intra d u v → rank u < rank v)
    (hinterrank : ∀ {d : ℕ} {u v : V}, inter d u v → rank u < rank v)
    (hpredsubset : ∀ {d : ℕ} {T : Finset V}, pred d T ⊆ layer (d + 1))
    (hprededge : ∀ {d : ℕ} {T : Finset V} {u : V},
      u ∈ pred d T → ∃ v ∈ T, inter d u v)
    (hexpansion : ∀ {d : ℕ} {T : Finset V}, d + 1 < ℓ → T ⊆ layer d →
      β ((T.card : ℝ) / n) * n ≤ (pred d T).card)
    (hdepth : ∀ {d : ℕ}, d < ℓ → ∀ F : Finset V, F ⊆ layer d →
      pi * n ≤ (F.card : ℝ) → ∃ p : List V, p ≠ [] ∧ p.IsChain (intra d) ∧
        (∀ v ∈ p, v ∈ F) ∧ αpi * n ≤ (p.length : ℝ))
    (black red : ℕ → Finset V)
    (hblacksubset : ∀ d, black d ⊆ layer d) (hredsubset : ∀ d, red d ⊆ layer d)
    (hblacktotal : ∀ m, ∑ d ∈ Finset.range m, ((black d).card : ℝ) / n ≤ ρ)
    (hredbound : ∀ d, ((red d).card : ℝ) ≤ δ * n)
    (hn : 0 < n) (hρ : 0 < ρ) (hσapi : σ < αpi)
    (s₀ z : ℕ)
    (hconstants : (s₀, z) =
      let gainD := fun x ↦ β x - δ - x
      let betaD := fun x ↦ β x - δ
      let gpi := gainD pi
      let piBar := 1 - β pi
      let zetaFloor := ζδ - ρ
      let gtilde := min (gainD zetaFloor) gpi
      let sigmaHat := min σ (1 - β σ)
      let lam := min piBar sigmaHat
      let ghat := min gpi (gainD σ / 2)
      let infertileCap := fun h ↦ Nat.ceil ((ρ - (ζδ - pi)) / h)
      let blockedCap := fun g ↦ Nat.ceil (ρ / g) - 1
      let sCap := infertileCap gtilde + blockedCap ghat
      let growthSpan := fun x ↦ max 1 ⌊(pi - σ + x) / ghat⌋₊
      let asymptoticGrowth := max 1 ((pi - σ) / ghat)
      let growthPot := fun split v ↦
        (min v split - σ) / (2 * ghat) + (max v split - split) / ghat
      let growthConst := min asymptoticGrowth (growthPot mid pi + 1)
      let h₁ := growthConst + 1
      let ledgerSlack := 2 * ρ / ghat
      let gmin := min ghat gtilde
      let jointSlack := 2 * ρ / gmin
      let searchHead := max 0 (1 + (pi - ζδ) / gtilde)
      let spendCap := ⌈ρ / ghat⌉₊
      let growthCap := growthSpan ρ
      let h₀ := growthCap + 2 * spendCap
      let bMax := blockedCap (betaD pi - lam)
      let s₀' := sCap + bMax * h₀
      let jointEntry :=
        if bMax = 0 then ⌈((ℓ : ℝ) - searchHead - jointSlack) / h₁⌉₊ else 0
      let z' := max 1 (max
        ⌈((ℓ : ℝ) - sCap - ledgerSlack - bMax * h₁) / (((bMax : ℝ) + 1) * h₁)⌉₊
        (max jointEntry ((ℓ - s₀') / ((bMax + 1) * h₀) + 1)))
      (s₀', z'))
    (hinside : s₀ < ℓ)
    (A : Finset V) (hA : A ⊆ layer 0)
    (hred : ∀ v ∈ A, v ∉ red 0)
    (hweight : ζδ ≤ (A.card : ℝ) / n) :
    ∃ u a, a ∈ A ∧ ∃ Q : List V,
      Q ≠ [] ∧
      Q.IsChain (fun x y ↦ (∃ d, intra d x y) ∨ (∃ d, inter d x y)) ∧
      (∀ v ∈ Q, v ∉ black (depth v) ∧ v ∉ red (depth v)) ∧
      Q.head? = some u ∧ Q.getLast? = some a ∧
      αpi * n + ((z : ℝ) - 1) * (αpi - σ) * n ≤ (Q.length : ℝ) := by
  sorry

end ProofOfSpaceStatement

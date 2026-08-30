import ProofOfSpace.Latency

/-!
# Proved latency solution

This is the proved counterpart of `Challenge.lean`. It constructs the bundled model
used by the substantive library, invokes `ProofOfSpace.latency_general`, and exposes its
path witness in the Mathlib-only form used by the Challenge.
-/

namespace ProofOfSpaceStatement

open Finset Set
open ProofOfSpace

universe u


/-- The concrete latency theorem, proved in `ProofOfSpace.Latency`. -/
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
  let S : Setting := {
    β := β
    αg := αg
    δ := δ
    pi := pi
    ρ := ρ
    ζδ := ζδ
    αmin := αmin
    αmax := αmax
    β_maps := by
      intro x hx
      exact hβmaps hx
    β_zero := hβzero
    β_strictMonoOn := hβmono
    β_concaveOn := hβconcave
    β_expands := by
      intro x hx
      exact hβexpands hx
    β_reversal := by
      intro x hx
      exact hβreversal hx
    αg_mem := hαgmem
    αg_max := by
      intro x hx hne
      exact hαgmax hx hne
    δ_nonneg := hδ
    ρ_nonneg := hρnonneg
    pi_mem := hpimem
    αg_lt_pi := hαgpi
    gpi_pos := hgpi
    αmin_mem := hαminmem
    αmax_mem := hαmaxmem
    gainD_αmin := hgainmin
    gainD_αmax := hgainmax
  }
  let T : Tracking S := {
    σ := σ
    σ_gt := hσmin
    σ_lt := hσpi
    mid := mid
    mid_ge := hσmid
    mid_le := hmidpi
    mid_gain := hmidgain
  }
  let G : Concrete.LayeredGraph V S ℓ n := {
    αpi := αpi
    layer := layer
    depth := depth
    rank := rank
    intra := intra
    inter := inter
    pred := pred
    layer_mem := hlayer
    layer_card := hlayercard
    intra_mem := hintramem
    inter_mem := hintermem
    intra_rank := hintrarank
    inter_rank := hinterrank
    pred_subset := by
      intro d T v hv
      exact hpredsubset hv
    pred_edge := hprededge
    expands := hexpansion
  }
  let P : Concrete.Pebbling G := {
    black := black
    red := red
    black_subset := by
      intro d v hv
      exact hblacksubset d hv
    red_subset := by
      intro d v hv
      exact hredsubset d hv
    black_total := hblacktotal
    red_bound := hredbound
  }
  let GR : GeneralRegime S := {
    entry := hentry
    zeta_le := hζmax
  }
  change (s₀, z) = (ProofOfSpace.s₀ S T, ProofOfSpace.zMin S T ℓ) at hconstants
  have hs₀ : s₀ = ProofOfSpace.s₀ S T := congrArg Prod.fst hconstants
  have hz : z = ProofOfSpace.zMin S T ℓ := congrArg Prod.snd hconstants
  subst s₀
  subst z
  have hσapi' : T.σ < G.αpi := by
    exact hσapi
  have hdepth' : G.DepthRobust G.αpi := by
    intro d hd F hF hcard
    exact hdepth hd F hF hcard
  have hinside' : ProofOfSpace.s₀ S T < ℓ := by
    exact hinside
  have hA' : A ⊆ G.layer 0 := by
    exact hA
  have hred' : ∀ v ∈ A, v ∉ P.red 0 := by
    exact hred
  have hweight' : S.ζδ ≤ Concrete.Pebbling.weight n A := by
    exact hweight
  have hpath := ProofOfSpace.latency_general G P T GR hn hρ hσapi' hdepth' hinside'
    A hA' hred' hweight'
  rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
  refine ⟨u, a, ha, Q.nodes, Q.nonempty, Q.chain, Q.unpebbled', ?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head Q.nonempty]
    exact congrArg some hfirst
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast
  · change
      αpi * n + ((ProofOfSpace.zMin S T ℓ : ℝ) - 1) * (αpi - σ) * n ≤
        (Q.nodes.length : ℝ) at hlength
    exact hlength

end ProofOfSpaceStatement

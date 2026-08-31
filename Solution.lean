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

/-- The explicit conditional assumptions of the latency theorem. -/
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


/-- Internal adapter from the unbundled statement to `ProofOfSpace.Latency`. -/
private theorem latency_general_flat
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

/-- The concrete latency theorem, with all conditional assumptions bundled explicitly. -/
theorem latency_general {V : Type u}
    (M : LatencyData V) [H : LiteratureHypotheses M]
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
  exact latency_general_flat (ℓ := M.ℓ) (n := M.n)
    M.β M.αg M.δ M.pi M.ρ M.ζδ M.αmin M.αmax
    H.β_maps H.β_zero H.β_mono H.β_concave H.β_expands H.β_reversal
    H.αg_mem H.αg_max H.δ_nonneg H.ρ_nonneg H.pi_mem H.αg_lt_pi H.gpi_pos
    H.αmin_mem H.αmax_mem H.gain_min H.gain_max
    M.σ M.mid H.σ_gt H.σ_lt H.mid_ge H.mid_le H.mid_gain
    H.entry H.ζδ_le M.αpi M.layer M.depth M.rank M.intra M.inter M.pred
    H.layer_mem H.layer_card H.intra_mem H.inter_mem H.intra_rank H.inter_rank
    (by
      intro d T v hv
      exact H.pred_subset hv)
    H.pred_edge H.expansion H.depth_robust
    M.black M.red H.black_subset H.red_subset H.black_total H.red_bound
    H.n_pos H.ρ_pos H.σ_lt_αpi M.s₀ M.z H.constants H.inside
    A hA hred hweight

end ProofOfSpaceStatement

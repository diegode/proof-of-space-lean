/-
# Chains and the constants of the latency theorems

This file formalizes the constants and chain of this development:

* `h₁`, `ledgerSlack`, `spendCap`, `growthCap`, `h₀`, `localSpan` — the per-link
  constants of `span bound`/`optimized span bound`, and `zMinNoBreak`, the chain length of
  `latency_general`.
* `ChainSystem` — the chain of `latency analysis`, in the form in which the analysis uses it.  All the
  graph-specific content of the development is confined to its two fields `extend` (depth
  robustness at a fertile expandable level, plus the path splicing of `path-payoff lemma`) and
  `realizes`.  Depth robustness is the one input the development leaves unproven for the
  concrete construction, so it is an assumption here as well.

The accounting itself — `extension-attempt lemma`, `level ledger`, and the chain
count — is *not* here.  There is a single accounting for both parameter regimes and it lives in
`Ledger.lean`, because it needs one input beyond a `ChainSystem`: the ability to restart
a broken chain.

Depths increase away from the challenge (Lean depth `d` is the development's level `ℓ - d`;
see `Footprint.lean`), so the windows of successive attempts are the pairwise disjoint
intervals `(b_j, b_{j+1}]`, and the ledger is just the total-budget bound applied to
their union.
-/
import ProofOfSpace.Continuation

namespace ProofOfSpace

open Set Finset

universe u

variable {S : Setting} {B : Budget S} {T : Tracking S}

/-! ### The per-link constants of `span bound` and `optimized span bound` -/

/-- **`h_1` of `optimized span bound`**: `growthConst + 1`.

The `+1` is exactly the constant of `contSpan`: an attempt spends
`growthConst + growthSpend/ĝ` levels growing and `2 continuationSpend/ĝ + 1` levels on
the fertile continuation, so `growthConst + 1 + 2(growthSpend + continuationSpend)/ĝ`
bounds the whole window.

`growthConst = min{a, Φ_{σ̃}(π) + 1}` selects the strongest of the single-constant
growth span `a = max{1, (π - σ)/ĝ}` and the two-piece potential count of `Growth.lean`. -/
noncomputable def h₁ (S : Setting) (T : Tracking S) : ℝ := growthConst S T + 1

/-- `2ρ/ĝ`, the one-time global-budget term of the level offset `s_1` in
`global constants`.  The development does not name it separately. -/
noncomputable def ledgerSlack (S : Setting) (T : Tracking S) : ℝ := 2 * S.ρ / T.ghat

/-! ### The joint ledger constants

The level offset `s_1 = s + 2ρ/ĝ` of `global constants` charges the budget `ρ` three
times over: once as the infertile-capacity term of `s`, once as its blocked-window term
`⌈ρ/ĝ⌉ - 1`, and twice more as `2ρ/ĝ`.  All three charges are levied on *disjoint*
ranges of levels — the searches and the attempts partition the stack — so one interval
sum bounds them all.  The constants below are the joint form: a head that no longer
mentions `ρ`, and a single global charge `2ρ/min{ĝ, g̃}`.

At the Filecoin parameters `ĝ = g̃ = g_π` and `searchHead + jointSlack < 14.82`.
-/

/-- `min{ĝ, g̃}`: the slower of the two certified gain rates.  Searches are charged at
`g̃` and attempts at `ĝ`; the joint ledger charges both at the smaller. -/
noncomputable def gmin (S : Setting) (T : Tracking S) : ℝ := min T.ghat S.gtilde

/-- `2ρ/min{ĝ, g̃}`: the single global spend charge of the joint ledger. -/
noncomputable def jointSlack (S : Setting) (T : Tracking S) : ℝ := 2 * S.ρ / gmin S T

/-- `max{0, 1 + (π - ζ_δ)/g̃}`: the spend-free head of the joint ledger.  It is the
ceiling slack of `infertile-capacity lemma` plus the distance the challenge footprint has
to climb from its undiminished weight `ζ_δ`; `jointSlack` accounts for the diminution. -/
noncomputable def searchHead (S : Setting) : ℝ := max 0 (1 + (S.pi - S.ζδ) / S.gtilde)

/-- The head at a restart depth `b`: `searchHead` with the spend already made above `b`
added back, since the challenge footprint at `b` may have been pushed down by it.  Only
`b = 0` is ever used at the top level, where it is `searchHead`; the general form is what
makes the induction of `general_ledger` go through. -/
noncomputable def restartHead (S : Setting) (B : Budget S) (b : ℕ) : ℝ :=
  max 0 (1 + (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 b, B.spend d) / S.gtilde)

theorem gmin_le_ghat : gmin S T ≤ T.ghat := min_le_left _ _

theorem gmin_le_gtilde : gmin S T ≤ S.gtilde := min_le_right _ _

theorem gmin_pos (hg : 0 < S.gtilde) : 0 < gmin S T := lt_min T.ghat_pos hg

theorem searchHead_nonneg : 0 ≤ searchHead S := le_max_left _ _

theorem restartHead_nonneg (b : ℕ) : 0 ≤ restartHead S B b := le_max_left _ _

@[simp] theorem restartHead_zero : restartHead S B 0 = searchHead S := by
  simp only [restartHead, searchHead, Finset.Ico_self, Finset.sum_empty, add_zero]

/-- Widening a charge from `ĝ` to `min{ĝ, g̃}`. -/
theorem ghat_charge_le_gmin (hg : 0 < S.gtilde) {x : ℝ} (hx : 0 ≤ x) :
    2 * x / T.ghat ≤ 2 * x / gmin S T := by
  refine div_le_div_of_nonneg_left (by linarith) (gmin_pos (T := T) hg) gmin_le_ghat
theorem gmin_charge_mono (hg : 0 < S.gtilde) {x y : ℝ} (hxy : x ≤ y) :
    2 * x / gmin S T ≤ 2 * y / gmin S T := by
  rw [div_le_div_iff_of_pos_right (gmin_pos (T := T) hg)]
  linarith

/-- `⌈ρ/ĝ⌉`, the blocked-window term of `span bound`. -/
noncomputable def spendCap (S : Setting) (T : Tracking S) : ℕ := ⌈S.ρ / T.ghat⌉₊

/-- `max{1, ⌊(π - σ + ρ)/ĝ⌋}`, the growth term of `span bound`. -/
noncomputable def growthCap (S : Setting) (T : Tracking S) : ℕ := growthSpan S T S.ρ

/-- **`h_0` of `span bound`**: `max{1, ⌊(π - σ + ρ)/ĝ⌋} + 2⌈ρ/ĝ⌉`, the
constant-charge per-link span. -/
noncomputable def h₀ (S : Setting) (T : Tracking S) : ℕ := growthCap S T + 2 * spendCap S T

/-- The number of levels an attempt consumes when every local charge is bounded by the
whole budget: the `h_0 - 1` of `attempt-span bound`, whenever `ρ > 0`. -/
noncomputable def localSpan (S : Setting) (T : Tracking S) : ℕ :=
  growthCap S T + contSpan T S.ρ

/-- **`z_min` of `minimum link-count definition`, specialized to `b^max = 0`**: the maximum defining the link
count when no break can be paid for.  `Ledger.zMin` is the general `minimum link-count definition`, and `Ledger.zMin_eq_zMinNoBreak`
identifies the two there. -/
noncomputable def zMinNoBreak (S : Setting) (T : Tracking S) (ℓ s : ℕ) : ℕ :=
  max 1 (max ⌈((ℓ : ℝ) - s - ledgerSlack S T) / h₁ S T⌉₊
    (max ⌈((ℓ : ℝ) - searchHead S - jointSlack S T) / h₁ S T⌉₊
      ((ℓ - s) / h₀ S T + 1)))

theorem h₁_pos : 0 < h₁ S T := by
  have := one_le_growthConst (S := S) (T := T)
  simp only [h₁]; linarith

theorem localSpan_succ_le_h₀ (hρ : 0 < S.ρ) : localSpan S T + 1 = h₀ S T := by
  have hq : 1 ≤ spendCap S T := by
    have : 0 < S.ρ / T.ghat := div_pos hρ T.ghat_pos
    simpa [spendCap] using Nat.one_le_ceil_iff.mpr this
  simp only [localSpan, h₀, contSpan, spendCap] at *
  omega

/-! ### Chains -/

/--
**The chain of `latency analysis`, in the form the analysis consumes.**

A `ChainSystem` is the graph-side data of chains for a fixed pebbling: a type of links,
each carrying its depth `b_i`, the footprint bound `wt` bounding the footprint weights of its
source set of the link below `b_i`, and the number `count` of links already spliced.

`extend` is the *only* graph input: at a fertile `ĝ`-expandable depth `b` strictly
inside the graph and strictly below the current link, depth robustness produces a path of
length `α_π n` inside the footprint at `b`, whose first `σ n` nodes form the next source set, and
the footprint inclusions a link carries (`path-payoff lemma`) splice the paths.  Depth
robustness of the construction is *assumed*, exactly as in the development.
-/
structure ChainSystem (S : Setting) (B : Budget S) (T : Tracking S) (ℓ : ℕ)
    (Realizes : ℕ → Prop) where
  /-- The links of a chain. -/
  Link : Type u
  /-- The depth `b_i` of a link. -/
  depth : Link → ℕ
  /-- A lower bound on the footprint weights of the source set of the link below `b_i`. -/
  wt : Link → ℕ → ℝ
  /-- `wt L` follows Reyzin's footprint recurrence below `depth L`. -/
  bound : ∀ L, IsFootprintBound S B (depth L) (wt L)
  /-- The source set has weight exactly `σ`. -/
  init : ∀ L, wt L (depth L) = T.σ
  /-- The last level of the chain is `ĝ`-expandable (`expandability condition`). -/
  expandable : ∀ L, Expandable B T.ghat (depth L)
  /-- The link lies inside the graph. -/
  inside : ∀ L, depth L < ℓ
  /-- The number of links of the chain ending at this one. -/
  count : Link → ℕ
  count_pos : ∀ L, 1 ≤ count L
  /-- The spliced path realized by the chain (`path-payoff lemma`). -/
  realizes : ∀ L, Realizes (count L)
  /-- **Depth robustness** (assumed) and the splice of `path-payoff lemma`. -/
  extend : ∀ (L : Link) (b : ℕ), depth L < b → b < ℓ → S.pi ≤ wt L b →
      Expandable B T.ghat b → ∃ L' : Link, depth L' = b ∧ count L' = count L + 1

/-! ### The accounting

`Ledger.lean` proves `ChainSystem.general_ledger` and
`ChainSystem.exists_many_links_gen`. It adds the ability to restart a broken chain.
When `ρ < β_δ(π) - π̄`, `Ledger.bMax_eq_zero` rules out paid breaks and
`Ledger.zMin_eq_zMinNoBreak` gives the specialized count defined above.
-/



end ProofOfSpace

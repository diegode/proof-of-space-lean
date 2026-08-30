/-
# The chain ledger: one latency accounting for both parameter regimes

This file proves the chain-counting theorem used by `latency_general`. Infertile
challenge levels are charged at the rate `g̃` from `challenge-floor lemma`. An attempt
may break when concentrated spending pushes its tracked footprint below `π̂`; the
construction then restarts from the challenge footprint.

At the Filecoin parameters, `gtilde_eq_gpi` identifies `g̃` with `g_π`, and
`bMax_eq_zero` rules out breaks because the black-pebble budget is smaller than the
charge `β_δ(π) - π̂` required by `Growth.break_charge`.

Contents:

* `GeneralRegime` — `general scalar conditions`.
* `bMax`, `sCap`, `s₀`, `zMin` — the link-count constants.
* `search_stops` — the search of `Search.lean` run to completion, in the positive
  form the restart searches need.
* `ChainSystem.extension_attempt_gen` — `extension-attempt lemma`: an attempt ends at the bottom
  of the graph, at the next link, or at a break; it consumes at most `h_0 - 1` levels and
  simultaneously at most `h_1 + 2x/ĝ`, where `x` is the spend inside its own window.
* `ChainSystem.general_ledger` — the accounting that runs the whole construction, and
  carries both of those bounds through one induction.  `break-charge lemma` and
  `level ledger` are two of its components.
* `ChainSystem.exists_many_links_gen` / `latency_gen` — `chain-length lemma` and
  `latency_general`, with all entries of `minimum link-count definition`: the ledger entry
  (slope `1/((b^max+1) h_1)`), the joint-ledger entry `jointEntry`, and the
  constant-charge one (slope `1/((b^max+1) h_0)`).

## The joint ledger

`global constants` offsets the ledger entry by `s_1 = s + 2ρ/ĝ`, and that charges the
black budget `ρ` three times over: once in the infertile-capacity term of `s`, once in
its blocked-window term `⌈ρ/ĝ⌉ - 1`, and twice in `2ρ/ĝ`.  The three charges are levied
on *disjoint* ranges of levels — a search and an attempt never share a level, and the
construction moves strictly downward — so a single interval sum bounds all of them, and
`Budget.sum_Ico_le` caps that sum by `ρ`.

`jointEntry` uses `ChallengeBound.infertile_card_charge` to price each infertile level
against spending in its own window. `GenLedger` carries the window start (`b` for a
search, `b + 1` for a link) and its head (`restartHead` or `0`). The joint clause applies
when no break is charged, so search and attempt windows remain disjoint.

At the Filecoin parameters this offset is below `14.82`.
-/
import ProofOfSpace.Chain

namespace ProofOfSpace

open Set Finset

universe u

variable {S : Setting} {B : Budget S} {T : Tracking S}

/-! ### The general parameter regime -/

/-- **`general scalar conditions`.**  The nontriviality assumptions of the general regime: the
challenge weight stays inside the active interval even after the whole budget is spent.

The Filecoin specialization verifies the stronger `π̄ < ζ_δ - ρ` of
`no-break parameter conditions`, from which this follows since `α_δ^min < π̄` always. -/
structure GeneralRegime (S : Setting) : Prop where
  /-- `α_δ^min < zetaFloor = ζ_δ - ρ`. -/
  entry : S.αmin < S.zetaFloor
  /-- `ζ_δ ≤ α_δ^max`. -/
  zeta_le : S.ζδ ≤ S.αmax

namespace GeneralRegime

theorem zetaFloor_lt_αmax (GR : GeneralRegime S) (hρ : 0 < S.ρ) : S.zetaFloor < S.αmax := by
  simp only [Setting.zetaFloor]
  linarith [GR.zeta_le]

theorem gtilde_pos (GR : GeneralRegime S) (hρ : 0 < S.ρ) : 0 < S.gtilde :=
  S.gtilde_pos GR.entry (GR.zetaFloor_lt_αmax hρ)

end GeneralRegime

/-! ### The constants of `latency_general` -/

/-- `b^max = ⌈ρ/(β_δ(π) - π̂)⌉ - 1`, the number of chain breaks the whole black-pebble
budget can pay for (`break-cap definition`).  `break_charge` is `break-charge lemma`, the charge a
break actually costs, and it is what makes `bMax_eq_zero` fire at the Filecoin
budget.  The
denominator is positive because
`π̂ ≤ π̄ < π < β_δ(π)`. -/
noncomputable def bMax (S : Setting) (T : Tracking S) : ℕ :=
  blockedCap S (S.betaD S.pi - T.lam)

/-- `s(ĝ, g̃) = infertileCap(g̃) + blockedCap(ĝ)` (`search-cap definition`): the total search overhead,
covering the initial search and *all* restart searches together. -/
noncomputable def sCap (S : Setting) (T : Tracking S) : ℕ := sCapOf S T.ghat S.gtilde

/-- **`s_0` of `global constants`**: the total non-chain overhead `s + b^max h_0`.

Only the `b^max` broken attempts need a whole link span; the final incomplete attempt of
the surviving segment is already paid for, because an attempt consumes at most
`localSpan = h_0 - 1` levels rather than `h_0`.  With `b^max = 0` this is just `s`, which
is what makes `zMin` collapse onto `zMinNoBreak` with no additive loss. -/
noncomputable def s₀ (S : Setting) (T : Tracking S) : ℕ :=
  sCap S T + bMax S T * h₀ S T

/--
**The joint-ledger entry.**

`⌈(ℓ - searchHead - 2ρ/min{ĝ,g̃})/h_1⌉_+`, the link count certified when the search
charge, the blocked-window charge and the attempt charges are all levied on the *same*
budget instead of three copies of it.

It is guarded by `b^max = 0`.  The joint clause of `GenLedger` is proved only when no
break was *charged*, because after a break the restart search runs below levels the
attempts have already been charged for, and the two windows are no longer disjoint.
When `b^max = 0` no break can be charged at all (`blocked_le_qB`), so the guard costs
nothing exactly where the entry is wanted. -/
noncomputable def jointEntry (S : Setting) (T : Tracking S) (ℓ : ℕ) : ℕ :=
  if bMax S T = 0 then ⌈((ℓ : ℝ) - searchHead S - jointSlack S T) / h₁ S T⌉₊ else 0

/--
**`z_min` of `minimum link-count definition`**: the chain length certified by `chain-length lemma`.

It is the maximum of the base entry `1` and three substantive bounds: the global
`h_1` ledger entry, the no-break joint-ledger entry, and the constant-charge `h_0`
entry. When breaks are possible, `b^max + 1` chain segments share the graph, so the
best of them gets a `(b^max + 1)`-th of the links, and the `b^max` broken attempts cost
one link span each.

When `b^max = 0`, `zMin_eq_zMinNoBreak` identifies this definition with
`zMinNoBreak`. The maximum combines valid lower bounds that can dominate for different
parameter choices. -/
noncomputable def zMin (S : Setting) (T : Tracking S) (ℓ : ℕ) : ℕ :=
  max 1 (max
    ⌈((ℓ : ℝ) - sCap S T - ledgerSlack S T - bMax S T * h₁ S T) /
        (((bMax S T : ℝ) + 1) * h₁ S T)⌉₊
    (max (jointEntry S T ℓ)
      ((ℓ - s₀ S T) / ((bMax S T + 1) * h₀ S T) + 1)))

theorem betaD_pi_sub_lam_pos : 0 < S.betaD S.pi - T.lam := by
  have hb : S.betaD S.pi = S.pi + S.gpi := by simp only [Setting.betaD_eq]; rfl
  rw [hb]
  linarith [T.lam_lt_pi, S.gpi_pos']

/-- **A budget below one break's charge forbids breaks outright.**  `break-charge lemma`
prices a break at `β_δ(π) - π̂`, so `ρ < β_δ(π) - π̂` says the budget cannot pay for a
single one.  At the Filecoin parameters this is the budget inequality
`ρ < β_δ(π) - π̄` of `no-break parameter conditions`, together with `π̂ = π̄`. -/
theorem bMax_eq_zero (hlt : S.ρ < S.betaD S.pi - T.lam) : bMax S T = 0 := by
  have hceil : ⌈S.ρ / (S.betaD S.pi - T.lam)⌉₊ ≤ 1 := by
    refine Nat.ceil_le.mpr ?_
    rw [Nat.cast_one, div_le_one betaD_pi_sub_lam_pos]
    linarith
  simp only [bMax, blockedCap]
  omega

/-- When the challenge floor sits above `π̄` and is itself infertile, the general
infertile-gain floor is `g_π`: `π̄ ≤ ζ_δ - ρ ≤ π` puts it on the mirror interval, where
concavity gives `gain_δ ≥ g_π`. -/
theorem gtilde_eq_gpi (h1 : S.piBar < S.zetaFloor) (hle : S.zetaFloor ≤ S.pi) :
    S.gtilde = S.gpi :=
  min_eq_right (S.gpi_le_gainD ⟨h1.le, hle⟩)

/-- **No loss when no break can be paid for.**  With `b^max = 0` the general chain
length is exactly `zMinNoBreak`. -/
theorem zMin_eq_zMinNoBreak (h : bMax S T = 0) (ℓ : ℕ) :
    zMin S T ℓ = zMinNoBreak S T ℓ (sCap S T) := by
  simp only [zMin, zMinNoBreak, jointEntry, s₀, h, Nat.cast_zero, zero_mul, sub_zero,
    zero_add, one_mul, Nat.add_zero, if_pos]

theorem one_le_growthCap : 1 ≤ growthCap S T := le_max_left _ _

theorem h₀_pos : 0 < h₀ S T := by
  have := one_le_growthCap (S := S) (T := T)
  simp only [h₀]
  omega

theorem one_le_zMin (ℓ : ℕ) : 1 ≤ zMin S T ℓ := le_max_left _ _


/-! ### The search in positive form -/

/-- **The search run to completion.**  From depth `t` the search of `Search.lean`
reaches a fertile `g`-expandable depth, or leaves the window `[t, E)`, and it consumes
exactly `I + Q` levels: `I` single-level skips at distinct infertile depths of `[t, p)`,
and `Q` levels inside blocked ranges whose *disjoint* spends exceed `Q g`.

`search_bound` packages the same search in the contrapositive form used by
`first-source lemma`; this version keeps the position it stops at, which is what a restart
needs. -/
theorem search_stops {B : Budget S} {g : ℝ} (Fert : ℕ → Prop) [DecidablePred Fert]
    (t E : ℕ) :
    ∃ p I Q : ℕ, p = t + I + Q ∧
      (E ≤ p ∨ (Fert p ∧ Expandable B g p)) ∧
      I ≤ ((Finset.Ico t p).filter (fun d => ¬ Fert d)).card ∧
      (0 < Q → (Q : ℝ) * g < ∑ d ∈ Finset.Ico (t + 1) p, B.spend d) := by
  classical
  have hex : ∃ j, (Fert (searchPos B g Fert t j) ∧ Expandable B g (searchPos B g Fert t j)) ∨
      E ≤ searchPos B g Fert t j := by
    refine ⟨E, Or.inr ?_⟩
    have := le_searchPos (B := B) (g := g) (Fert := Fert) (t := t) E
    omega
  set J := Nat.find hex with hJ
  have hJspec := Nat.find_spec hex
  have hbad : ∀ j, j < J →
      ¬(Fert (searchPos B g Fert t j) ∧ Expandable B g (searchPos B g Fert t j)) := by
    intro j hj hcon
    exact (Nat.find_min hex hj) (Or.inl hcon)
  obtain ⟨_, hQlt⟩ :=
    searchQ_spend (B := B) (g := g) (Fert := Fert) (t := t) hbad J (le_refl J)
  exact ⟨searchPos B g Fert t J, searchI B g Fert t J, searchQ B g Fert t J,
    searchPos_eq J, hJspec.symm, searchI_card J,
    fun h => by simpa only [searchSpend] using hQlt h⟩

/-- Infertile counts over consecutive windows add. -/
theorem card_infertile_add {Fert : ℕ → Prop} [DecidablePred Fert] {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a b).filter (fun d => ¬ Fert d)).card
        + ((Finset.Ico b c).filter (fun d => ¬ Fert d)).card
      = ((Finset.Ico a c).filter (fun d => ¬ Fert d)).card := by
  rw [← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive a b c)),
    ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- Infertile counts are monotone in the window. -/
theorem card_infertile_mono {Fert : ℕ → Prop} [DecidablePred Fert] {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ((Finset.Ico b c).filter (fun e => ¬ Fert e)).card
      ≤ ((Finset.Ico a d).filter (fun e => ¬ Fert e)).card :=
  Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico hab hcd))

/-! ### Interval-sum bookkeeping

Every charge in the general regime is levied on a window of levels, and the windows of
successive attempts and searches move strictly downward.  These two lemmas are how the
charges merge: consecutive windows are disjoint and their union is again a window, so
the accumulated charge is bounded by a *single* interval sum and hence by `ρ`.
-/

/-- Charges on two separated windows add up inside the enclosing window. -/
theorem sum_Ico_pair_le (B : Budget S) {a b c d : ℕ}
    (hbc : b ≤ c) (hac : a ≤ c) (hbd : b ≤ d) :
    (∑ e ∈ Finset.Ico a b, B.spend e) + (∑ e ∈ Finset.Ico c d, B.spend e)
      ≤ ∑ e ∈ Finset.Ico a d, B.spend e := by
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico c d) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ico] at hx hx'
    omega
  have hsub : Finset.Ico a b ∪ Finset.Ico c d ⊆ Finset.Ico a d := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_Ico] at hx ⊢
    omega
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => B.spend_nonneg x

/-- Charges are monotone in the window. -/
theorem sum_Ico_mono' (B : Budget S) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∑ e ∈ Finset.Ico b c, B.spend e ≤ ∑ e ∈ Finset.Ico a d, B.spend e := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => B.spend_nonneg x
  intro x hx
  simp only [Finset.mem_Ico] at hx ⊢
  omega

/-! ### The ledger bookkeeping -/

/--
The bookkeeping produced by the general chain construction run from depth `b`, where the
segment in progress already holds `base` links.

The five counters are: `z`, the number of links in the *best* segment produced (this is
what `Good` certifies, and `Near` locates); `A`, the number of extension attempts; `nb`,
the number of charged breaks; and `I`, `Q`, the two search capacities — single-level
skips at distinct infertile challenge depths, and levels inside disjoint blocked ranges.
All charges are levied inside one window `[b, N)`, so `Budget.sum_Ico_le` caps each of
them by `ρ`.

The conclusions are, in order:

* `Good z` and, when no break was charged, `Near z` — the best segment is the *last* one,
  so its final link sits within `localSpan` levels of the bottom of the graph.
* `base + A ≤ (nb + 1)(z + 1)` — the segment structure.  There are `nb + 1` segments;
  each contributes its completed links plus one final attempt, and `z` bounds every
  segment's link count.  `base` discounts the links already made in the segment in
  progress.
* every level of `[b, ℓ)` belongs to a search (`I + Q` of them) or to an attempt, which
  consumes at most `localSpan = h_0 - 1` levels — the constant-charge accounting;
* …and, *simultaneously*, the same levels counted by the ledger of `level ledger`: an
  attempt consumes at most `h_1` levels plus `2/ĝ` per unit of black pebble spent
  inside its own window.  Because the windows are disjoint, the whole construction pays
  the `2ρ/ĝ` slack once rather than once per link.  Carrying both bounds through the
  same induction is what lets one theorem match `latency_general`'s slope in the uniform
  regime and still survive breaks outside it;
* …and, when *no break was charged*, the **joint** ledger: the searches and the
  attempts occupy disjoint ranges of levels, so the infertile charge of
  `ChallengeBound.infertile_card_charge`, the blocked charge and the attempt charges can
  all be levied on one interval sum.  This is the entry that stops `ρ` being granted
  three times over, and it is why the clause carries its own window start `w` (`b` for a
  search, `b + 1` for a link) and its own head (`restartHead` for a search, `0` for a
  link);
* the blocked levels are paid for at rate `ĝ` on disjoint spends;
* the breaks are paid for at rate `β_δ(π) - π̂` on disjoint spends — this is
  `break-charge lemma`, at the sharper rate of `break_charge`.
-/
def GenLedger (S : Setting) (B : Budget S) (T : Tracking S) (Fert : ℕ → Prop)
    [DecidablePred Fert] (ℓ b base : ℕ) (Good Near : ℕ → Prop) (head : ℝ) (w : ℕ) : Prop :=
  ∃ z A nb I Q N : ℕ,
    Good z ∧
    (nb = 0 → 0 < z → Near z) ∧
    base + A ≤ (nb + 1) * (z + 1) ∧
    ℓ - b ≤ I + Q + A * localSpan S T ∧
    ((ℓ - b : ℕ) : ℝ) ≤ (I : ℝ) + (Q : ℝ) + (A : ℝ) * h₁ S T
      + 2 * (∑ d ∈ Finset.Ico (b + 1) N, B.spend d) / T.ghat ∧
    (nb = 0 → ((ℓ - b : ℕ) : ℝ) ≤ head + (A : ℝ) * h₁ S T
      + 2 * (∑ d ∈ Finset.Ico w N, B.spend d) / gmin S T) ∧
    I ≤ ((Finset.Ico b N).filter (fun d => ¬ Fert d)).card ∧
    (0 < Q → (Q : ℝ) * T.ghat < ∑ d ∈ Finset.Ico (b + 1) N, B.spend d) ∧
    (0 < nb → (nb : ℝ) * (S.betaD S.pi - T.lam) <
      ∑ d ∈ Finset.Ico (b + 1) N, B.spend d)


/-! ### `extension-attempt lemma` -/

namespace ChainSystem

variable {ℓ : ℕ} {Realizes : ℕ → Prop} (CS : ChainSystem.{u} S B T ℓ Realizes)

/--
**Chain extension with a possible break** (`extension-attempt lemma`).

An attempt from a link consumes at most `growthCap + contSpan = h_0 - 1` levels and ends in one of
three ways: the bottom of the graph, the next link, or a *break* — the tracked footprint
falling below `π̂`.  In the break case the levels traversed carry total spend greater
than `π - π̂`, which is the second conclusion of `fertile-continuation lemma` and the
charge that `break-charge lemma` uses.

The three outcomes are reaching the bottom, producing another link, or breaking the
tracked chain. The break charge bounds how often the third outcome can occur.
-/
theorem extension_attempt_gen (L : CS.Link) :
    ∃ b', CS.depth L < b' ∧
      (ℓ ≤ b' ∨
        (∃ L' : CS.Link, CS.depth L' = b' ∧ CS.count L' = CS.count L + 1) ∨
        S.betaD S.pi - T.lam <
          ∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d) ∧
      ((b' - CS.depth L : ℕ) : ℝ) ≤
        h₁ S T + 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d) / T.ghat ∧
      b' - CS.depth L ≤ localSpan S T := by
  classical
  set b := CS.depth L with hb
  set f := CS.wt L with hf
  have hbound : IsFootprintBound S B b f := CS.bound L
  have hinit : f b = T.σ := CS.init L
  have hexp : Expandable B T.ghat b := CS.expandable L
  have hbℓ : b < ℓ := CS.inside L
  have hf0 : 0 ≤ f b := by rw [hinit]; exact T.σ_pos.le
  have hfmax : f b ≤ S.αmax := by rw [hinit]; exact T.σ_lt_αmax.le
  have henc := hbound.le_αmax hf0 hfmax
  -- the growth phase: the first depth below `b` at which the footprint exceeds `π`
  have hex : ∃ k, S.pi < f (b + k + 1) ∨ ℓ ≤ b + k + 1 := ⟨ℓ, Or.inr (by omega)⟩
  set k0 := Nat.find hex with hk0
  set t1 := b + k0 + 1 with ht1
  have hspec : S.pi < f t1 ∨ ℓ ≤ t1 := Nat.find_spec hex
  have hmin : ∀ k, k < k0 → ¬(S.pi < f (b + k + 1) ∨ ℓ ≤ b + k + 1) := fun k hk =>
    Nat.find_min hex hk
  have hbt1 : b < t1 := by omega
  have hbelow : ∀ d, b ≤ d → d < t1 → f d ≤ S.pi := by
    intro d hbd hdt1
    rcases Nat.eq_or_lt_of_le hbd with rfl | hlt
    · rw [hinit]; exact T.σ_lt.le
    · obtain ⟨k, rfl⟩ : ∃ k, d = b + k + 1 := ⟨d - b - 1, by omega⟩
      have := hmin k (by omega)
      push Not at this
      exact this.1
  set growthSpend : ℝ := ∑ d ∈ Finset.Ico (b + 1) t1, B.spend d with hgrowthSpend
  have hgrowthSpend0 : 0 ≤ growthSpend := Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hgrowthSpendρ : growthSpend ≤ S.ρ := B.sum_Ico_le _ _
  have hgrowSpan : t1 - b ≤ growthSpan S T growthSpend :=
    growth_window hexp hbound hinit hbt1 hbelow
  have hgrow : t1 - b ≤ growthCap S T :=
    le_trans hgrowSpan
      (by simpa only [growthCap] using
        growthSpan_mono (S := S) (T := T) hgrowthSpendρ)
  have hgrow_real : ((t1 - b : ℕ) : ℝ) ≤ growthConst S T + growthSpend / T.ghat :=
    growthConst_window hexp hbound hinit hbt1 hbelow
  by_cases hend : ℓ ≤ t1
  · -- the graph is exhausted during the growth phase
    refine ⟨t1, hbt1, Or.inl hend, ?_, by simp only [localSpan]; omega⟩
    have hmono : growthSpend ≤ ∑ d ∈ Finset.Ico (b + 1) (t1 + 1), B.spend d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
      intro d hd
      simp only [Finset.mem_Ico] at hd ⊢
      omega
    have h1 : growthSpend / T.ghat
        ≤ 2 * (∑ d ∈ Finset.Ico (b + 1) (t1 + 1), B.spend d) / T.ghat := by
      rw [div_le_div_iff_of_pos_right T.ghat_pos]
      linarith
    have h2 : growthConst S T ≤ h₁ S T := by simp only [h₁]; linarith
    linarith
  push Not at hend
  have hcross : S.pi < f t1 := by
    rcases hspec with h | h
    · exact h
    · omega
  have hbound1 : IsFootprintBound S B t1 f := fun d hd => hbound d (by omega)
  have hmaxall : ∀ d, t1 ≤ d → f d ≤ S.αmax := fun d hd => (henc d (by omega)).2
  -- the search below `t1`, cut off at the first depth (if any) that breaks the floor
  obtain ⟨E, hEℓ, hfloorE, hbreak⟩ :
      ∃ E : ℕ, E ≤ ℓ ∧ (∀ d, t1 ≤ d → d < E → T.lam ≤ f d) ∧
        (E < ℓ → S.betaD S.pi - T.lam <
          ∑ d ∈ Finset.Ico (t1 + 1) (E + 1), B.spend d) := by
    by_cases hbrk : ∃ d, t1 ≤ d ∧ f d < T.lam
    · set D := Nat.find hbrk with hD
      have hDspec : t1 ≤ D ∧ f D < T.lam := Nat.find_spec hbrk
      have hDmin : ∀ d, d < D → ¬(t1 ≤ d ∧ f d < T.lam) := fun d hd => Nat.find_min hbrk hd
      have hfloorD : ∀ d, t1 ≤ d → d < D → T.lam ≤ f d := by
        intro d hd hdD
        by_contra hcon
        exact hDmin d hdD ⟨hd, lt_of_not_ge hcon⟩
      have ht1D : t1 < D := by
        rcases Nat.eq_or_lt_of_le hDspec.1 with heq | hlt
        · exact absurd hDspec.2 (by rw [← heq]; linarith [T.lam_lt_pi])
        · exact hlt
      refine ⟨min ℓ D, min_le_left _ _, fun d hd hdE =>
        hfloorD d hd (lt_of_lt_of_le hdE (min_le_right _ _)), ?_⟩
      intro hlt
      have hDmin' : min ℓ D = D := by omega
      rw [hDmin']
      refine break_charge hbound1 hcross.le (henc t1 (by omega)).1
        (hmaxall t1 (le_refl _)) ht1D ?_ hDspec.2
      intro d hd hdD
      exact S.gainD_nonneg
        ⟨le_of_lt (lt_of_lt_of_le T.αmin_lt_lam (hfloorD d (by omega) hdD)),
          hmaxall d (by omega)⟩
    · push Not at hbrk
      exact ⟨ℓ, le_refl ℓ, fun d hd _ => hbrk d hd, fun h => absurd h (by omega)⟩
  obtain ⟨t2, ht12, hout, hcont⟩ :=
    fertile_continuation_gen (E := E) hbound1 hcross.le hfloorE
      (fun d hd _ => hmaxall d hd)
  set continuationSpend : ℝ := ∑ d ∈ Finset.Ico (t1 + 1) t2, B.spend d with hcontinuationSpend
  have hcontinuationSpend0 : 0 ≤ continuationSpend :=
    Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hcontinuationSpendρ : continuationSpend ≤ S.ρ := B.sum_Ico_le _ _
  have hcont_real : ((t2 - t1 : ℕ) : ℝ) ≤ 2 * continuationSpend / T.ghat + 1 := by
    refine le_trans ?_ (contSpan_le (T := T) hcontinuationSpend0)
    exact_mod_cast hcont
  have hcontρ : t2 - t1 ≤ contSpan T S.ρ :=
    le_trans hcont (contSpan_mono (B.sum_Ico_le _ _))
  have hlocal : t2 - b ≤ localSpan S T := by
    simp only [localSpan]
    omega
  -- the two subwindows together are contained in `(b, t2]`
  have hcover : growthSpend + continuationSpend ≤
      ∑ d ∈ Finset.Ico (b + 1) (t2 + 1), B.spend d := by
    have hdisj : Disjoint (Finset.Ico (b + 1) t1) (Finset.Ico (t1 + 1) t2) := by
      rw [Finset.disjoint_left]
      intro a ha ha'
      simp only [Finset.mem_Ico] at ha ha'
      omega
    have hsub : Finset.Ico (b + 1) t1 ∪ Finset.Ico (t1 + 1) t2
        ⊆ Finset.Ico (b + 1) (t2 + 1) := by
      intro a ha
      simp only [Finset.mem_union, Finset.mem_Ico] at ha ⊢
      omega
    rw [hgrowthSpend, hcontinuationSpend, ← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => B.spend_nonneg d
  have hwindow : ((t2 - b : ℕ) : ℝ) ≤
      h₁ S T + 2 * (∑ d ∈ Finset.Ico (b + 1) (t2 + 1), B.spend d) / T.ghat := by
    have hsplit : ((t2 - b : ℕ) : ℝ) = ((t1 - b : ℕ) : ℝ) + ((t2 - t1 : ℕ) : ℝ) := by
      have : t2 - b = (t1 - b) + (t2 - t1) := by omega
      rw [this]; push_cast; ring
    have hgrowthSpend_le : growthSpend / T.ghat ≤ 2 * growthSpend / T.ghat := by
      rw [div_le_div_iff_of_pos_right T.ghat_pos]; linarith
    have hsum : 2 * growthSpend / T.ghat + 2 * continuationSpend / T.ghat
        ≤ 2 * (∑ d ∈ Finset.Ico (b + 1) (t2 + 1), B.spend d) / T.ghat := by
      rw [← add_div, div_le_div_iff_of_pos_right T.ghat_pos]
      linarith
    rw [hsplit]
    simp only [h₁]
    linarith
  by_cases hend2 : ℓ ≤ t2
  · exact ⟨t2, by omega, Or.inl hend2, hwindow, hlocal⟩
  push Not at hend2
  rcases hout with hE | ⟨hfert2, hexp2⟩
  · -- the attempt broke: charge it inside its own window
    refine ⟨t2, by omega, Or.inr (Or.inr ?_), hwindow, hlocal⟩
    have hspend := hbreak (by omega)
    have hsub : ∑ d ∈ Finset.Ico (t1 + 1) (E + 1), B.spend d
        ≤ ∑ d ∈ Finset.Ico (b + 1) (t2 + 1), B.spend d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
      intro d hd
      simp only [Finset.mem_Ico] at hd ⊢
      omega
    linarith
  · obtain ⟨L', hL'depth, hL'count⟩ := CS.extend L t2 (by omega) hend2 hfert2 hexp2
    exact ⟨t2, by omega, Or.inr (Or.inl ⟨L', hL'depth, hL'count⟩), hwindow, hlocal⟩


/-! ### The general construction and `latency_general` -/

/--
**The general construction and its ledger.**

Two mutually dependent statements, proved by a single induction on a level budget `m`:

* from a link at depth `b`, running attempts until the graph ends produces a
  `GenLedger` for the segment in progress;
* from a bare depth `b`, searching for a fertile `ĝ`-expandable challenge level and
  then running the construction from there produces a `GenLedger` with no segment in
  progress — its `z` may be `0`, which happens exactly when the graph ends before any
  restart level is found.

The induction is stratified rather than mutual: at each budget the link statement is
proved first (from the *smaller* budget, since an attempt strictly descends), and the
search statement then uses it at the *same* budget, since a search may find its level at
the depth it starts from.

`restart` is the only additional graph input over `ChainSystem`, and it is exactly
`first-source lemma` applied below a break.

This single accounting subsumes both `level ledger` and the level count of
`latency_general`; `exists_many_links_gen` reads both off it at once.
-/
theorem general_ledger (Fert : ℕ → Prop) [DecidablePred Fert]
    (restart : ∀ b : ℕ, b < ℓ → Fert b → Expandable B T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1)
    (Near : ℕ → Prop)
    (hNear : ∀ L : CS.Link, ℓ - CS.depth L ≤ localSpan S T → Near (CS.count L))
    (hgt : 0 < S.gtilde)
    (infCharge : ∀ a p : ℕ,
      ((((Finset.Ico a p).filter (fun d => ¬ Fert d)).card : ℕ) : ℝ)
        ≤ restartHead S B a + (∑ d ∈ Finset.Ico a p, B.spend d) / S.gtilde)
    (m : ℕ) :
    (∀ L : CS.Link, ℓ - CS.depth L ≤ m →
        GenLedger S B T Fert ℓ (CS.depth L) (CS.count L) Realizes Near 0
          (CS.depth L + 1)) ∧
      (∀ b : ℕ, ℓ - b ≤ m →
        GenLedger S B T Fert ℓ b 1 (fun z => z = 0 ∨ Realizes z) Near
          (restartHead S B b) b) := by
  have hdiv2 : ∀ x y : ℝ, x ≤ y → 2 * x / T.ghat ≤ 2 * y / T.ghat := by
    intro x y hxy
    rw [div_le_div_iff_of_pos_right T.ghat_pos]
    linarith
  have hsumnn : ∀ a c : ℕ, (0 : ℝ) ≤ ∑ d ∈ Finset.Ico a c, B.spend d := fun a c =>
    Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hspendnn : ∀ a c : ℕ, (0 : ℝ) ≤ 2 * (∑ d ∈ Finset.Ico a c, B.spend d) / T.ghat := by
    intro a c
    exact div_nonneg (by linarith [hsumnn a c]) T.ghat_pos.le
  -- the joint-charge arithmetic
  have hgm : 0 < gmin S T := gmin_pos (T := T) hgt
  have hjdiv : ∀ x y : ℝ, x ≤ y → 2 * x / gmin S T ≤ 2 * y / gmin S T := fun x y hxy =>
    gmin_charge_mono (T := T) hgt hxy
  have hjnn : ∀ a c : ℕ, (0 : ℝ) ≤ 2 * (∑ d ∈ Finset.Ico a c, B.spend d) / gmin S T := by
    intro a c
    exact div_nonneg (by linarith [hsumnn a c]) hgm.le
  have hjghat : ∀ x : ℝ, 0 ≤ x → 2 * x / T.ghat ≤ 2 * x / gmin S T := fun x hx =>
    ghat_charge_le_gmin (T := T) hgt hx
  have hjadd : ∀ x y : ℝ, 2 * x / gmin S T + 2 * y / gmin S T
      = 2 * (x + y) / gmin S T := by
    intro x y; rw [← add_div]; ring_nf
  induction m with
  | zero =>
      refine ⟨fun L hm => absurd (CS.inside L) (by omega), fun b hm => ?_⟩
      refine ⟨0, 0, 0, 0, 0, b, Or.inl rfl, fun _ h => absurd h (by omega), by omega,
        by omega, ?_, ?_, by simp, fun h => absurd h (by omega),
        fun h => absurd h (by omega)⟩
      · have hz : ℓ - b = 0 := by omega
        rw [hz]
        have := hspendnn (b + 1) b
        push_cast
        linarith
      · intro _
        have hz : ℓ - b = 0 := by omega
        rw [hz]
        have h0 := hjnn b b
        have := restartHead_nonneg (S := S) (B := B) b
        push_cast
        linarith
  | succ m ih =>
      -- the link statement, from the smaller budget
      have hA : ∀ L : CS.Link, ℓ - CS.depth L ≤ m + 1 →
          GenLedger S B T Fert ℓ (CS.depth L) (CS.count L) Realizes Near 0
            (CS.depth L + 1) := by
        intro L hm
        obtain ⟨b', hbb', hout, hled, hloc⟩ := CS.extension_attempt_gen L
        have hbℓ : CS.depth L < ℓ := CS.inside L
        rcases hout with hend | ⟨L', hL'depth, hL'count⟩ | hbrk
        · -- the graph is exhausted: this attempt is the segment's last
          have hmono : ((ℓ - CS.depth L : ℕ) : ℝ) ≤ ((b' - CS.depth L : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le_sub_right hend _
          refine ⟨CS.count L, 1, 0, 0, 0, b' + 1, CS.realizes L,
            fun _ _ => hNear L (by omega), by ring_nf; omega, by omega, ?_, ?_, by simp,
            fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
          · have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
            simp only [Nat.cast_zero, zero_add, hone, one_mul]
            linarith
          · intro _
            have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
            have hwiden := hjghat (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d)
              (hsumnn _ _)
            simp only [hone, one_mul, zero_add]
            linarith
        · -- the attempt completed the next link
          obtain ⟨z, A, nb, I, Q, N, hz, hnear, hcnt, hlev, hledger, hjnt, hinf, hQ, hnb⟩ :=
            ih.1 L' (by rw [hL'depth]; omega)
          rw [hL'count] at hcnt
          rw [hL'depth] at hlev hledger hjnt hinf hQ hnb
          obtain ⟨N', hNN, hNb⟩ : ∃ N', N ≤ N' ∧ b' + 1 ≤ N' :=
            ⟨max N (b' + 1), le_max_left _ _, le_max_right _ _⟩
          have hmul : (A + 1) * localSpan S T = A * localSpan S T + localSpan S T := by ring
          have hsplit : ((ℓ - CS.depth L : ℕ) : ℝ)
              ≤ ((ℓ - b' : ℕ) : ℝ) + ((b' - CS.depth L : ℕ) : ℝ) := by
            have : ℓ - CS.depth L ≤ (ℓ - b') + (b' - CS.depth L) := by omega
            exact_mod_cast this
          have hpair : (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d)
              + (∑ d ∈ Finset.Ico (b' + 1) N', B.spend d)
              ≤ ∑ d ∈ Finset.Ico (CS.depth L + 1) N', B.spend d :=
            sum_Ico_pair_le B (le_refl _) (by omega) hNb
          have hmono2 : ∑ d ∈ Finset.Ico (b' + 1) N, B.spend d
              ≤ ∑ d ∈ Finset.Ico (b' + 1) N', B.spend d :=
            sum_Ico_mono' B (le_refl _) hNN
          have hcastA : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
          refine ⟨z, A + 1, nb, I, Q, N', hz, hnear, by omega, by omega, ?_, ?_,
            le_trans hinf (card_infertile_mono (by omega) hNN),
            fun h => lt_of_lt_of_le (hQ h) (sum_Ico_mono' B (by omega) hNN),
            fun h => lt_of_lt_of_le (hnb h) (sum_Ico_mono' B (by omega) hNN)⟩
          · have hcomb : 2 * (∑ d ∈ Finset.Ico (b' + 1) N, B.spend d) / T.ghat
                + 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d) / T.ghat
                ≤ 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) N', B.spend d) / T.ghat := by
              rw [← add_div, div_le_div_iff_of_pos_right T.ghat_pos]
              linarith
            rw [hcastA, add_mul, one_mul]
            linarith
          · intro hnb0
            have hIH := hjnt hnb0
            have hattempt := hjghat
              (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d) (hsumnn _ _)
            have hIHmono : 2 * (∑ d ∈ Finset.Ico (b' + 1) N, B.spend d) / gmin S T
                ≤ 2 * (∑ d ∈ Finset.Ico (b' + 1) N', B.spend d) / gmin S T :=
              hjdiv _ _ hmono2
            have hcomb : 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d)
                  / gmin S T
                + 2 * (∑ d ∈ Finset.Ico (b' + 1) N', B.spend d) / gmin S T
                ≤ 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) N', B.spend d) / gmin S T := by
              rw [hjadd]
              exact hjdiv _ _ hpair
            rw [hcastA, add_mul, one_mul]
            linarith
        · -- the attempt broke: this segment ends and a restart is searched for below
          obtain ⟨z, A, nb, I, Q, N, hz, _hnear, hcnt, hlev, hledger, _hjnt, hinf, hQ,
            hnb⟩ := ih.2 b' (by omega)
          obtain ⟨N', hNN, hNb⟩ : ∃ N', N ≤ N' ∧ b' + 1 ≤ N' :=
            ⟨max N (b' + 1), le_max_left _ _, le_max_right _ _⟩
          have hz' : Realizes (max z (CS.count L)) := by
            rcases hz with rfl | hzr
            · rw [max_eq_right (Nat.zero_le _)]; exact CS.realizes L
            · rcases max_cases z (CS.count L) with ⟨he, _⟩ | ⟨he, _⟩
              · rw [he]; exact hzr
              · rw [he]; exact CS.realizes L
          have hmono : (nb + 1) * (z + 1) ≤ (nb + 1) * (max z (CS.count L) + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have hexpand : (nb + 1 + 1) * (max z (CS.count L) + 1)
              = (nb + 1) * (max z (CS.count L) + 1) + (max z (CS.count L) + 1) := by ring
          have hcle : CS.count L ≤ max z (CS.count L) := le_max_right _ _
          have hmul : (A + 1) * localSpan S T = A * localSpan S T + localSpan S T := by ring
          have hpair : (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d)
              + (∑ d ∈ Finset.Ico (b' + 1) N', B.spend d)
              ≤ ∑ d ∈ Finset.Ico (CS.depth L + 1) N', B.spend d :=
            sum_Ico_pair_le B (le_refl _) (by omega) hNb
          have hmono2 : ∑ d ∈ Finset.Ico (b' + 1) N, B.spend d
              ≤ ∑ d ∈ Finset.Ico (b' + 1) N', B.spend d :=
            sum_Ico_mono' B (le_refl _) hNN
          have hnb' : (nb : ℝ) * (S.betaD S.pi - T.lam)
              ≤ ∑ d ∈ Finset.Ico (b' + 1) N', B.spend d := by
            rcases Nat.eq_zero_or_pos nb with h0 | hpos
            · simp only [h0, Nat.cast_zero, zero_mul]
              exact Finset.sum_nonneg fun d _ => B.spend_nonneg d
            · exact le_trans (hnb hpos).le hmono2
          refine ⟨max z (CS.count L), A + 1, nb + 1, I, Q, N', hz',
            fun h => absurd h (by omega), by omega, by omega, ?_,
            fun h => absurd h (by omega),
            le_trans hinf (card_infertile_mono (by omega) hNN),
            fun h => lt_of_lt_of_le (hQ h) (sum_Ico_mono' B (by omega) hNN), ?_⟩
          · have hsplit : ((ℓ - CS.depth L : ℕ) : ℝ)
                ≤ ((ℓ - b' : ℕ) : ℝ) + ((b' - CS.depth L : ℕ) : ℝ) := by
              have : ℓ - CS.depth L ≤ (ℓ - b') + (b' - CS.depth L) := by omega
              exact_mod_cast this
            have hcomb : 2 * (∑ d ∈ Finset.Ico (b' + 1) N, B.spend d) / T.ghat
                + 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) (b' + 1), B.spend d) / T.ghat
                ≤ 2 * (∑ d ∈ Finset.Ico (CS.depth L + 1) N', B.spend d) / T.ghat := by
              rw [← add_div, div_le_div_iff_of_pos_right T.ghat_pos]
              linarith
            have hcastA : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
            rw [hcastA, add_mul, one_mul]
            linarith
          · intro _
            have hcast : ((nb + 1 : ℕ) : ℝ) * (S.betaD S.pi - T.lam)
                = (nb : ℝ) * (S.betaD S.pi - T.lam) + (S.betaD S.pi - T.lam) := by
              push_cast; ring
            rw [hcast]
            linarith
      refine ⟨hA, ?_⟩
      -- the search statement, at the same budget
      intro b hm
      obtain ⟨p, I₀, Q₀, hp, hfound, hI₀, hQ₀⟩ :=
        search_stops (B := B) (g := T.ghat) Fert b ℓ
      -- the search charge, levied on its own window `[b, p)`
      have hsearch : (I₀ : ℝ) + (Q₀ : ℝ)
          ≤ restartHead S B b + 2 * (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T := by
      -- the infertile skips are paid for by `infertile_card_charge`, the blocked levels
      -- by their own disjoint spends, and both windows sit inside `[b, p)`
        have hXnn : (0 : ℝ) ≤ ∑ d ∈ Finset.Ico b p, B.spend d := hsumnn b p
        have hmonoQ : ∑ d ∈ Finset.Ico (b + 1) p, B.spend d
            ≤ ∑ d ∈ Finset.Ico b p, B.spend d := sum_Ico_mono' B (by omega) (le_refl _)
        have hIle : (I₀ : ℝ)
            ≤ restartHead S B b + (∑ d ∈ Finset.Ico b p, B.spend d) / S.gtilde := by
          refine le_trans ?_ (infCharge b p)
          exact_mod_cast hI₀
        have hQle : (Q₀ : ℝ) ≤ (∑ d ∈ Finset.Ico b p, B.spend d) / T.ghat := by
          rcases Nat.eq_zero_or_pos Q₀ with h0 | hpos
          · rw [h0]
            exact_mod_cast div_nonneg hXnn T.ghat_pos.le
          · rw [le_div_iff₀ T.ghat_pos]
            exact le_trans (hQ₀ hpos).le hmonoQ
        have hg1 : (∑ d ∈ Finset.Ico b p, B.spend d) / S.gtilde
            ≤ (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T :=
          div_le_div_of_nonneg_left hXnn hgm gmin_le_gtilde
        have hg2 : (∑ d ∈ Finset.Ico b p, B.spend d) / T.ghat
            ≤ (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T :=
          div_le_div_of_nonneg_left hXnn hgm gmin_le_ghat
        have hsum2 : 2 * (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T
            = (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T
              + (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T := by
          rw [← add_div]; ring_nf
        rw [hsum2]
        linarith
      by_cases hpℓ : ℓ ≤ p
      · have hle : ℓ - b ≤ I₀ + Q₀ := by omega
        have hcast : ((ℓ - b : ℕ) : ℝ) ≤ (I₀ : ℝ) + (Q₀ : ℝ) := by
          have h : ((ℓ - b : ℕ) : ℝ) ≤ ((I₀ + Q₀ : ℕ) : ℝ) := Nat.cast_le.mpr hle
          simpa using h
        refine ⟨0, 0, 0, I₀, Q₀, p, Or.inl rfl, fun _ h => absurd h (by omega), by omega,
          by omega, ?_, ?_, hI₀, hQ₀, fun h => absurd h (by omega)⟩
        · have h1 := hspendnn (b + 1) p
          simp only [Nat.cast_zero, zero_mul, add_zero]
          linarith
        · intro _
          simp only [Nat.cast_zero, zero_mul, add_zero]
          linarith
      rcases hfound with hcon | ⟨hf, he⟩
      · exact absurd hcon hpℓ
      obtain ⟨L, hLdepth, hLcount⟩ := restart p (by omega) hf he
      obtain ⟨z, A, nb, I, Q, N, hz, hnear, hcnt, hlev, hledger, hjnt, hinf, hQ, hnb⟩ :=
        hA L (by rw [hLdepth]; omega)
      rw [hLcount] at hcnt
      rw [hLdepth] at hlev hledger hjnt hinf hQ hnb
      obtain ⟨N', hNN', hpN⟩ : ∃ N', N ≤ N' ∧ p + 1 ≤ N' :=
        ⟨max N (p + 1), le_max_left _ _, le_max_right _ _⟩
      have hbp : b ≤ p := by omega
      have hinf' : I₀ + I ≤ ((Finset.Ico b N').filter (fun d => ¬ Fert d)).card := by
        have hadd := card_infertile_add (Fert := Fert) hbp (by omega : p ≤ N')
        have h2 : I ≤ ((Finset.Ico p N').filter (fun d => ¬ Fert d)).card :=
          le_trans hinf (card_infertile_mono (le_refl _) hNN')
        omega
      have hpair : (∑ d ∈ Finset.Ico (b + 1) p, B.spend d)
          + (∑ d ∈ Finset.Ico (p + 1) N', B.spend d)
          ≤ ∑ d ∈ Finset.Ico (b + 1) N' , B.spend d :=
        sum_Ico_pair_le B (by omega) (by omega) (by omega : p ≤ N')
      have hQ₀' : (Q₀ : ℝ) * T.ghat ≤ ∑ d ∈ Finset.Ico (b + 1) p, B.spend d := by
        rcases Nat.eq_zero_or_pos Q₀ with h0 | hpos
        · simp only [h0, Nat.cast_zero, zero_mul]
          exact Finset.sum_nonneg fun d _ => B.spend_nonneg d
        · exact (hQ₀ hpos).le
      have hQ' : (Q : ℝ) * T.ghat ≤ ∑ d ∈ Finset.Ico (p + 1) N', B.spend d := by
        rcases Nat.eq_zero_or_pos Q with h0 | hpos
        · simp only [h0, Nat.cast_zero, zero_mul]
          exact Finset.sum_nonneg fun d _ => B.spend_nonneg d
        · exact le_trans (hQ hpos).le (sum_Ico_mono' B (le_refl _) hNN')
      have hsplit : ((ℓ - b : ℕ) : ℝ) ≤ ((p - b : ℕ) : ℝ) + ((ℓ - p : ℕ) : ℝ) := by
        have : ℓ - b ≤ (p - b) + (ℓ - p) := by omega
        exact_mod_cast this
      have hpb : ((p - b : ℕ) : ℝ) = (I₀ : ℝ) + (Q₀ : ℝ) := by
        have hpq : p - b = I₀ + Q₀ := by omega
        rw [hpq]; push_cast; ring
      refine ⟨z, A, nb, I₀ + I, Q₀ + Q, N', Or.inr hz, hnear, by omega, by omega, ?_,
        ?_, hinf', ?_, ?_⟩
      · have hdiv : 2 * (∑ d ∈ Finset.Ico (p + 1) N', B.spend d) / T.ghat
            ≤ 2 * (∑ d ∈ Finset.Ico (b + 1) N', B.spend d) / T.ghat := by
          refine hdiv2 _ _ ?_
          linarith [hsumnn (b + 1) p]
        have hdivN : 2 * (∑ d ∈ Finset.Ico (p + 1) N, B.spend d) / T.ghat
            ≤ 2 * (∑ d ∈ Finset.Ico (p + 1) N', B.spend d) / T.ghat :=
          hdiv2 _ _ (sum_Ico_mono' B (le_refl _) hNN')
        have hcastIQ : ((I₀ + I : ℕ) : ℝ) = (I₀ : ℝ) + (I : ℝ) := by push_cast; ring
        have hcastQQ : ((Q₀ + Q : ℕ) : ℝ) = (Q₀ : ℝ) + (Q : ℝ) := by push_cast; ring
        rw [hcastIQ, hcastQQ]
        linarith
      · -- the joint entry: the search window `[b, p)` and the attempt windows
        -- `(p, N')` are disjoint, so one interval sum pays for both
        intro hnb0
        have hIH := hjnt hnb0
        have hpairj : (∑ d ∈ Finset.Ico b p, B.spend d)
            + (∑ d ∈ Finset.Ico (p + 1) N', B.spend d)
            ≤ ∑ d ∈ Finset.Ico b N', B.spend d :=
          sum_Ico_pair_le B (by omega) (by omega) (by omega)
        have hIHmono : 2 * (∑ d ∈ Finset.Ico (p + 1) N, B.spend d) / gmin S T
            ≤ 2 * (∑ d ∈ Finset.Ico (p + 1) N', B.spend d) / gmin S T :=
          hjdiv _ _ (sum_Ico_mono' B (le_refl _) hNN')
        have hcombj : 2 * (∑ d ∈ Finset.Ico b p, B.spend d) / gmin S T
            + 2 * (∑ d ∈ Finset.Ico (p + 1) N', B.spend d) / gmin S T
            ≤ 2 * (∑ d ∈ Finset.Ico b N', B.spend d) / gmin S T := by
          rw [hjadd]
          exact hjdiv _ _ hpairj
        linarith
      · intro hpos
        have hcast : ((Q₀ + Q : ℕ) : ℝ) * T.ghat
            = (Q₀ : ℝ) * T.ghat + (Q : ℝ) * T.ghat := by push_cast; ring
        rw [hcast]
        rcases Nat.eq_zero_or_pos Q₀ with h0 | h0
        · have hstrict := lt_of_lt_of_le (hQ (by omega)) (sum_Ico_mono' B (le_refl _) hNN')
          linarith
        · have hstrict := hQ₀ h0
          linarith
      · intro hpos
        exact lt_of_lt_of_le (hnb hpos) (sum_Ico_mono' B (by omega) hNN')


/--
**The chain-counting core, break-aware.**

Running the construction from depth `0` covers the whole graph.  The four capacities of
`general_ledger` pay for every level: at most `s(ĝ, g̃)` belong to the initial and
restart searches (`challenge-floor lemma` caps `I`, disjoint blocked spends cap `Q`);
at most `b^max` attempts break (`break-charge lemma`, at the sharp rate of
`break_charge`), so there are at most `b^max + 1` segments; and the remaining levels are
charged to attempts, simultaneously at `h_0 - 1` levels each and through the ledger of
`level ledger`.  The best segment therefore holds at least `zMin` links, and — if no
break was charged — its final link lies within `localSpan` levels of the bottom.
-/
theorem exists_many_links_gen (GR : GeneralRegime S) (hρ : 0 < S.ρ)
    (chall : ChallengeBound S B)
    (restart : ∀ b : ℕ, b < ℓ → S.pi ≤ chall.f b → Expandable B T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1)
    (hℓ : s₀ S T < ℓ) :
    ∃ z, zMin S T ℓ ≤ z ∧ Realizes z ∧
      (bMax S T = 0 →
        ∃ Lₑ : CS.Link, CS.count Lₑ = z ∧ ℓ - CS.depth Lₑ ≤ localSpan S T) := by
  classical
  have hgt : 0 < S.gtilde := GR.gtilde_pos hρ
  have hgm : 0 < gmin S T := gmin_pos (T := T) hgt
  have hinfCharge : ∀ a p : ℕ,
      ((((Finset.Ico a p).filter (fun d => ¬ (S.pi ≤ chall.f d))).card : ℕ) : ℝ)
        ≤ restartHead S B a + (∑ d ∈ Finset.Ico a p, B.spend d) / S.gtilde := by
    intro a p
    have hcongr : (Finset.Ico a p).filter (fun d => ¬ (S.pi ≤ chall.f d))
        = (Finset.Ico a p).filter (fun d => chall.f d < S.pi) := by
      refine Finset.filter_congr ?_
      intro d _
      simp only [not_le]
    rw [hcongr]
    exact chall.infertile_card_charge GR.zeta_le GR.entry (GR.zetaFloor_lt_αmax hρ) a p
  obtain ⟨z, A, nb, I, Q, N, hz, hnear, hcnt, hlev, hledger, hjnt, hinf, hQ, hnb⟩ :=
    (CS.general_ledger (fun d => S.pi ≤ chall.f d) restart
      (fun z => ∃ Lₑ : CS.Link, CS.count Lₑ = z ∧ ℓ - CS.depth Lₑ ≤ localSpan S T)
      (fun L h => ⟨L, rfl, h⟩) hgt hinfCharge ℓ).2 0 (by omega)
  -- the three global capacities
  have hI : I ≤ infertileCap S S.gtilde := by
    refine le_trans hinf ?_
    have hcongr : (Finset.Ico 0 N).filter (fun d => ¬ (S.pi ≤ chall.f d))
        = (Finset.Ico 0 N).filter (fun d => chall.f d < S.pi) := by
      refine Finset.filter_congr ?_
      intro d _
      simp only [not_le]
    rw [hcongr]
    exact chall.infertile_card_le_gen GR.zeta_le GR.entry (GR.zetaFloor_lt_αmax hρ) N
  have hQcap : Q ≤ blockedCap S T.ghat := blocked_le_qB T.ghat_pos (B.sum_Ico_le _ _) hQ
  have hnbcap : nb ≤ bMax S T :=
    blocked_le_qB betaD_pi_sub_lam_pos (B.sum_Ico_le _ _) hnb
  have hIQ : I + Q ≤ sCap S T := by
    simp only [sCap, sCapOf]; omega
  have hHL : localSpan S T + 1 = h₀ S T := localSpan_succ_le_h₀ hρ
  -- the segment structure
  have hKpos : 1 ≤ (nb + 1) * (z + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨K, hK⟩ : ∃ K, K + 1 = (nb + 1) * (z + 1) :=
    ⟨(nb + 1) * (z + 1) - 1, by omega⟩
  have hAK : A ≤ K := by omega
  -- the constant-charge entry
  have hconst : (ℓ - s₀ S T) / ((bMax S T + 1) * h₀ S T) + 1 ≤ z := by
    have hAloc : A * localSpan S T ≤ K * localSpan S T :=
      Nat.mul_le_mul_right _ hAK
    have hKh : K * localSpan S T + K = K * h₀ S T := by
      rw [← hHL]; ring
    have hPh : K * h₀ S T + h₀ S T = ((nb + 1) * (z + 1)) * h₀ S T := by
      rw [← hK]; ring
    have hexp2 : ((nb + 1) * (z + 1)) * h₀ S T
        = ((nb + 1) * h₀ S T) * z + (nb + 1) * h₀ S T := by ring
    have hmz : ((nb + 1) * h₀ S T) * z ≤ ((bMax S T + 1) * h₀ S T) * z :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have hm1 : (nb + 1) * h₀ S T = nb * h₀ S T + h₀ S T := by ring
    have hnbh : nb * h₀ S T ≤ bMax S T * h₀ S T :=
      Nat.mul_le_mul_right _ hnbcap
    have hgen : s₀ S T = sCap S T + bMax S T * h₀ S T := rfl
    have hKge : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h0 | h
      · exfalso
        have hA0 : A = 0 := by omega
        rw [hA0, Nat.zero_mul] at hlev
        omega
      · exact h
    have hstep1 : ℓ ≤ sCap S T + K * localSpan S T := by omega
    have hstep2 : K * localSpan S T + K + h₀ S T
        = ((nb + 1) * h₀ S T) * z + (nb + 1) * h₀ S T := by omega
    have hstep3 : ((nb + 1) * h₀ S T) * z + (nb + 1) * h₀ S T
        ≤ ((bMax S T + 1) * h₀ S T) * z + bMax S T * h₀ S T
          + h₀ S T := by omega
    have hlt : ℓ - s₀ S T < ((bMax S T + 1) * h₀ S T) * z := by omega
    exact Nat.div_lt_of_lt_mul hlt
  -- the ledger entry
  have hledgerEntry :
      ⌈((ℓ : ℝ) - sCap S T - ledgerSlack S T - bMax S T * h₁ S T) /
          (((bMax S T : ℝ) + 1) * h₁ S T)⌉₊ ≤ z := by
    have hslack : 2 * (∑ d ∈ Finset.Ico (0 + 1) N, B.spend d) / T.ghat
        ≤ ledgerSlack S T := by
      rw [ledgerSlack, div_le_div_iff_of_pos_right T.ghat_pos]
      linarith [B.sum_Ico_le (0 + 1) N]
    have hIQreal : (I : ℝ) + (Q : ℝ) ≤ (sCap S T : ℝ) := by exact_mod_cast hIQ
    have hAreal : (A : ℝ) ≤ ((bMax S T : ℝ) + 1) * ((z : ℝ) + 1) - 1 := by
      have h1 : ((1 + A : ℕ) : ℝ) ≤ (((nb + 1) * (z + 1) : ℕ) : ℝ) := by exact_mod_cast hcnt
      have h2 : ((nb : ℝ) + 1) * ((z : ℝ) + 1)
          ≤ ((bMax S T : ℝ) + 1) * ((z : ℝ) + 1) := by
        have hnbr : (nb : ℝ) + 1 ≤ (bMax S T : ℝ) + 1 := by
          have hc : (nb : ℝ) ≤ (bMax S T : ℝ) := by exact_mod_cast hnbcap
          linarith
        exact mul_le_mul_of_nonneg_right hnbr (by positivity)
      push_cast at h1
      linarith
    have hℓcast : (ℓ : ℝ) = ((ℓ - 0 : ℕ) : ℝ) := by simp
    have h₁pos : (0 : ℝ) < h₁ S T := h₁_pos
    have hDpos : (0 : ℝ) < ((bMax S T : ℝ) + 1) * h₁ S T := by positivity
    have hmain : (ℓ : ℝ) ≤ (sCap S T : ℝ) + ledgerSlack S T
        + (((bMax S T : ℝ) + 1) * ((z : ℝ) + 1) - 1) * h₁ S T := by
      have hAh : (A : ℝ) * h₁ S T
          ≤ (((bMax S T : ℝ) + 1) * ((z : ℝ) + 1) - 1) * h₁ S T :=
        mul_le_mul_of_nonneg_right hAreal h₁pos.le
      rw [hℓcast]
      linarith
    have hring : (((bMax S T : ℝ) + 1) * ((z : ℝ) + 1) - 1) * h₁ S T
        = (z : ℝ) * (((bMax S T : ℝ) + 1) * h₁ S T)
          + (bMax S T : ℝ) * h₁ S T := by ring
    rw [hring] at hmain
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hDpos]
    linarith
  -- the joint entry: one budget for the searches and the attempts together
  have hjointEntry : jointEntry S T ℓ ≤ z := by
    unfold jointEntry
    split_ifs with hb0
    · have hnb0 : nb = 0 := by omega
      have hjoint := hjnt hnb0
      rw [restartHead_zero] at hjoint
      have hslack : 2 * (∑ d ∈ Finset.Ico 0 N, B.spend d) / gmin S T
          ≤ jointSlack S T := by
        rw [jointSlack, div_le_div_iff_of_pos_right hgm]
        linarith [B.sum_Ico_le 0 N]
      have hAz : A ≤ z := by
        rw [hnb0] at hcnt
        omega
      have hAreal : (A : ℝ) ≤ (z : ℝ) := by exact_mod_cast hAz
      have h₁pos : (0 : ℝ) < h₁ S T := h₁_pos
      have hℓcast : (ℓ : ℝ) = ((ℓ - 0 : ℕ) : ℝ) := by simp
      have hmain : (ℓ : ℝ) ≤ searchHead S + (z : ℝ) * h₁ S T + jointSlack S T := by
        have hAh : (A : ℝ) * h₁ S T ≤ (z : ℝ) * h₁ S T :=
          mul_le_mul_of_nonneg_right hAreal h₁pos.le
        rw [hℓcast]
        linarith
      refine Nat.ceil_le.mpr ?_
      rw [div_le_iff₀ h₁pos]
      linarith
    · exact Nat.zero_le _
  have hzpos : 1 ≤ z := le_trans (Nat.le_add_left 1 _) hconst
  have hzMinNoBreak : zMin S T ℓ ≤ z := by
    simp only [zMin, max_le_iff]
    exact ⟨hzpos, hledgerEntry, hjointEntry, hconst⟩
  rcases hz with rfl | hzr
  · omega
  · exact ⟨z, hzMinNoBreak, hzr, fun h => hnear (by omega) (by omega)⟩

/--
**Latency lower bound, one theorem for both parameter regimes** (`latency_general`,
strengthened to subsume `latency_general`).

`Realizes` is downward closed for the intended interpretation, exactly as in the development's
`latency_general`: the construction produces a chain of `z ≥ z_min` links, and the theorem is
stated at the displayed `z_min`.
-/
theorem latency_gen (GR : GeneralRegime S) (hρ : 0 < S.ρ)
    (chall : ChallengeBound S B)
    (restart : ∀ b : ℕ, b < ℓ → S.pi ≤ chall.f b → Expandable B T.ghat b →
      ∃ L : CS.Link, CS.depth L = b ∧ CS.count L = 1)
    (hℓ : s₀ S T < ℓ)
    (realizes_mono : ∀ ⦃z z'⦄, z ≤ z' → Realizes z' → Realizes z) :
    Realizes (zMin S T ℓ) := by
  obtain ⟨z, hz, hzr, _⟩ := CS.exists_many_links_gen GR hρ chall restart hℓ
  exact realizes_mono hz hzr


end ChainSystem

end ProofOfSpace

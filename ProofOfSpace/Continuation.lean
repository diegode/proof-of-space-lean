/-
# The search, the base case, and the fertile continuation

This file finishes the continuation argument in `sec:footprint-proof` of
`docs/explanation.tex`:

* `search_reaches` — `lem:first-source`: if a window of `q + blockedCap(g)` levels contains at
  most `q` infertile levels, it contains a fertile `g`-expandable level.
* `basecase` — `lem:first-source`: the challenge footprint reaches a fertile `g`-expandable
  level within `s(g,h) = infertileCap(h) + blockedCap(g)` levels.
* `basecase_gen` — `lem:first-source` again, outside the no-break entry condition,
  at the general infertile-gain floor `g̃` of `lem:challenge-floor`.
* `fertile_continuation` — `lem:fertile-continuation`: below a depth carrying weight at
  least `π`, a fertile `ĝ`-expandable level (or the bottom of the graph) is reached
  within `r(x) = max{0, 2⌈x/ĝ⌉ - 1}` levels, where `x` is the spend *inside* the window.
* `fertile_continuation_gen` — the same search with the footprint-bound hypotheses imposed only
  above a cut-off `E`, so that running past `E` can be a chain *break* rather than the
  bottom of the graph.  This is the form the general regime needs.

Both searches are instances of the single search of `Search.lean`; they differ only in how
the infertile count `I` is bounded — globally by `infertileCap` in the base case, locally by the
window spend in the continuation.
-/
import ProofOfSpace.Growth

namespace ProofOfSpace

open Set Finset

variable {S : Setting} {B : Budget S} {T : Tracking S}

/-! ### `lem:first-source`: the search -/

/-- The number of levels inside disjoint blocked ranges is at most `blockedCap(g)`. -/
theorem blocked_le_qB {g : ℝ} (hg : 0 < g) {Q : ℕ} {x : ℝ} (hx : x ≤ S.ρ)
    (hQ : 0 < Q → (Q : ℝ) * g < x) : Q ≤ blockedCap S g := by
  rcases Nat.eq_zero_or_pos Q with rfl | hpos
  · exact Nat.zero_le _
  · have h1 : (Q : ℝ) * g < S.ρ := lt_of_lt_of_le (hQ hpos) hx
    have h2 : (Q : ℝ) < S.ρ / g := by rw [lt_div_iff₀ hg]; exact h1
    have h3 : Q < ⌈S.ρ / g⌉₊ := Nat.lt_ceil.mpr h2
    simp only [blockedCap]
    omega

/--
**The fertile–expandable search** (`lem:first-source`).

If at most `q` of the depths in every prefix below `t` are infertile, then within
`q + blockedCap(g)` levels the search meets a level that is both fertile and `g`-expandable.
-/
theorem search_reaches {g : ℝ} (hg : 0 < g) (Fert : ℕ → Prop) [DecidablePred Fert]
    (t D q : ℕ)
    (hq : ∀ P, ((Finset.Ico t P).filter (fun d => ¬ Fert d)).card ≤ q)
    (hD : q + blockedCap S g ≤ D) :
    ∃ p, t ≤ p ∧ p ≤ t + D ∧ Fert p ∧ Expandable B g p := by
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ p, t ≤ p → p ≤ t + D → ¬(Fert p ∧ Expandable B g p) := by
    intro p h1 h2 ⟨hf, he⟩
    exact absurd he (hcon p h1 h2 hf)
  obtain ⟨I, Q, P, hP, hDIQ, hPeq, hI, hQ⟩ := search_bound (B := B) (g := g) Fert t D hbad
  have hIq : I ≤ q := le_trans hI (hq P)
  have hQq : Q ≤ blockedCap S g :=
    blocked_le_qB hg (B.sum_Ico_le (t + 1) P) hQ
  omega

/-! ### `lem:first-source`: the level it stops at -/

/--
**The first fertile expandable level** (`lem:first-source`, the pebbling half).

Under the entry condition, the challenge footprint reaches a level that is simultaneously
fertile and `g`-expandable within `s(g,h)` levels.  Clause (ii) of the paper statement —
the set `S_σ` of sources of long paths inside `F_π` — is the depth-robustness input,
recorded separately in `Chain.lean`.

The expandability parameter `g` is unconstrained beyond `g > 0`: `s(g,h) = infertileCap(h)+blockedCap(g)`
already absorbs the cost of a smaller `g` through `blockedCap(g) = ⌈ρ/g⌉ - 1`.  Only the
*fertility* parameter `h` has to satisfy `h ≤ g_π`, which is what `infertile_card_le`
needs.  Every caller instantiates both at `g = h = g_π`.
-/
theorem basecase {C : ChallengeBound S B} {g h : ℝ} (hg : 0 < g)
    (hh : 0 < h) (hhle : h ≤ S.gpi)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ) :
    ∃ b, b ≤ sCapOf S g h ∧ S.pi ≤ C.f b ∧ Expandable B g b := by
  classical
  have hq : ∀ P, ((Finset.Ico 0 P).filter (fun d => ¬ (S.pi ≤ C.f d))).card ≤ infertileCap S h := by
    intro P
    have hcongr : (Finset.Ico 0 P).filter (fun d => ¬ (S.pi ≤ C.f d))
        = (Finset.Ico 0 P).filter (fun d => C.f d < S.pi) := by
      refine Finset.filter_congr ?_
      intro d _
      simp only [not_le]
    rw [hcongr]
    rcases Nat.eq_zero_or_pos P with rfl | hpos
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
      have : Finset.Ico 0 (m + 1) = Finset.range (m + 1) := by
        rw [Finset.range_eq_Ico]
      rw [this]
      exact C.infertile_card_le hζmax hentry hh hhle m
  obtain ⟨p, _, hple, hfert, hexp⟩ :=
    search_reaches (B := B) hg (fun d => S.pi ≤ C.f d) 0 (sCapOf S g h) (infertileCap S h) hq
      (le_of_eq rfl)
  exact ⟨p, by omega, hfert, hexp⟩

/--
**The first fertile expandable level, general parameters** (`lem:first-source`).

Outside the entry condition `π̄ < ζ_δ - ρ` the infertile levels of the challenge
footprint can no longer be charged at rate `g_π`.  `lem:challenge-floor` replaces
that rate by `g̃`, and the same search then reaches a fertile `g`-expandable level
within `s(g, g̃) = infertileCap(g̃) + blockedCap(g)` levels.

The search is charged on `[0, P)` for arbitrary `P`, so — as the paragraph after
`lem:first-source` records — the same capacity also covers every *restart* search: the
searches run over disjoint level ranges and between them meet only a subset of the same
`infertileCap(g̃)` infertile challenge depths.  `Ledger.lean` is where that is used.
-/
theorem basecase_gen {C : ChallengeBound S B} {g : ℝ} (hg : 0 < g)
    (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor) (hlt : S.zetaFloor < S.αmax) :
    ∃ b, b ≤ sCapOf S g S.gtilde ∧ S.pi ≤ C.f b ∧ Expandable B g b := by
  classical
  have hq : ∀ P, ((Finset.Ico 0 P).filter (fun d => ¬ (S.pi ≤ C.f d))).card
      ≤ infertileCap S S.gtilde := by
    intro P
    have hcongr : (Finset.Ico 0 P).filter (fun d => ¬ (S.pi ≤ C.f d))
        = (Finset.Ico 0 P).filter (fun d => C.f d < S.pi) := by
      refine Finset.filter_congr ?_
      intro d _
      simp only [not_le]
    rw [hcongr]
    exact C.infertile_card_le_gen hζmax hentry hlt P
  obtain ⟨p, _, hple, hfert, hexp⟩ :=
    search_reaches (B := B) hg (fun d => S.pi ≤ C.f d) 0 (sCapOf S g S.gtilde)
      (infertileCap S S.gtilde) hq (le_of_eq rfl)
  exact ⟨p, by omega, hfert, hexp⟩

/-! ### `lem:fertile-continuation` -/

/-- The constant-charge continuation span `r(x) = max{0, 2⌈x/ĝ⌉ - 1}`. -/
noncomputable def contSpan (T : Tracking S) (x : ℝ) : ℕ := 2 * ⌈x / T.ghat⌉₊ - 1

theorem contSpan_mono {x y : ℝ} (hxy : x ≤ y) : contSpan T x ≤ contSpan T y := by
  have hd : (y - x) / T.ghat = y / T.ghat - x / T.ghat := by ring
  have : x / T.ghat ≤ y / T.ghat := by
    have := div_nonneg (sub_nonneg.mpr hxy) T.ghat_pos.le
    linarith [hd ▸ this]
  simp only [contSpan]
  have := Nat.ceil_le_ceil this
  omega

/-- `r(x) ≤ 2x/ĝ + 1`. -/
theorem contSpan_le {x : ℝ} (hx : 0 ≤ x) :
    ((contSpan T x : ℕ) : ℝ) ≤ 2 * x / T.ghat + 1 := by
  have hy : 0 ≤ x / T.ghat := div_nonneg hx T.ghat_pos.le
  rcases Nat.eq_zero_or_pos ⌈x / T.ghat⌉₊ with hc | hc
  · have hz : contSpan T x = 0 := by simp only [contSpan, hc]
    rw [hz]
    have h2 : (0:ℝ) ≤ 2 * x / T.ghat := div_nonneg (by linarith) T.ghat_pos.le
    push_cast
    linarith
  · obtain ⟨c, hceq⟩ : ∃ c, ⌈x / T.ghat⌉₊ = c + 1 := ⟨⌈x / T.ghat⌉₊ - 1, by omega⟩
    have hclt : (c : ℝ) < x / T.ghat := by
      have := Nat.lt_ceil (n := c) (a := x / T.ghat)
      rw [hceq] at this
      exact this.mp (by omega)
    have hval : contSpan T x = 2 * c + 1 := by simp only [contSpan, hceq]; omega
    rw [hval]
    have : (2:ℝ) * x / T.ghat = 2 * (x / T.ghat) := by ring
    push_cast
    linarith

/--
**Fertile continuation, break, or exhaustion** (`lem:fertile-continuation`).

Search forward from a depth `t1` whose tracked footprint weighs at least `π`.  The
hypotheses are imposed only *above the cut-off* `E`: the tracked footprint has to stay
above the tracking floor `π̂` and below `α_δ^max` only at the depths `t1 ≤ d < E`.
Within `r(x)` levels the search reaches a fertile `ĝ`-expandable depth or runs past `E`;
here `x` is the spend strictly inside the traversed window.

In the no-break regime `E` is the bottom `ℓ` of the graph, because `post_floor` and the
budget inequality `ρ < β_δ(π) - π̄` supply the floor everywhere below `t1`
(`fertile_continuation`).  In the general regime the floor is available only down to the
first depth at which the footprint *breaks* through `π̂`, and running past `E` is then
the break outcome rather than exhaustion.

The two capacities are charged exactly as in the uniform proof, with one refinement: the
infertile count is charged on the window `[t1, searchPos (J-1) + 1)`, which stops before
the search's final jump and therefore stays strictly above the cut-off, rather than on the
whole traversed range, which a blocked range may push past it.
-/
theorem fertile_continuation_gen {f : ℕ → ℝ} {t1 E : ℕ}
    (hbound : IsFootprintBound S B t1 f) (hfert : S.pi ≤ f t1)
    (hfloor : ∀ d, t1 ≤ d → d < E → T.lam ≤ f d)
    (hmax : ∀ d, t1 ≤ d → d < E → f d ≤ S.αmax) :
    ∃ t2, t1 ≤ t2 ∧
      (E ≤ t2 ∨ (S.pi ≤ f t2 ∧ Expandable B T.ghat t2)) ∧
      t2 - t1 ≤ contSpan T (∑ d ∈ Finset.Ico (t1 + 1) t2, B.spend d) := by
  classical
  set Fert : ℕ → Prop := fun d => S.pi ≤ f d with hFert
  -- the search stops at the first fertile expandable position, or when it leaves `[t1, E)`
  have hex : ∃ j, (Fert (searchPos B T.ghat Fert t1 j) ∧
      Expandable B T.ghat (searchPos B T.ghat Fert t1 j)) ∨
      E ≤ searchPos B T.ghat Fert t1 j := by
    refine ⟨E, Or.inr ?_⟩
    have := le_searchPos (B := B) (g := T.ghat) (Fert := Fert) (t := t1) E
    omega
  set J := Nat.find hex with hJ
  set t2 := searchPos B T.ghat Fert t1 J with ht2
  have hJspec : (Fert t2 ∧ Expandable B T.ghat t2) ∨ E ≤ t2 := Nat.find_spec hex
  have hbad : ∀ j, j < J →
      ¬(Fert (searchPos B T.ghat Fert t1 j) ∧
        Expandable B T.ghat (searchPos B T.ghat Fert t1 j)) := by
    intro j hj hcon
    exact (Nat.find_min hex hj) (Or.inl hcon)
  have hcut : ∀ j, j < J → searchPos B T.ghat Fert t1 j < E := by
    intro j hj
    have := Nat.find_min hex hj
    push Not at this
    exact this.2
  have ht1t2 : t1 ≤ t2 := base_le_searchPos J
  refine ⟨t2, ht1t2, hJspec.symm, ?_⟩
  -- the two capacities
  obtain ⟨_, hQlt⟩ := searchQ_spend (B := B) (g := T.ghat) (Fert := Fert) (t := t1) hbad J
    (le_refl J)
  have hpos := searchPos_eq (B := B) (g := T.ghat) (Fert := Fert) (t := t1) J
  set x : ℝ := ∑ d ∈ Finset.Ico (t1 + 1) t2, B.spend d with hx
  have hxnn : 0 ≤ x := Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hspend : searchSpend (B := B) (g := T.ghat) (Fert := Fert) (t := t1) J = x := by
    simp only [searchSpend, hx, ht2]
  -- the infertile skips, charged on a window that stops before the search's last jump
  have hIle : searchI B T.ghat Fert t1 J ≤ ⌈x / T.ghat⌉₊ := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · simp [hJ0, searchI]
    obtain ⟨j, hjJ⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
    set p := searchPos B T.ghat Fert t1 j with hp
    have hpE : p < E := hcut j (by omega)
    have hpt1 : t1 ≤ p := base_le_searchPos j
    have hp1t2 : p + 1 ≤ t2 := by
      have := searchPos_lt_succ (B := B) (g := T.ghat) (Fert := Fert) (t := t1) j
      rw [ht2, hjJ]; omega
    set K := ((Finset.Ico t1 (p + 1)).filter (fun d => ¬ Fert d)).card with hK
    have hIK : searchI B T.ghat Fert t1 J ≤ K := by
      rw [hjJ, hK]
      exact searchI_card_succ (B := B) (g := T.ghat) (Fert := Fert) (t := t1) j
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · omega
    -- gains along the tracked footprint bound, unpebbled above the cut-off
    have hgnn : ∀ d, t1 ≤ d → d < p + 1 → 0 ≤ S.gainD (f d) := by
      intro d hd hdp
      have hdE : d < E := by omega
      exact S.gainD_nonneg
        ⟨le_of_lt (lt_of_lt_of_le T.αmin_lt_lam (hfloor d hd hdE)), hmax d hd hdE⟩
    have hginf : ∀ d, t1 ≤ d → d < p + 1 → f d < S.pi → T.ghat ≤ S.gainD (f d) := by
      intro d hd hdp hlt
      have hdE : d < E := by omega
      exact T.ghat_le_gainD ⟨hfloor d hd hdE, hlt.le⟩
    have hKcongr : (Finset.Ico t1 (p + 1)).filter (fun d => ¬ Fert d)
        = (Finset.Ico t1 (p + 1)).filter (fun d => f d < S.pi) := by
      refine Finset.filter_congr ?_
      intro d _
      simp only [hFert, not_le]
    have hb := hbound.infertile_budget (P := p + 1) hgnn hginf T.ghat_nonneg hKpos
      (by rw [hK, hKcongr])
    have hwin : ∑ d ∈ Finset.Ico (t1 + 1) (p + 1), B.spend d ≤ x := by
      rw [hx]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
      intro d hd
      simp only [Finset.mem_Ico] at hd ⊢
      omega
    have hKx : ((K : ℝ) - 1) * T.ghat < x := by linarith
    obtain ⟨k, hkeq⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    have hcast : (k : ℝ) < x / T.ghat := by
      rw [lt_div_iff₀ T.ghat_pos]
      rw [hkeq] at hKx; push_cast at hKx; linarith
    have := Nat.lt_ceil.mpr hcast
    omega
  -- the blocked ranges, charged to their own disjoint spends
  have hQle : searchQ B T.ghat Fert t1 J ≤ ⌈x / T.ghat⌉₊ - 1 := by
    rcases Nat.eq_zero_or_pos (searchQ B T.ghat Fert t1 J) with h0 | hpos'
    · omega
    · have h1 := hQlt hpos'
      rw [hspend] at h1
      have h2 : (searchQ B T.ghat Fert t1 J : ℝ) < x / T.ghat := by
        rw [lt_div_iff₀ T.ghat_pos]; exact h1
      have := Nat.lt_ceil.mpr h2
      omega
  have hsum : t2 - t1 = searchI B T.ghat Fert t1 J + searchQ B T.ghat Fert t1 J := by
    rw [ht2, hpos]; omega
  simp only [contSpan]
  omega

/--
**Fertile continuation or exhaustion** (`lem:fertile-continuation`, uniform form).

Search forward from a depth `t1` whose tracked footprint weighs at least `π` and stays
above the tracking floor `π̂`.  Within `r(x)` levels the search reaches a fertile
`ĝ`-expandable depth, or runs past the bottom `ℓ` of the graph; here `x` is the spend
strictly inside the traversed window.  Chains cannot break under these hypotheses, so
this is the specialization of `fertile_continuation_gen` with cut-off `ℓ`.
-/
theorem fertile_continuation {f : ℕ → ℝ} {t1 ℓ : ℕ}
    (hbound : IsFootprintBound S B t1 f) (hfert : S.pi ≤ f t1)
    (hfloor : ∀ d, t1 ≤ d → T.lam ≤ f d)
    (hmax : ∀ d, t1 ≤ d → f d ≤ S.αmax) :
    ∃ t2, t1 ≤ t2 ∧
      (ℓ ≤ t2 ∨ (S.pi ≤ f t2 ∧ Expandable B T.ghat t2)) ∧
      t2 - t1 ≤ contSpan T (∑ d ∈ Finset.Ico (t1 + 1) t2, B.spend d) :=
  fertile_continuation_gen hbound hfert (fun d hd _ => hfloor d hd) (fun d hd _ => hmax d hd)

end ProofOfSpace

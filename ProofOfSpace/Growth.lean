/-
# The mirror-based growth theorem

This file formalizes part of `footprint analysis` in this development:

* `mirror_floor` — `mirror-floor lemma`: while the footprint of a source set of weight `σ`
  sitting at a `ĝ`-expandable depth stays below `π`, it never falls below the tracking
  floor `π̂`.
* `growth_exhaustion` — the gain-sum core of `growth-window lemma`.
* `growth_window` / `growth_window_real` — `growth-window lemma` proper: the first crossing of
  `π` happens within `u(x) = max{1, ⌊(π - σ + x)/ĝ⌋}` levels, where `x` is the spend
  *inside the window*, and `u(x) ≤ a + x/ĝ`.
* `post_floor` — the no-break form of `break-charge lemma`: once a footprint reaches `π` it
  never afterwards drops
  below `β_δ(π) - ρ`.

Everything is stated in the depth indexing of `Footprint.lean`: depth `d` is Reyzin's
published level `ℓ - d`, so the depth `t + i` here is the corresponding level `ℓ - t - i`, and
moving to larger depth is moving to smaller level.
-/
import ProofOfSpace.Tracking
import ProofOfSpace.Search

namespace ProofOfSpace

open Set Finset

variable {S : Setting} {B : Budget S} {T : Tracking S} {t : ℕ} {f : ℕ → ℝ}

/-! ### The gain accumulated by a tracked source -/

/--
The gain accumulated over `i ≥ 1` levels below a source of weight `σ` is at least
`(i+1) ĝ`: the source step contributes `gain_δ(σ) ≥ 2 ĝ`, and each of the `i - 1`
later steps contributes at least `ĝ` by `tracking-gain bound`.
-/
theorem gain_sum_ge (hinit : f t = T.σ) {i : ℕ} (hi : 1 ≤ i)
    (hfloor : ∀ m, m < i → T.lam ≤ f (t + m))
    (hle : ∀ m, m < i → f (t + m) ≤ S.pi) :
    ((i : ℝ) + 1) * T.ghat ≤ ∑ m ∈ Finset.range i, S.gainD (f (t + m)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hhead : 2 * T.ghat ≤ S.gainD (f (t + 0)) := by
    rw [Nat.add_zero, hinit]
    exact T.two_ghat_le_gainD_σ
  have htail : (j : ℝ) * T.ghat ≤ ∑ m ∈ Finset.range j, S.gainD (f (t + (m + 1))) := by
    have hb : ∀ m ∈ Finset.range j, T.ghat ≤ S.gainD (f (t + (m + 1))) := by
      intro m hm
      have hm' : m + 1 < j + 1 := by simpa using Nat.succ_lt_succ (Finset.mem_range.mp hm)
      exact T.ghat_le_gainD ⟨hfloor _ hm', hle _ hm'⟩
    have := Finset.card_nsmul_le_sum (Finset.range j) (fun m => S.gainD (f (t + (m + 1))))
      T.ghat hb
    simpa [nsmul_eq_mul] using this
  have hsum : ∑ m ∈ Finset.range j, S.gainD (f (t + (m + 1)))
      = ∑ m ∈ Finset.range j, S.gainD (f (t + m + 1)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Nat.add_assoc]
  rw [hsum] at htail
  push_cast
  linarith

/-! ### `mirror-floor lemma` -/

/--
**Mirror tracking floor** (`mirror-floor lemma`).

Let `f` be the footprint bound of an unpebbled set of weight `σ` at a
`ĝ`-expandable depth `t`.  If the footprint does not exceed `π` during the next `j`
levels, then it stays at least `π̂` throughout those levels.
-/
theorem mirror_floor (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f)
    (hinit : f t = T.σ) {j : ℕ} (hle : ∀ i, i ≤ j → f (t + i) ≤ S.pi) :
    ∀ i, i ≤ j → T.lam ≤ f (t + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hij
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [Nat.add_zero, hinit]; exact T.lam_le_σ
    · have hfloor : ∀ m, m < i → T.lam ≤ f (t + m) := fun m hm => ih m hm (by omega)
      have hle' : ∀ m, m < i → f (t + m) ≤ S.pi := fun m hm => hle m (by omega)
      have hgain := gain_sum_ge hinit hi hfloor hle'
      have hspend := hexp i hi
      have hid := hbound.sum_le (le_refl t) i
      rw [hinit] at hid
      have : T.σ ≤ f (t + i) := by linarith
      exact le_trans T.lam_le_σ this

/-! ### `growth-window lemma` -/

/--
**`growth-window inequality`.**  If the footprint stays at most `π` for `m ≥ 1` levels below a
`ĝ`-expandable source of weight `σ`, then `(m+1) ĝ ≤ π - σ + x`, where `x` is the
spend inside the window.
-/
theorem growth_exhaustion (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f)
    (hinit : f t = T.σ) {m : ℕ} (hm : 1 ≤ m) (hle : ∀ i, i ≤ m → f (t + i) ≤ S.pi) :
    ((m : ℝ) + 1) * T.ghat
      ≤ S.pi - T.σ + ∑ d ∈ Finset.Ico (t + 1) (t + m + 1), B.spend d := by
  have hfloor := mirror_floor hexp hbound hinit hle
  have hgain := gain_sum_ge hinit hm (fun k hk => hfloor k (by omega))
    (fun k hk => hle k (by omega))
  have hid := hbound.sum_le (le_refl t) m
  rw [hinit] at hid
  have hshift : ∑ k ∈ Finset.range m, B.spend (t + k + 1)
      = ∑ d ∈ Finset.Ico (t + 1) (t + m + 1), B.spend d := B.sum_shift t m
  rw [hshift] at hid
  have := hle m (le_refl m)
  linarith

/-- The constant-charge growth window `u(x) = max{1, ⌊(π - σ + x)/ĝ⌋}`. -/
noncomputable def growthSpan (S : Setting) (T : Tracking S) (x : ℝ) : ℕ :=
  max 1 ⌊(S.pi - T.σ + x) / T.ghat⌋₊

/--
**`growth-window lemma`, integer form.**  If `t1 > t` is the first level at which the footprint
of the source exceeds `π`, then `t1 - t ≤ u(x)`, where `x` is the spend strictly between
`t` and `t1`.
-/
theorem growth_window (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f)
    (hinit : f t = T.σ) {t1 : ℕ} (ht1 : t < t1)
    (hbelow : ∀ d, t ≤ d → d < t1 → f d ≤ S.pi) :
    t1 - t ≤ growthSpan S T (∑ d ∈ Finset.Ico (t + 1) t1, B.spend d) := by
  obtain ⟨m, rfl⟩ : ∃ m, t1 = t + m + 1 := ⟨t1 - t - 1, by omega⟩
  have hle : ∀ i, i ≤ m → f (t + i) ≤ S.pi := fun i hi => hbelow _ (by omega) (by omega)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [growthSpan]
    have : t + 0 + 1 - t = 1 := by omega
    rw [this]
    exact le_max_left _ _
  · have hex := growth_exhaustion hexp hbound hinit hm hle
    have hcast : ((t + m + 1 - t : ℕ) : ℝ) = (m : ℝ) + 1 := by
      have : t + m + 1 - t = m + 1 := by omega
      rw [this]; push_cast; ring
    have hfloorle : ((t + m + 1 - t : ℕ) : ℝ)
        ≤ (S.pi - T.σ + ∑ d ∈ Finset.Ico (t + 1) (t + m + 1), B.spend d) / T.ghat := by
      rw [hcast, le_div_iff₀ T.ghat_pos]
      exact hex
    refine le_trans (Nat.le_floor hfloorle) (le_max_right _ _)

/-- `a = max{1, (π - σ)/ĝ}`, the asymptotic growth span of `optimized span bound`. -/
noncomputable def asymptoticGrowth (S : Setting) (T : Tracking S) : ℝ :=
  max 1 ((S.pi - T.σ) / T.ghat)

theorem one_le_asymptoticGrowth : 1 ≤ asymptoticGrowth S T := le_max_left _ _

/-- `u(x) ≤ a + x/ĝ`, the real-valued form of `growth-window lemma`. -/
theorem growthSpan_le {x : ℝ} (hx : 0 ≤ x) :
    ((growthSpan S T x : ℕ) : ℝ) ≤ asymptoticGrowth S T + x / T.ghat := by
  have hdiv : 0 ≤ x / T.ghat := div_nonneg hx T.ghat_pos.le
  have hA : (1:ℝ) ≤ asymptoticGrowth S T := one_le_asymptoticGrowth
  have hnum : 0 ≤ (S.pi - T.σ + x) / T.ghat :=
    div_nonneg (by linarith [T.σ_lt]) T.ghat_pos.le
  simp only [growthSpan, Nat.cast_max, Nat.cast_one]
  refine max_le (by linarith) ?_
  refine le_trans (Nat.floor_le hnum) ?_
  have hsplit : (S.pi - T.σ + x) / T.ghat = (S.pi - T.σ) / T.ghat + x / T.ghat := by ring
  have hmax : (S.pi - T.σ) / T.ghat ≤ asymptoticGrowth S T := le_max_right _ _
  rw [hsplit]
  linarith

/-- `growthSpan` is monotone in the charge, so granting the adversary the whole budget
gives the constant-charge value `growthCap`. -/
theorem growthSpan_mono {x y : ℝ} (hxy : x ≤ y) :
    growthSpan S T x ≤ growthSpan S T y := by
  refine max_le_max (le_refl 1) (Nat.floor_le_floor ?_)
  have hd : (S.pi - T.σ + y) / T.ghat - (S.pi - T.σ + x) / T.ghat = (y - x) / T.ghat := by
    field_simp
    ring
  have := div_nonneg (sub_nonneg.mpr hxy) T.ghat_pos.le
  linarith

/-! ### The post-fertile floor -/

/--
**Post-fertile floor**, the no-break form of `break-charge lemma`.

Assume `β_δ(π) - ρ > α_δ^min`.  If the footprint reaches `π` at depth `d0`, then below
`d0` it never falls under `β_δ(π) - ρ`.
-/
theorem post_floor (hbound : IsFootprintBound S B t f) (h0 : 0 ≤ f t) (hmax : f t ≤ S.αmax)
    (hcond : S.αmin + S.ρ < S.betaD S.pi)
    {d0 : ℕ} (hd0 : t ≤ d0) (hfert : S.pi ≤ f d0) :
    ∀ d, d0 < d → S.betaD S.pi - S.ρ ≤ f d := by
  have henc := hbound.le_αmax h0 hmax
  -- one expansion step at the fertile depth
  have hstep : S.betaD S.pi - B.spend (d0 + 1) ≤ f (d0 + 1) := by
    have hmemIcc : f d0 ∈ Icc (0:ℝ) 1 :=
      ⟨(henc d0 hd0).1, le_trans (henc d0 hd0).2 S.αmax_le_one⟩
    have hmono : S.betaD S.pi ≤ S.betaD (f d0) := by
      rcases lt_or_eq_of_le hfert with hlt | heq
      · exact (S.betaD_strictMonoOn S.pi_mem_Icc hmemIcc hlt).le
      · rw [heq]
    have := hbound.step_ge hd0
    have hb : S.betaD (f d0) = f d0 + S.gainD (f d0) := S.betaD_eq _
    rw [hb] at hmono
    linarith
  -- and then the general floor invariant from depth `d0 + 1`
  have hbase : S.betaD S.pi - ∑ d ∈ Finset.Ico (d0 + 1) (d0 + 1 + 1), B.spend d
      ≤ f (d0 + 1) := by
    rw [Finset.sum_Ico_succ_top (le_refl (d0 + 1)), Finset.Ico_self, Finset.sum_empty,
      zero_add]
    exact hstep
  have hbound' : IsFootprintBound S B (d0 + 1) f := fun d hd => hbound d (by omega)
  have hfl := hbound'.floor (a := d0 + 1) (le_refl _) hcond (henc (d0 + 1) (by omega)).2 hbase
  intro d hd
  have := (hfl d (by omega)).1
  have hb := B.sum_Ico_le (d0 + 1) (d + 1)
  linarith

/--
**The window charge of a break**, the sharp form of the second conclusion of
`fertile-continuation lemma`.

If the tracked footprint is fertile at `t1`, and `D` is the first depth below `t1` at
which it falls under `c`, then the black pebbles placed strictly inside `(t1, D]` weigh
more than `β_δ(π) - c`.

This is `break-charge lemma`: the expansion step at `t1` itself is kept rather than
discarded, so the charge is `β_δ(π) - c` and not merely `π - c`.  That one step is what
turns the no-break condition `ρ < β_δ(π) - π̄` into the statement
that *no* break can be paid for, and hence what lets a single break-aware latency
theorem subsume the no-break one instead of losing a factor `b^max + 1` to it.

This is the local, window-charged counterpart of `post_floor`, which draws the same
conclusion from the whole budget `ρ`.
-/
theorem break_charge {f : ℕ → ℝ} {t1 D : ℕ} {c : ℝ}
    (hbound : IsFootprintBound S B t1 f) (hfert : S.pi ≤ f t1) (h0 : 0 ≤ f t1)
    (hmax : f t1 ≤ S.αmax) (ht1D : t1 < D)
    (hgain : ∀ d, t1 < d → d < D → 0 ≤ S.gainD (f d))
    (hD : f D < c) :
    S.betaD S.pi - c < ∑ d ∈ Finset.Ico (t1 + 1) (D + 1), B.spend d := by
  -- one expansion step at the fertile depth
  have hmemIcc : f t1 ∈ Icc (0 : ℝ) 1 := ⟨h0, le_trans hmax S.αmax_le_one⟩
  have hmono : S.betaD S.pi ≤ S.betaD (f t1) := by
    rcases lt_or_eq_of_le hfert with hlt | heq
    · exact (S.betaD_strictMonoOn S.pi_mem_Icc hmemIcc hlt).le
    · rw [heq]
  have hstep : S.betaD S.pi - B.spend (t1 + 1) ≤ f (t1 + 1) := by
    have hs := hbound.step_ge (le_refl t1)
    rw [S.betaD_eq (f t1)] at hmono
    linarith
  -- and the nonnegative-gain descent from there to the break
  obtain ⟨i, hi⟩ : ∃ i, D = t1 + 1 + i := ⟨D - (t1 + 1), by omega⟩
  have hbound' : IsFootprintBound S B (t1 + 1) f := fun d hd => hbound d (by omega)
  have hid := hbound'.sum_le (le_refl (t1 + 1)) i
  have hgains : 0 ≤ ∑ m ∈ Finset.range i, S.gainD (f (t1 + 1 + m)) :=
    Finset.sum_nonneg fun m hm => hgain _ (by omega)
      (by have := Finset.mem_range.mp hm; omega)
  have hshift : ∑ m ∈ Finset.range i, B.spend (t1 + 1 + m + 1)
      = ∑ d ∈ Finset.Ico (t1 + 1 + 1) (t1 + 1 + i + 1), B.spend d := B.sum_shift (t1 + 1) i
  have hsplit : ∑ d ∈ Finset.Ico (t1 + 1) (D + 1), B.spend d
      = B.spend (t1 + 1) + ∑ d ∈ Finset.Ico (t1 + 1 + 1) (D + 1), B.spend d :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  rw [show t1 + 1 + i + 1 = D + 1 from by omega] at hshift
  rw [hshift, ← hi] at hid
  linarith

/-! ### The two-piece growth potential

`growthSpan` linearizes the growth with the single constant `ĝ`, which lower-bounds the
gain throughout the tracking interval `[π̂, π]`.  In between the gain is often much
larger — for the Filecoin Chung-8 curve it is `1.8`–`2.9 × g_π` — and the source condition
`gain_δ(σ) ≥ 2 g_π` already certifies `gain_δ(σ) ≥ 2 ĝ` at the source.  Concavity
propagates that to a whole initial segment `[σ, σ̃]`.

The potential below turns "the gain is at least `2 ĝ` up to `σ̃` and at least `ĝ`
after it" into a level count.  `Φ` is `1/ĝ`-Lipschitz, so one unit of black-pebble
spend costs at most `1/ĝ`, while one level of growth advances it by at least `1`.
This is the level-counting device behind the sharpened growth window, in the form that needs
only concavity of `β_δ` — no derivatives, no exchange argument.

One caveat, load-bearing for the comparison with `growth_window`: the window bound
obtained here is `Φ_{σ̃}(π) + 1 + x/ĝ`, against `a + x/ĝ` for `growth_window` composed with
`growthSpan_le`.  The `+1` is real — `gain_sum_ge` extracts a *free* level at the source
from `gain_δ(σ) ≥ 2 ĝ`, whereas the potential spends that same doubling on the halved
slope of `Φ` below `σ̃`.  The two constants to compare are therefore `Φ_{σ̃}(π) + 1` and
`a`, and `growthPot_pi_succ_lt_asymptoticGrowth` says exactly when the former wins.

The generic helper declarations below call their arbitrary split point `split`; when
the ledger instantiates it with `T.mid`, that point is the development's `σ̃`.

**What consumes this.**  `growthConst = min{a, Φ_{σ̃}(π) + 1}` at the end of this file is
the constant `Chain.h₁` is built from, so the potential feeds the *real-valued* ledger
entry of `zMin` and hence the certified slope and threshold.  The `ℕ`-valued
`growthSpan`/`growthCap` still drive `localSpan` and `h₀`, which are layer counts; those
are the constant-charge entry and are dominated at the Filecoin parameters.
-/

/-- `Φ_{σ̃}(v)`: progress from `σ` to `v`, measured in levels, charging `2 ĝ` per level
below `σ̃` and `ĝ` per level above it. -/
noncomputable def growthPot (S : Setting) (T : Tracking S) (split v : ℝ) : ℝ :=
  (min v split - T.σ) / (2 * T.ghat) + (max v split - split) / T.ghat

theorem growthPot_sigma {split : ℝ} (hσsplit : T.σ ≤ split) :
    growthPot S T split T.σ = 0 := by
  simp only [growthPot, min_eq_left hσsplit, max_eq_right hσsplit]
  simp

/-- `Φ_{σ̃}` is `1/ĝ`-Lipschitz: one unit of black-pebble spend costs at most `1/ĝ`
levels of progress. -/
theorem growthPot_lipschitz {split u v : ℝ} (huv : u ≤ v) :
    growthPot S T split v - growthPot S T split u ≤ (v - u) / T.ghat := by
  have hg := T.ghat_pos
  have hmin : min u split ≤ min v split := min_le_min huv (le_refl split)
  have hmax : max u split ≤ max v split := max_le_max huv (le_refl split)
  have hsplit :
      (min v split - min u split) + (max v split - max u split) = v - u := by
    have h1 : min v split + max v split = v + split := min_add_max v split
    have h2 : min u split + max u split = u + split := min_add_max u split
    linarith
  have hsmall : (min v split - min u split) / (2 * T.ghat)
      ≤ (min v split - min u split) / T.ghat := by
    rw [div_le_div_iff₀ (by positivity) hg]
    nlinarith
  have hexp : growthPot S T split v - growthPot S T split u
      = (min v split - min u split) / (2 * T.ghat)
        + (max v split - max u split) / T.ghat := by
    simp only [growthPot]; ring
  have hgoal : (v - u) / T.ghat
      = (min v split - min u split) / T.ghat
        + (max v split - max u split) / T.ghat := by
    rw [← hsplit]; ring
  rw [hexp, hgoal]
  linarith

/-- One free level of growth advances `Φ_{σ̃}` by at least `1`.  Below `σ̃` this uses the
doubled gain supplied by the source condition and concavity; above `σ̃` the ordinary
tracking gain `ĝ` suffices. -/
theorem growthPot_step {split v : ℝ}
    (hmid : ∀ x, T.σ ≤ x → x ≤ split → 2 * T.ghat ≤ S.gainD x)
    (hv : T.σ ≤ v) (hvπ : v ≤ S.pi) :
    growthPot S T split v + 1 ≤ growthPot S T split (S.betaD v) := by
  have hg := T.ghat_pos
  have hgeq := S.betaD_eq v
  have hgain : T.ghat ≤ S.gainD v := T.ghat_le_gainD ⟨le_trans T.lam_le_σ hv, hvπ⟩
  have hvb : v ≤ S.betaD v := by rw [hgeq]; linarith
  rcases le_total v split with hvsplit | hsplitv
  · have hgv : 2 * T.ghat ≤ S.gainD v := hmid v hv hvsplit
    have hbv : v + 2 * T.ghat ≤ S.betaD v := by rw [hgeq]; linarith
    have h2 : (1 : ℝ) ≤ (S.betaD v - v) / (2 * T.ghat) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rcases le_total (S.betaD v) split with hbetaSplit | hsplitBeta
    · simp only [growthPot, min_eq_left hvsplit, max_eq_right hvsplit,
        min_eq_left hbetaSplit, max_eq_right hbetaSplit]
      have heq : (S.betaD v - T.σ) / (2 * T.ghat) - (v - T.σ) / (2 * T.ghat)
          = (S.betaD v - v) / (2 * T.ghat) := by ring
      simp only [sub_self, zero_div, add_zero]
      linarith
    · simp only [growthPot, min_eq_left hvsplit, max_eq_right hvsplit,
        min_eq_right hsplitBeta, max_eq_left hsplitBeta, sub_self, zero_div, add_zero]
      have h1 : (S.betaD v - split) / (2 * T.ghat)
          ≤ (S.betaD v - split) / T.ghat := by
        rw [div_le_div_iff₀ (by positivity) hg]
        nlinarith
      have heq : (split - T.σ) / (2 * T.ghat)
          + (S.betaD v - split) / (2 * T.ghat)
          - (v - T.σ) / (2 * T.ghat) = (S.betaD v - v) / (2 * T.ghat) := by ring
      linarith
  · have hbv : v + T.ghat ≤ S.betaD v := by rw [hgeq]; linarith
    have hsplitBeta : split ≤ S.betaD v := le_trans hsplitv hvb
    simp only [growthPot, min_eq_right hsplitv, max_eq_left hsplitv,
      min_eq_right hsplitBeta, max_eq_left hsplitBeta]
    have heq : (S.betaD v - split) / T.ghat - (v - split) / T.ghat
        = (S.betaD v - v) / T.ghat := by ring
    have h1 : (1 : ℝ) ≤ (S.betaD v - v) / T.ghat := by
      rw [le_div_iff₀ hg]; linarith
    linarith

theorem growthPot_mono {split u v : ℝ} (huv : u ≤ v) :
    growthPot S T split u ≤ growthPot S T split v := by
  have hg := T.ghat_pos
  have hm := min_le_min huv (le_refl split)
  have hM := max_le_max huv (le_refl split)
  have h1 : (min u split - T.σ) / (2 * T.ghat)
      ≤ (min v split - T.σ) / (2 * T.ghat) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : (max u split - split) / T.ghat ≤ (max v split - split) / T.ghat := by
    rw [div_le_div_iff₀ hg hg]
    nlinarith
  simp only [growthPot]
  linarith

/-- the source condition plus concavity certify the doubled gain on the whole segment
`[σ, σ̃]`, from a single certificate `2 ĝ ≤ gain_δ(σ̃)` at the right endpoint. -/
theorem two_ghat_le_gainD_of_mem {split x : ℝ} (hsplit : 2 * T.ghat ≤ S.gainD split)
    (hsplitmem : split ∈ Icc (0 : ℝ) 1) (hx : T.σ ≤ x) (hxsplit : x ≤ split) :
    2 * T.ghat ≤ S.gainD x := by
  have h := S.gainD_concaveOn.min_le_of_mem_Icc T.σ_mem_Icc hsplitmem ⟨hx, hxsplit⟩
  exact le_trans (le_min T.two_ghat_le_gainD_σ hsplit) h

/-- `mirror-floor lemma`, in the sharper form its own proof establishes: at a
`ĝ`-expandable depth the tracked footprint never falls below the *source weight*
`σ`, not merely below the tracking floor `π̂`. -/
theorem mirror_floor_sigma (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f)
    (hinit : f t = T.σ) {j : ℕ} (hle : ∀ i, i ≤ j → f (t + i) ≤ S.pi) :
    ∀ i, i ≤ j → T.σ ≤ f (t + i) := by
  intro i hij
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [Nat.add_zero, hinit]
  · have hfloor := mirror_floor hexp hbound hinit hle
    have hgain := gain_sum_ge hinit hi (fun m hm => hfloor m (by omega))
      (fun m hm => hle m (by omega))
    have hspend := hexp i hi
    have hid := hbound.sum_le (le_refl t) i
    rw [hinit] at hid
    linarith

/-- The potential telescopes along the footprint bound: each level buys one unit of
progress, each unit of spend costs at most `1/ĝ`. -/
theorem growthPot_bound {split : ℝ} (hσsplit : T.σ ≤ split)
    (hmid : ∀ x, T.σ ≤ x → x ≤ split → 2 * T.ghat ≤ S.gainD x)
    (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f) (hinit : f t = T.σ)
    {m : ℕ} (hle : ∀ i, i ≤ m → f (t + i) ≤ S.pi) :
    ∀ i, i ≤ m →
      (i : ℝ) - (∑ d ∈ Finset.Ico (t + 1) (t + i + 1), B.spend d) / T.ghat
        ≤ growthPot S T split (f (t + i)) := by
  have hg := T.ghat_pos
  intro i
  induction i with
  | zero =>
      intro _
      simp only [Nat.add_zero, hinit, Nat.cast_zero]
      rw [growthPot_sigma hσsplit, show Finset.Ico (t + 1) (t + 1) = ∅ from by simp]
      simp
  | succ i ih =>
      intro him
      have hi := ih (by omega)
      have hfi : T.σ ≤ f (t + i) :=
        mirror_floor_sigma hexp hbound hinit hle i (by omega)
      have hfiπ : f (t + i) ≤ S.pi := hle i (by omega)
      have hstep : S.betaD (f (t + i)) - B.spend (t + i + 1) ≤ f (t + i + 1) := by
        have := hbound.step_ge (Nat.le_add_right t i)
        rw [S.betaD_eq]
        linarith
      have hmono : growthPot S T split (S.betaD (f (t + i)) - B.spend (t + i + 1))
          ≤ growthPot S T split (f (t + i + 1)) := growthPot_mono hstep
      have hlip := growthPot_lipschitz (S := S) (T := T) (split := split)
        (u := S.betaD (f (t + i)) - B.spend (t + i + 1)) (v := S.betaD (f (t + i)))
        (by linarith [B.spend_nonneg (t + i + 1)])
      have hadv := growthPot_step (S := S) (T := T) hmid hfi hfiπ
      have hdiv : (S.betaD (f (t + i)) - (S.betaD (f (t + i)) - B.spend (t + i + 1)))
          / T.ghat = B.spend (t + i + 1) / T.ghat := by ring_nf
      rw [hdiv] at hlip
      rw [show t + (i + 1) = t + i + 1 from by omega,
        Finset.sum_Ico_succ_top (by omega : t + 1 ≤ t + i + 1)]
      push_cast
      rw [add_div]
      linarith

/--
**Growth window with the two-piece potential.**

The same hypotheses as `growth_window` plus the doubled-gain certificate `hmid`, and the
level count `Φ_{σ̃}(π) + 1` in place of `a = max{1, (π - σ)/ĝ}`.

This is *not* automatically smaller: `Φ_{σ̃}(π) ≤ (π - σ)/ĝ` always
(`growthPot_pi_le_div`), but the `+1` has to be paid back, and it is recovered exactly
when the doubled-gain segment exceeds `2 ĝ` — see
`growthPot_pi_succ_lt_asymptoticGrowth`.  At the Filecoin Chung-8 parameters with
`σ̃ = 3/5` the segment is `0.482` against `2 ĝ = 0.223`, and the constant is `4.97`
against `a = 6.12`; the certified gap is `chung8_growthPot_window_gap`.
-/
theorem growthPot_window {split : ℝ} (hσsplit : T.σ ≤ split)
    (hmid : ∀ x, T.σ ≤ x → x ≤ split → 2 * T.ghat ≤ S.gainD x)
    (hexp : Expandable B T.ghat t) (hbound : IsFootprintBound S B t f) (hinit : f t = T.σ)
    {t1 : ℕ} (ht1 : t < t1)
    (hbelow : ∀ d, t ≤ d → d < t1 → f d ≤ S.pi) :
    ((t1 - t : ℕ) : ℝ) ≤
      growthPot S T split S.pi + 1
        + (∑ d ∈ Finset.Ico (t + 1) t1, B.spend d) / T.ghat := by
  obtain ⟨m, rfl⟩ : ∃ m, t1 = t + m + 1 := ⟨t1 - t - 1, by omega⟩
  have hle : ∀ i, i ≤ m → f (t + i) ≤ S.pi := fun i hi =>
    hbelow _ (by omega) (by omega)
  have hkey := growthPot_bound hσsplit hmid hexp hbound hinit hle m (le_refl m)
  have hfm : growthPot S T split (f (t + m)) ≤ growthPot S T split S.pi :=
    growthPot_mono (hle m (le_refl m))
  have hcast : ((t + m + 1 - t : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [show t + m + 1 - t = m + 1 from by omega]; push_cast; ring
  rw [hcast]
  linarith

/-- Closed form of the potential at `π`:
`Φ_{σ̃}(π) = (σ̃-σ)/(2ĝ) + (π-σ̃)/ĝ`. -/
theorem growthPot_pi {split : ℝ} (hsplitπ : split ≤ S.pi) :
    growthPot S T split S.pi =
      (split - T.σ) / (2 * T.ghat) + (S.pi - split) / T.ghat := by
  simp only [growthPot, min_eq_right hsplitπ, max_eq_left hsplitπ]

/-- The exact saving of the two-piece potential over the single-constant count: the
doubled-gain segment `[σ, σ̃]` is charged at half price, and nothing else changes. -/
theorem growthPot_pi_add_gap {split : ℝ} (hsplitπ : split ≤ S.pi) :
    growthPot S T split S.pi + (split - T.σ) / (2 * T.ghat)
      = (S.pi - T.σ) / T.ghat := by
  have hg := T.ghat_pos
  rw [growthPot_pi hsplitπ]
  field_simp
  ring

/-- The two-piece potential is never worse than the single-constant count `(π-σ)/ĝ`.

Note the right-hand side is the *quotient*, not `asymptoticGrowth S T = max{1, ·}`; see
`growthPot_pi_le_asymptoticGrowth` for the comparison against the constant that
`growth_window` actually uses. -/
theorem growthPot_pi_le_div {split : ℝ} (hσsplit : T.σ ≤ split)
    (hsplitπ : split ≤ S.pi) :
    growthPot S T split S.pi ≤ (S.pi - T.σ) / T.ghat := by
  have hg := T.ghat_pos
  have hgap : 0 ≤ (split - T.σ) / (2 * T.ghat) := by
    apply div_nonneg (by linarith) (by positivity)
  linarith [growthPot_pi_add_gap (S := S) (T := T) hsplitπ]

/-- …and strictly better as soon as `σ < σ̃`. -/
theorem growthPot_pi_lt_div {split : ℝ} (hσsplit : T.σ < split)
    (hsplitπ : split ≤ S.pi) :
    growthPot S T split S.pi < (S.pi - T.σ) / T.ghat := by
  have hg := T.ghat_pos
  have hgap : 0 < (split - T.σ) / (2 * T.ghat) := by
    apply div_pos (by linarith) (by positivity)
  linarith [growthPot_pi_add_gap (S := S) (T := T) hsplitπ]

theorem growthPot_pi_le_asymptoticGrowth {split : ℝ}
    (hσsplit : T.σ ≤ split) (hsplitπ : split ≤ S.pi) :
    growthPot S T split S.pi ≤ asymptoticGrowth S T :=
  (growthPot_pi_le_div hσsplit hsplitπ).trans (le_max_right _ _)

/--
**When the two-piece window actually beats the linear one.**

`growthPot_window` certifies `Φ_{σ̃}(π) + 1 + x/ĝ` levels and `growth_window` certifies
`a + x/ĝ`, so the comparison is between `Φ_{σ̃}(π) + 1` and `a`.  The saving of the
potential is `(σ̃ - σ)/(2 ĝ)` levels (`growthPot_pi_add_gap`) and its cost is the one
free level that `gain_sum_ge` extracts at the source, so the potential wins exactly when
the doubled-gain segment is longer than `2 ĝ`.

`hgap` also rules out the `max{1, ·}` in `asymptoticGrowth` being active: it forces
`π - σ ≥ σ̃ - σ > 2 ĝ`, hence `(π - σ)/ĝ > 2`.
-/
theorem growthPot_pi_succ_lt_asymptoticGrowth {split : ℝ} (hsplitπ : split ≤ S.pi)
    (hgap : 2 * T.ghat < split - T.σ) :
    growthPot S T split S.pi + 1 < asymptoticGrowth S T := by
  have hg := T.ghat_pos
  have hstrict : 1 < (split - T.σ) / (2 * T.ghat) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hlin : 1 ≤ (S.pi - T.σ) / T.ghat := by
    rw [le_div_iff₀ hg]; linarith
  have hmax : asymptoticGrowth S T = (S.pi - T.σ) / T.ghat :=
    max_eq_right hlin
  rw [hmax]
  linarith [growthPot_pi_add_gap (S := S) (T := T) hsplitπ]

/-! ### The growth constant the ledger charges

`growthConst` is the better of the two window constants at the *tracking mid-point*
`T.mid`, which every `Tracking` carries.  With `mid = σ` the potential entry degenerates
to `(π - σ)/ĝ + 1`, one worse than `asymptoticGrowth`, and the `min` picks the old
constant; with a genuine mid-point it picks the potential.  Either way
`growthConst_window` charges an attempt's growth phase at `growthConst + x/ĝ` levels,
which is what `Chain.h₁` is built from.
-/

/-- the source condition plus concavity certify the doubled gain on the whole segment
`[σ, mid]`, from the single mid-point certificate `Tracking.mid_gain`. -/
theorem two_ghat_le_gainD_of_le_mid {x : ℝ} (hx : T.σ ≤ x) (hxmid : x ≤ T.mid) :
    2 * T.ghat ≤ S.gainD x :=
  two_ghat_le_gainD_of_mem T.two_ghat_le_gainD_mid T.mid_mem_Icc hx hxmid

/-- **The growth constant of `optimized span bound`**, `min{a, Φ_{σ̃}(π) + 1}`: the better
of the single-constant count `a = max{1, (π-σ)/ĝ}` and the two-piece potential count. -/
noncomputable def growthConst (S : Setting) (T : Tracking S) : ℝ :=
  min (asymptoticGrowth S T) (growthPot S T T.mid S.pi + 1)

theorem growthPot_mid_pi_nonneg : 0 ≤ growthPot S T T.mid S.pi := by
  have hg := T.ghat_pos
  rw [growthPot_pi T.mid_le]
  have h1 : 0 ≤ (T.mid - T.σ) / (2 * T.ghat) :=
    div_nonneg (by linarith [T.mid_ge]) (by positivity)
  have h2 : 0 ≤ (S.pi - T.mid) / T.ghat :=
    div_nonneg (by linarith [T.mid_le]) hg.le
  linarith

theorem one_le_growthConst : 1 ≤ growthConst S T :=
  le_min one_le_asymptoticGrowth (by linarith [growthPot_mid_pi_nonneg (S := S) (T := T)])

theorem growthConst_le_asymptoticGrowth : growthConst S T ≤ asymptoticGrowth S T :=
  min_le_left _ _

/--
**`growth-window lemma` at the growth constant.**  Both window bounds hold, so their
minimum does: an attempt's growth phase spans at most `growthConst + x/ĝ` levels, where
`x` is the spend strictly inside the window.
-/
theorem growthConst_window (hexp : Expandable B T.ghat t)
    (hbound : IsFootprintBound S B t f) (hinit : f t = T.σ)
    {t1 : ℕ} (ht1 : t < t1)
    (hbelow : ∀ d, t ≤ d → d < t1 → f d ≤ S.pi) :
    ((t1 - t : ℕ) : ℝ) ≤
      growthConst S T + (∑ d ∈ Finset.Ico (t + 1) t1, B.spend d) / T.ghat := by
  have hx : (0 : ℝ) ≤ ∑ d ∈ Finset.Ico (t + 1) t1, B.spend d :=
    Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hlin : ((t1 - t : ℕ) : ℝ)
      ≤ asymptoticGrowth S T + (∑ d ∈ Finset.Ico (t + 1) t1, B.spend d) / T.ghat := by
    refine le_trans ?_ (growthSpan_le (S := S) (T := T) hx)
    exact_mod_cast growth_window hexp hbound hinit ht1 hbelow
  have hpot := growthPot_window (split := T.mid) T.mid_ge
    (fun x hx hxmid => two_ghat_le_gainD_of_le_mid hx hxmid) hexp hbound hinit ht1 hbelow
  simp only [growthConst]
  rcases le_total (asymptoticGrowth S T) (growthPot S T T.mid S.pi + 1) with h | h
  · rw [min_eq_left h]; exact hlin
  · rw [min_eq_right h]; exact hpot

end ProofOfSpace

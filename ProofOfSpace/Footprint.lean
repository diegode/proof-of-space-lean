/-
# Footprint bounds: the footprint identity, the gain floor, and the infertile budget

This file formalizes the footprint recurrence and challenge bounds of
this development.

**The one convention that differs from the development.**  The Lean field `depth` is an index
counted from the challenge, while the development counts levels the other way, following
Reyzin.  Lean depth `d` is Reyzin's **level** `ℓ - d`, so Lean `layer 0` is the
published construction's bottom layer `V_ℓ` (which carries the targets) and Lean
`layer (ℓ-1)` is its top layer `V_1`.  Inter-layer edges run from Lean `layer (d+1)` to `layer d`,
which is the development's `V_{j-1}` to `V_j`.  Every direction word therefore flips: the
published recurrence runs upward in `j`, this one runs forward in `d`.  Counting forward
is what keeps the recurrence free of truncated `ℕ` subtraction.

Consequently the field named `depth` is a level index in the development's sense — the development
reserves *depth* for the length of a path, and `NodeDepthRobust` and its relatives do
use `depth` in that path-length sense.

Because depths count forward from the challenge, the development's upward recurrence
`footprint recurrence` becomes the forward recurrence
`f (d+1) = max (0) (β_δ (f d) - spend (d+1))`.

Results proved here:

* `IsFootprintBound.sum_le` — the accumulated form of `footprint recurrence`, in the
  inequality form in which it is always used.  Because `max 0 v ≥ v`, no positivity side
  condition is needed.  The development does not restate it, citing it throughout
  this development as the accumulated bound of Reyzin, Claim 3.
* `ChallengeBound.floor` — `challenge-floor lemma`: under the entry condition
  `ζδ - ρ > π̄` the challenge footprint never drops below `π̄` and never rises above
  `αmax`; in particular every gain along the footprint bound is nonnegative, and every
  *infertile* gain is at least `g_π`.  This is where `challenge-floor lemma` is absorbed:
  the two invariants are proved by a single simultaneous induction, which avoids the
  circularity of quoting positivity of the gain sum before the floor is known.
* `ChallengeBound.infertile_budget` — `infertile-capacity lemma`.
* `ChallengeBound.infertile_card_le` — the resulting capacity bound
  `k ≤ infertileCap h`, the first summand of `s` in `search-cap definition`.
-/
import ProofOfSpace.Expansion
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring

namespace ProofOfSpace

open Real Set Finset

/-- A black-pebble allocation: `spend d` is the weight `ρ_d` of black pebbles placed at
level `d`.  The prefix bound `total` is `pebbling-budget condition`; the adversary's total budget is
`ρ`. -/
structure Budget (S : Setting) where
  /-- Weight of black pebbles at depth `d`. -/
  spend : ℕ → ℝ
  spend_nonneg : ∀ d, 0 ≤ spend d
  total : ∀ m, ∑ d ∈ Finset.range m, spend d ≤ S.ρ

namespace Budget

variable {S : Setting} (B : Budget S)


/-- Shifted sums are sums over an interval. -/
theorem sum_shift (t i : ℕ) :
    ∑ m ∈ Finset.range i, B.spend (t + m + 1)
      = ∑ d ∈ Finset.Ico (t + 1) (t + i + 1), B.spend d := by
  rw [Finset.sum_Ico_eq_sum_range]
  have : t + i + 1 - (t + 1) = i := by omega
  rw [this]
  exact Finset.sum_congr rfl fun m _ => by ring_nf

/-- The prefix sums are monotone. -/
theorem sum_range_mono {a b : ℕ} (hab : a ≤ b) :
    ∑ d ∈ Finset.range a, B.spend d ≤ ∑ d ∈ Finset.range b, B.spend d := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
  intro d hd
  simp only [Finset.mem_range] at hd ⊢
  omega

/-- Any window of the spend is bounded by the total budget. -/
theorem sum_Ico_le (a m : ℕ) : ∑ d ∈ Finset.Ico a m, B.spend d ≤ S.ρ := by
  refine le_trans ?_ (B.total m)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
  intro d hd
  simp only [Finset.mem_Ico] at hd
  simp only [Finset.mem_range]
  omega

end Budget

/-- `IsFootprintBound S B start f` says that from depth `start` downwards, `f` follows Reyzin's
footprint recurrence. -/
def IsFootprintBound (S : Setting) (B : Budget S) (start : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ d, start ≤ d → f (d + 1) = max 0 (S.betaD (f d) - B.spend (d + 1))

namespace IsFootprintBound

variable {S : Setting} {B : Budget S} {start : ℕ} {f : ℕ → ℝ}

theorem nonneg (h : IsFootprintBound S B start f) {d : ℕ} (hd : start < d) : 0 ≤ f d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [h e (by omega)]
  exact le_max_left _ _

/-- One step of the recurrence, in the inequality form. -/
theorem step_ge (h : IsFootprintBound S B start f) {d : ℕ} (hd : start ≤ d) :
    f d + S.gainD (f d) - B.spend (d + 1) ≤ f (d + 1) := by
  rw [h d hd, Setting.betaD_eq]
  exact le_max_right _ _

/--
**The accumulated bound** — Reyzin, Claim 3, as this development cites it —
in the inequality form used throughout: the footprint at depth `t + i` is at least the
starting weight plus the accumulated gains minus the accumulated spend. Truncation at `0` can
only help, so
unlike the equality version this needs no positivity hypothesis.
-/
theorem sum_le (h : IsFootprintBound S B start f) {t : ℕ} (ht : start ≤ t) (i : ℕ) :
    f t + (∑ m ∈ Finset.range i, S.gainD (f (t + m)))
        - (∑ m ∈ Finset.range i, B.spend (t + m + 1)) ≤ f (t + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hstep : f (t + i) + S.gainD (f (t + i)) - B.spend (t + i + 1) ≤ f (t + i + 1) :=
        h.step_ge (le_trans ht (Nat.le_add_right t i))
      have hsucc : t + (i + 1) = t + i + 1 := by omega
      rw [hsucc, Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/--
**The general floor invariant.**  If the footprint bound starts at depth `start` no lower
than
`c` minus the spend already charged on `[a, start]`, and `c` stays above `αmin` even after
the *whole* budget is spent, then it stays above `c` minus the accumulated
spend, and never rises above `αmax`.

This is the common core of `challenge-floor lemma` and of the post-fertile floor
`Growth.post_floor`, both in this development: the two invariants are needed
simultaneously, because the gain used
in the descent step is only known to be nonnegative once the footprint is enclosed in
`[αmin, αmax]`.
-/
theorem floor {a : ℕ} {c : ℝ} (h : IsFootprintBound S B start f) (ha : a ≤ start)
    (hc : S.αmin + S.ρ < c) (hmax : f start ≤ S.αmax)
    (hbase : c - ∑ d ∈ Finset.Ico a (start + 1), B.spend d ≤ f start) :
    ∀ d, start ≤ d → c - (∑ e ∈ Finset.Ico a (d + 1), B.spend e) ≤ f d ∧ f d ≤ S.αmax := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact ⟨hbase, hmax⟩
  | succ d hd ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hbound : ∑ e ∈ Finset.Ico a (d + 1), B.spend e ≤ S.ρ := B.sum_Ico_le a (d + 1)
      have hlow : S.αmin < f d := by linarith
      have hf0 : 0 ≤ f d := le_trans S.αmin_nonneg hlow.le
      have hgain : 0 ≤ S.gainD (f d) := S.gainD_nonneg ⟨hlow.le, ih2⟩
      have hsplit : ∑ e ∈ Finset.Ico a (d + 1 + 1), B.spend e
          = (∑ e ∈ Finset.Ico a (d + 1), B.spend e) + B.spend (d + 1) :=
        Finset.sum_Ico_succ_top (by omega) _
      constructor
      · have hstep := h.step_ge hd
        rw [hsplit]
        linarith
      · have hmemIcc : f d ∈ Icc (0:ℝ) 1 := ⟨hf0, le_trans ih2 S.αmax_le_one⟩
        have hmono : S.betaD (f d) ≤ S.αmax := by
          rcases lt_or_eq_of_le ih2 with hlt | heq
          · have := S.betaD_strictMonoOn hmemIcc S.αmax_mem_Icc hlt
            rw [S.betaD_αmax] at this; exact this.le
          · rw [heq, S.betaD_αmax]
        rw [h d hd]
        refine max_le ?_ ?_
        · exact le_trans S.αg_mem.1.le S.αmax_mem.1
        · have := B.spend_nonneg (d + 1); linarith

/--
**The general infertile-budget bound.**  If `K` of the depths in `[start, P)` are infertile
and every infertile gain is at least `g` (while every gain is nonnegative), then the black
pebbles strictly below `start` and above `P` weigh more than
`f start - π + (K - 1) g`.

This is the scalar form of `infertile-capacity lemma` in this development; it is used
both for the challenge footprint (base case) and for a tracked source footprint
(`fertile-continuation lemma`).
-/
theorem infertile_budget {g : ℝ} {P : ℕ} (h : IsFootprintBound S B start f)
    (hnn : ∀ d, start ≤ d → d < P → 0 ≤ S.gainD (f d))
    (hinf : ∀ d, start ≤ d → d < P → f d < S.pi → g ≤ S.gainD (f d))
    (hg : 0 ≤ g) {K : ℕ} (hKpos : 0 < K)
    (hK : K ≤ ((Finset.Ico start P).filter (fun d => f d < S.pi)).card) :
    f start - S.pi + ((K : ℝ) - 1) * g < ∑ d ∈ Finset.Ico (start + 1) P, B.spend d := by
  classical
  set T := (Finset.Ico start P).filter (fun d => f d < S.pi) with hT
  have hTne : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hKpos hK)
  set D := T.max' hTne with hD
  have hDT : D ∈ T := T.max'_mem hTne
  have hDmem := Finset.mem_Ico.mp (Finset.mem_filter.mp hDT).1
  have hDinf : f D < S.pi := (Finset.mem_filter.mp hDT).2
  -- the other `K - 1` infertile depths lie strictly above `D`
  set U := (Finset.Ico start D).filter (fun d => f d < S.pi) with hU
  have hsub : T.erase D ⊆ U := by
    intro d hd
    have hdT : d ∈ T := Finset.mem_of_mem_erase hd
    have hne : d ≠ D := Finset.ne_of_mem_erase hd
    have hle : d ≤ D := T.le_max' d hdT
    have hstart := (Finset.mem_Ico.mp (Finset.mem_filter.mp hdT).1).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hstart, by omega⟩, (Finset.mem_filter.mp hdT).2⟩
  have hUcard : K - 1 ≤ U.card := by
    have h1 : (T.erase D).card = T.card - 1 := Finset.card_erase_of_mem hDT
    have h2 := Finset.card_le_card hsub
    omega
  have hUcard' : ((K : ℝ) - 1) ≤ (U.card : ℝ) := by
    have hk1 : (1:ℕ) ≤ K := hKpos
    have : (K : ℝ) - 1 ≤ ((K - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hk1]; linarith
    exact this.trans (by exact_mod_cast hUcard)
  -- the accumulated gain above `D` is at least `(K-1) g`
  have hgains : ((K : ℝ) - 1) * g ≤ ∑ j ∈ Finset.Ico start D, S.gainD (f j) := by
    have hstep1 : ∑ j ∈ U, S.gainD (f j) ≤ ∑ j ∈ Finset.Ico start D, S.gainD (f j) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro j hj _
      exact hnn j (Finset.mem_Ico.mp hj).1
        (lt_trans (Finset.mem_Ico.mp hj).2 hDmem.2)
    have hstep2 : (U.card : ℝ) * g ≤ ∑ j ∈ U, S.gainD (f j) := by
      have hb : ∀ j ∈ U, g ≤ S.gainD (f j) := by
        intro j hj
        have h1 := Finset.mem_filter.mp hj
        exact hinf j (Finset.mem_Ico.mp h1.1).1
          (lt_trans (Finset.mem_Ico.mp h1.1).2 hDmem.2) h1.2
      have := Finset.card_nsmul_le_sum U (fun j => S.gainD (f j)) g hb
      simpa [nsmul_eq_mul] using this
    calc ((K : ℝ) - 1) * g ≤ (U.card : ℝ) * g := mul_le_mul_of_nonneg_right hUcard' hg
      _ ≤ ∑ j ∈ U, S.gainD (f j) := hstep2
      _ ≤ ∑ j ∈ Finset.Ico start D, S.gainD (f j) := hstep1
  -- the footprint identity at the deepest infertile depth
  obtain ⟨i, hi⟩ : ∃ i, D = start + i := ⟨D - start, by omega⟩
  have hid := h.sum_le (le_refl start) i
  rw [← hi] at hid
  have hgainsum : ∑ m ∈ Finset.range i, S.gainD (f (start + m))
      = ∑ j ∈ Finset.Ico start D, S.gainD (f j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have : D - start = i := by omega
    rw [this]
  have hspend : ∑ m ∈ Finset.range i, B.spend (start + m + 1)
      ≤ ∑ d ∈ Finset.Ico (start + 1) P, B.spend d := by
    rw [B.sum_shift start i]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
    intro d hd
    simp only [Finset.mem_Ico] at hd ⊢
    omega
  rw [hgainsum] at hid
  linarith

/-- The footprint never grows past `αmax`, where the gain vanishes. -/
theorem le_αmax (h : IsFootprintBound S B start f) (h0 : 0 ≤ f start) (hmax : f start ≤ S.αmax) :
    ∀ d, start ≤ d → 0 ≤ f d ∧ f d ≤ S.αmax := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact ⟨h0, hmax⟩
  | succ d hd ih =>
      obtain ⟨ih0, ih2⟩ := ih
      have hmemIcc : f d ∈ Icc (0:ℝ) 1 := ⟨ih0, le_trans ih2 S.αmax_le_one⟩
      have hmono : S.betaD (f d) ≤ S.αmax := by
        rcases lt_or_eq_of_le ih2 with hlt | heq
        · have := S.betaD_strictMonoOn hmemIcc S.αmax_mem_Icc hlt
          rw [S.betaD_αmax] at this; exact this.le
        · rw [heq, S.betaD_αmax]
      rw [h d hd]
      refine ⟨le_max_left _ _, max_le ?_ ?_⟩
      · exact le_trans S.αg_mem.1.le S.αmax_mem.1
      · have := B.spend_nonneg (d + 1); linarith

end IsFootprintBound

/-! ### The challenge footprint bound -/

/-- The footprint bound of the challenge set, of adjusted weight `ζδ`. -/
structure ChallengeBound (S : Setting) (B : Budget S) where
  /-- Footprint weight at depth `d`. -/
  f : ℕ → ℝ
  bound : IsFootprintBound S B 0 f
  /-- `f_ℓ ≥ ζ_δ - ρ_ℓ`. -/
  init_ge : S.ζδ - B.spend 0 ≤ f 0
  /-- The footprint of the challenge set cannot exceed its weight. -/
  init_le : f 0 ≤ S.ζδ

namespace ChallengeBound

variable {S : Setting} {B : Budget S} (C : ChallengeBound S B)

/-- The two invariants of `challenge-floor lemma`, proved by simultaneous induction.

The hypothesis is the *general* entry condition `α_δ^min < zetaFloor = ζ_δ - ρ` of
`challenge-floor lemma`, not the stronger `π̄ < ζ_δ - ρ` of `no-break parameter conditions`: the
induction only ever needs the floor to keep the footprint inside the active interval
`[α_δ^min, α_δ^max]`, where the gain is nonnegative.  `invariants` below is the
specialization used by the uniform-regime results. -/
theorem invariants_gen (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.ζδ - S.ρ) (d : ℕ) :
    S.ζδ - (∑ m ∈ Finset.range (d + 1), B.spend m) ≤ C.f d ∧ C.f d ≤ S.αmax := by
  induction d with
  | zero =>
      constructor
      · simpa using C.init_ge
      · exact le_trans C.init_le hζmax
  | succ d ih =>
      obtain ⟨ih1, ih2⟩ := ih
      -- The floor forces the current footprint into the active interval.
      have hlow : S.αmin < C.f d := by
        have hb := B.total (d + 1)
        linarith
      have hgain : 0 ≤ S.gainD (C.f d) := S.gainD_nonneg ⟨hlow.le, ih2⟩
      constructor
      · have hstep := C.bound.step_ge (d := d) (Nat.zero_le d)
        rw [Finset.sum_range_succ]
        linarith
      · -- The footprint cannot grow past `αmax`, where the gain vanishes.
        have hf0 : 0 ≤ C.f d := by
          have := S.αmin_nonneg
          linarith
        have hmemIcc : C.f d ∈ Icc (0:ℝ) 1 := ⟨hf0, le_trans ih2 S.αmax_le_one⟩
        have hmono : S.betaD (C.f d) ≤ S.αmax := by
          rcases lt_or_eq_of_le ih2 with hlt | heq
          · have := S.betaD_strictMonoOn hmemIcc S.αmax_mem_Icc hlt
            rw [S.betaD_αmax] at this; exact this.le
          · rw [heq, S.betaD_αmax]
        rw [C.bound d (Nat.zero_le d)]
        refine max_le ?_ ?_
        · exact le_trans S.αg_mem.1.le S.αmax_mem.1
        · have := B.spend_nonneg (d + 1); linarith

/-- The two invariants of `challenge-floor lemma` under the entry condition
`no-break parameter conditions`, which is stronger than the hypothesis of `invariants_gen`
because `α_δ^min < π̄`. -/
theorem invariants (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ) (d : ℕ) :
    S.ζδ - (∑ m ∈ Finset.range (d + 1), B.spend m) ≤ C.f d ∧ C.f d ≤ S.αmax :=
  C.invariants_gen hζmax (lt_trans S.αmin_lt_piBar hentry) d

/-- **`challenge-floor lemma`, lower half.** Under the entry condition the challenge footprint
never falls below `π̄`. -/
theorem piBar_lt (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ) (d : ℕ) :
    S.piBar < C.f d := by
  have h := (C.invariants hζmax hentry d).1
  have hb := B.total (d + 1)
  linarith

/-- **`challenge-floor lemma`, upper half.** -/
theorem le_αmax (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ) (d : ℕ) :
    C.f d ≤ S.αmax := (C.invariants hζmax hentry d).2

/-- Every gain along the challenge footprint bound is nonnegative. -/
theorem gainD_nonneg (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ) (d : ℕ) :
    0 ≤ S.gainD (C.f d) := by
  have h1 := C.piBar_lt hζmax hentry d
  have h2 := C.le_αmax hζmax hentry d
  exact S.gainD_nonneg ⟨le_of_lt (lt_of_le_of_lt S.αmin_lt_piBar.le h1), h2⟩

/-- Every *infertile* gain along the challenge footprint bound is at least `g_π`. -/
theorem gpi_le_gainD_of_infertile (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    {d : ℕ} (hd : C.f d < S.pi) : S.gpi ≤ S.gainD (C.f d) :=
  S.gpi_le_gainD ⟨(C.piBar_lt hζmax hentry d).le, hd.le⟩

end ChallengeBound

/-! ### The infertile budget bound -/

/-- `⌈(π - ζ_δ + ρ)/h⌉_+`, the infertile capacity of `infertile-capacity lemma` and the
first summand of `s` in `search-cap definition`. -/
noncomputable def infertileCap (S : Setting) (h : ℝ) : ℕ := Nat.ceil ((S.ρ - (S.ζδ - S.pi)) / h)

/-- `⌈ρ/g⌉ - 1`, the blocked-window capacity of `first-source lemma` and the second
summand of `s` in `search-cap definition`. -/
noncomputable def blockedCap (S : Setting) (g : ℝ) : ℕ := Nat.ceil (S.ρ / g) - 1

/-- **`s` of `search-cap definition`**, as a function of the two gains it is evaluated at:
`s(g,h) = infertileCap(h) + blockedCap(g)`.  `Ledger.sCap` is the instance the theorem
uses, at `g = ĝ` and `h = g̃`. -/
noncomputable def sCapOf (S : Setting) (g h : ℝ) : ℕ := infertileCap S h + blockedCap S g

namespace ChallengeBound

variable {S : Setting} {B : Budget S} (C : ChallengeBound S B)

/--
**`infertile-capacity lemma`.** If at least `k > 0` of the depths `0, …, m` are infertile,
then the black pebbles placed on those depths weigh more than `ζδ - π + (k-1) g_π`.
-/
theorem infertile_budget (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    (m k : ℕ) (hk : 0 < k)
    (hcard : k ≤ ((Finset.range (m + 1)).filter (fun d => C.f d < S.pi)).card) :
    S.ζδ - S.pi + ((k : ℝ) - 1) * S.gpi < ∑ d ∈ Finset.range (m + 1), B.spend d := by
  classical
  set T := (Finset.range (m + 1)).filter (fun d => C.f d < S.pi) with hT
  have hTne : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk hcard)
  set D := T.max' hTne with hD
  have hDT : D ∈ T := T.max'_mem hTne
  have hDinf : C.f D < S.pi := (Finset.mem_filter.mp hDT).2
  have hDm : D ≤ m := by
    have := (Finset.mem_range.mp (Finset.mem_filter.mp hDT).1); omega
  -- The gains strictly above `D` account for at least `k-1` infertile levels.
  set U := (Finset.range D).filter (fun d => C.f d < S.pi) with hU
  have hsub : T.erase D ⊆ U := by
    intro d hd
    have hdT : d ∈ T := Finset.mem_of_mem_erase hd
    have hne : d ≠ D := Finset.ne_of_mem_erase hd
    have hle : d ≤ D := T.le_max' d hdT
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (Finset.mem_filter.mp hdT).2⟩
  have hUcard : k - 1 ≤ U.card := by
    have h1 : (T.erase D).card = T.card - 1 := Finset.card_erase_of_mem hDT
    have h2 := Finset.card_le_card hsub
    omega
  have hUcard' : ((k : ℝ) - 1) ≤ (U.card : ℝ) := by
    have : (k : ℝ) - 1 ≤ ((k - 1 : ℕ) : ℝ) := by
      have : (1:ℕ) ≤ k := hk
      push_cast [Nat.cast_sub this]
      linarith
    exact this.trans (by exact_mod_cast hUcard)
  -- Sum of gains over `range D` is at least `(k-1) g_π`.
  have hgains : ((k : ℝ) - 1) * S.gpi ≤ ∑ j ∈ Finset.range D, S.gainD (C.f j) := by
    have hUsub : U ⊆ Finset.range D := Finset.filter_subset _ _
    have hstep1 : ∑ j ∈ U, S.gainD (C.f j) ≤ ∑ j ∈ Finset.range D, S.gainD (C.f j) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hUsub ?_
      intro j _ _
      exact C.gainD_nonneg hζmax hentry j
    have hstep2 : (U.card : ℝ) * S.gpi ≤ ∑ j ∈ U, S.gainD (C.f j) := by
      have hb : ∀ j ∈ U, S.gpi ≤ S.gainD (C.f j) := by
        intro j hj
        exact C.gpi_le_gainD_of_infertile hζmax hentry (Finset.mem_filter.mp hj).2
      have := Finset.card_nsmul_le_sum U (fun j => S.gainD (C.f j)) S.gpi hb
      simpa [nsmul_eq_mul] using this
    have hgpi : 0 ≤ S.gpi := S.gpi_pos.le
    calc ((k : ℝ) - 1) * S.gpi ≤ (U.card : ℝ) * S.gpi :=
          mul_le_mul_of_nonneg_right hUcard' hgpi
      _ ≤ ∑ j ∈ U, S.gainD (C.f j) := hstep2
      _ ≤ ∑ j ∈ Finset.range D, S.gainD (C.f j) := hstep1
  -- Reyzin's identity at the deepest infertile level.
  have hid := C.bound.sum_le (t := 0) (le_refl 0) D
  simp only [Nat.zero_add] at hid
  have hspend : B.spend 0 + ∑ j ∈ Finset.range D, B.spend (j + 1)
      = ∑ d ∈ Finset.range (D + 1), B.spend d := by
    rw [Finset.sum_range_succ']
    ring
  have hmono : ∑ d ∈ Finset.range (D + 1), B.spend d ≤ ∑ d ∈ Finset.range (m + 1), B.spend d :=
    B.sum_range_mono (by omega)
  have hinit := C.init_ge
  linarith

/-- The number of infertile depths in a prefix is at most `infertileCap(h)`, for any certified
infertile-gain floor `0 < h ≤ g_π`. -/
theorem infertile_card_le (hζmax : S.ζδ ≤ S.αmax) (hentry : S.piBar < S.ζδ - S.ρ)
    {h : ℝ} (hh_pos : 0 < h) (hh_le : h ≤ S.gpi) (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun d => C.f d < S.pi)).card ≤ infertileCap S h := by
  classical
  set k := ((Finset.range (m + 1)).filter (fun d => C.f d < S.pi)).card with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · simp [h0]
  have hbudget := C.infertile_budget hζmax hentry m k hpos (le_refl k)
  have htotal := B.total (m + 1)
  have hkey : ((k : ℝ) - 1) * h < S.ρ - (S.ζδ - S.pi) := by
    have h1 : ((k : ℝ) - 1) * h ≤ ((k : ℝ) - 1) * S.gpi := by
      have hk1 : (0:ℝ) ≤ (k : ℝ) - 1 := by
        have : (1:ℕ) ≤ k := hpos
        have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast this
        linarith
      exact mul_le_mul_of_nonneg_left hh_le hk1
    linarith
  have hdiv : ((k : ℝ) - 1) < (S.ρ - (S.ζδ - S.pi)) / h := by
    rw [lt_div_iff₀ hh_pos]; exact hkey
  have hceil : ((k : ℝ) - 1) < (infertileCap S h : ℝ) :=
    lt_of_lt_of_le hdiv (Nat.le_ceil _)
  have : (k : ℝ) < (infertileCap S h : ℝ) + 1 := by linarith
  have : k < infertileCap S h + 1 := by exact_mod_cast this
  omega


/-! ### `challenge-floor lemma`: the general positive floor

Outside the entry condition `π̄ < ζ_δ - ρ` the challenge footprint may sink below `π̄`,
and infertile levels can no longer be charged at rate `g_π`.  What survives is the
coarser floor `zetaFloor = ζ_δ - ρ`, which the whole budget cannot breach, together with the
rate `g̃ = min{gain_δ(ζ_δ - ρ), g_π}` certified on `[ζ_δ - ρ, π]` by concavity.  The three
results below are the three assertions of `challenge-floor lemma`. -/

/-- **`challenge-floor lemma`, the floor.**  The challenge footprint never falls
below `zetaFloor = ζ_δ - ρ`, however the adversary allocates its budget. -/
theorem zetaFloor_le (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor) (d : ℕ) :
    S.zetaFloor ≤ C.f d := by
  have h := (C.invariants_gen hζmax hentry d).1
  have hb := B.total (d + 1)
  simp only [Setting.zetaFloor] at hentry ⊢
  linarith

/-- Every gain along the challenge footprint bound is nonnegative in the general regime. -/
theorem gainD_nonneg_gen (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor) (d : ℕ) :
    0 ≤ S.gainD (C.f d) :=
  S.gainD_nonneg ⟨le_trans hentry.le (C.zetaFloor_le hζmax hentry d),
    (C.invariants_gen hζmax hentry d).2⟩

/-- **`challenge-floor lemma`, the rate.**  Every *infertile* gain along the
challenge footprint bound is at least `g̃`. -/
theorem gtilde_le_gainD_of_infertile (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor)
    (hlt : S.zetaFloor < S.αmax) {d : ℕ} (hd : C.f d < S.pi) :
    S.gtilde ≤ S.gainD (C.f d) :=
  S.gtilde_le_gainD hentry hlt ⟨C.zetaFloor_le hζmax hentry d, hd.le⟩

/-- **`challenge-floor lemma`, the capacity.**  At most `infertileCap(g̃)` depths of any
prefix are infertile for the challenge footprint. Since
`ρ - (ζ_δ - π) = π - ζ_δ + ρ`, this is exactly
`⌈(π - ζ_δ + ρ)/g̃⌉`. -/
theorem infertile_card_le_gen (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor)
    (hlt : S.zetaFloor < S.αmax) (P : ℕ) :
    ((Finset.Ico 0 P).filter (fun d => C.f d < S.pi)).card ≤ infertileCap S S.gtilde := by
  classical
  set k := ((Finset.Ico 0 P).filter (fun d => C.f d < S.pi)).card with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · simp [h0]
  have hgz : 0 < S.gtilde := S.gtilde_pos hentry hlt
  have hPpos : 0 < P := by
    rcases Nat.eq_zero_or_pos P with hP | hP
    · exfalso; rw [hP] at hk; simp at hk; omega
    · exact hP
  have hbudget := C.bound.infertile_budget (P := P)
    (fun d _ _ => C.gainD_nonneg_gen hζmax hentry d)
    (fun d _ _ hd => C.gtilde_le_gainD_of_infertile hζmax hentry hlt hd)
    hgz.le hpos (le_of_eq hk)
  have hsplit : B.spend 0 + ∑ d ∈ Finset.Ico 1 P, B.spend d ≤ S.ρ := by
    have htot := B.total P
    rwa [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hPpos] at htot
  have hinit := C.init_ge
  simp only [Nat.zero_add] at hbudget
  have hkey : ((k : ℝ) - 1) * S.gtilde < S.ρ - (S.ζδ - S.pi) := by linarith
  have hdiv : ((k : ℝ) - 1) < (S.ρ - (S.ζδ - S.pi)) / S.gtilde := by
    rw [lt_div_iff₀ hgz]; exact hkey
  have hceil : ((k : ℝ) - 1) < (infertileCap S S.gtilde : ℝ) := lt_of_lt_of_le hdiv (Nat.le_ceil _)
  have hlt' : (k : ℝ) < (infertileCap S S.gtilde : ℝ) + 1 := by linarith
  have : k < infertileCap S S.gtilde + 1 := by exact_mod_cast hlt'
  omega

/--
**`infertile-capacity lemma`, window form.**

The infertile challenge depths of a window `[a, p)` are paid for by the spend *inside
that window*, plus the spend strictly above it and the one-level ceiling slack:
`k ≤ 1 + (π - ζ_δ + ∑_{[0,a)} ρ)/g̃ + (∑_{[a,p)} ρ)/g̃`.

`infertile_card_le_gen` is the same statement with every spend replaced by the whole
budget `ρ`, which is what makes `s` charge `ρ` a second time.  Keeping the window
explicit is what lets the ledger of `Ledger.lean` add this charge to the attempt charges
against *one* budget: searches and attempts occupy disjoint level ranges, so
`∑_{search} ρ + ∑_{attempts} ρ ≤ ρ`.
-/
theorem infertile_card_charge (hζmax : S.ζδ ≤ S.αmax) (hentry : S.αmin < S.zetaFloor)
    (hlt : S.zetaFloor < S.αmax) (a p : ℕ) :
    ((((Finset.Ico a p).filter (fun d => C.f d < S.pi)).card : ℕ) : ℝ)
      ≤ max 0 (1 + (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d) / S.gtilde)
        + (∑ d ∈ Finset.Ico a p, B.spend d) / S.gtilde := by
  classical
  set K := ((Finset.Ico a p).filter (fun d => C.f d < S.pi)).card with hK
  have hgz : 0 < S.gtilde := S.gtilde_pos hentry hlt
  have hwin : (0 : ℝ) ≤ ∑ d ∈ Finset.Ico a p, B.spend d :=
    Finset.sum_nonneg fun d _ => B.spend_nonneg d
  have hwin' : (0 : ℝ) ≤ (∑ d ∈ Finset.Ico a p, B.spend d) / S.gtilde :=
    div_nonneg hwin hgz.le
  have hhead : (0 : ℝ)
      ≤ max 0 (1 + (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d) / S.gtilde) :=
    le_max_left _ _
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · rw [h0]
    push_cast
    linarith
  have hap : a < p := by
    by_contra hcon
    push Not at hcon
    have hempty : Finset.Ico a p = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty] at hK
    simp only [Finset.filter_empty, Finset.card_empty] at hK
    omega
  have hbnd : IsFootprintBound S B a C.f := fun d _ => C.bound d (Nat.zero_le d)
  have hbudget := hbnd.infertile_budget (P := p)
    (fun d _ _ => C.gainD_nonneg_gen hζmax hentry d)
    (fun d _ _ hd => C.gtilde_le_gainD_of_infertile hζmax hentry hlt hd)
    hgz.le hpos (le_of_eq hK)
  have hfa := (C.invariants_gen hζmax hentry a).1
  have hsplit1 : ∑ m ∈ Finset.range (a + 1), B.spend m
      = (∑ d ∈ Finset.Ico 0 a, B.spend d) + B.spend a := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_succ_top (Nat.zero_le a)]
  have hsplit2 : ∑ d ∈ Finset.Ico a p, B.spend d
      = B.spend a + ∑ d ∈ Finset.Ico (a + 1) p, B.spend d :=
    Finset.sum_eq_sum_Ico_succ_bot hap _
  have hkey : ((K : ℝ) - 1) * S.gtilde
      < (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d)
        + ∑ d ∈ Finset.Ico a p, B.spend d := by
    rw [hsplit1] at hfa
    rw [hsplit2]
    linarith
  have hdiv : (K : ℝ) - 1
      < (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d) / S.gtilde
        + (∑ d ∈ Finset.Ico a p, B.spend d) / S.gtilde := by
    rw [← add_div, lt_div_iff₀ hgz]
    exact hkey
  have hle : 1 + (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d) / S.gtilde
      ≤ max 0 (1 + (S.pi - S.ζδ + ∑ d ∈ Finset.Ico 0 a, B.spend d) / S.gtilde) :=
    le_max_right _ _
  linarith

/-- If a prefix contains more depths than the maximum possible number of infertile
depths, then one of its deepest `infertileCap + 1` levels is fertile.  The lower bound on `d`
is sharp for the cardinality argument: all `infertileCap` deeper levels may be infertile. -/
theorem exists_deep_fertile (hζmax : S.ζδ ≤ S.αmax)
    (hentry : S.piBar < S.ζδ - S.ρ) {h : ℝ}
    (hh_pos : 0 < h) (hh_le : h ≤ S.gpi) {ℓ : ℕ} (hlevels : infertileCap S h < ℓ) :
    ∃ d, ℓ - infertileCap S h - 1 ≤ d ∧ d < ℓ ∧ S.pi ≤ C.f d := by
  classical
  have hcard := C.infertile_card_le hζmax hentry hh_pos hh_le (ℓ - 1)
  have hsucc : ℓ - 1 + 1 = ℓ := by omega
  rw [hsucc] at hcard
  by_contra hnone
  push Not at hnone
  let tail := Finset.Ico (ℓ - infertileCap S h - 1) ℓ
  have hsub : tail ⊆ (Finset.range ℓ).filter (fun d => C.f d < S.pi) := by
    intro d hd
    have hd' := Finset.mem_Ico.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd'.2,
      hnone d hd'.1 hd'.2⟩
  have htail : tail.card = infertileCap S h + 1 := by
    simp only [tail, Nat.card_Ico]
    omega
  have := Finset.card_le_card hsub
  rw [htail] at this
  omega

end ChallengeBound

end ProofOfSpace

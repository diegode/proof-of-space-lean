/-
# The genuine Chung-8 Filecoin specialization

This file connects the latency development to the threshold curve actually constructed
in `ChungCurve.lean`.  On `(0,1)`, `chungBeta8` is definitionally the unique zero of
the degree-eight Chung union-bound exponent.  Its endpoint values use the `0` and `1`
convention required by the paper's closed-interval shape assumptions.

There are two distinct kinds of input:

* `chungBeta8_maps`, `chungBeta8_expands`, `chungBeta8_strictMonoOn`, and
  `chungBeta8_reversal` are proved here/from `ChungCurve.lean` for the defined curve;
* `Chung8AnalyticAssumptions` records the remaining global shape facts that the paper
  states as standing analytic assumptions.  After the reductions in this file that is
  just two: concavity of `chungBeta8` on `[0,1]`, and the uniqueness of the gain
  maximizer.  The two adjusted-gain roots used to live here too; they are now derived.

Given only that explicit analytic certificate, `chung8Setting` is a `Setting` whose
`β` is exactly `chungBeta8`, and the Filecoin `GeneralRegime` and numerical parameter
bundles are theorems.  In particular, the Möbius consistency witness of `Witness.lean`
is not used anywhere in this specialization.
-/
import ProofOfSpace.ChungNumerics
import ProofOfSpace.Latency
import ProofOfSpace.Ledger
import Mathlib.Analysis.Convex.Continuous

namespace ProofOfSpace
namespace ChungCurve

open Set

/-! ### Closed-unit-interval version of the constructed threshold -/

/-- The genuine degree-eight Chung threshold on `(0,1)`, extended by `β(0)=0` and
`β(1)=1`.  Values outside `[0,1]` are irrelevant to `Setting`; the chosen clamped
extension makes the definition total. -/
noncomputable def chungBeta8 (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x < 1 then chungBeta 8 x else 1

@[simp] theorem chungBeta8_zero : chungBeta8 0 = 0 := by
  simp [chungBeta8]

@[simp] theorem chungBeta8_one : chungBeta8 1 = 1 := by
  simp [chungBeta8]

theorem chungBeta8_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chungBeta8 x = chungBeta 8 x := by
  simp [chungBeta8, not_le.mpr hx.1, hx.2]

theorem chungBeta8_maps {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    chungBeta8 x ∈ Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    simp
  rcases eq_or_lt_of_le hx.2 with hone | hx1
  · subst x
    simp
  · have hβ := chungBeta_mem (d := (8 : ℝ)) (by norm_num) hx0 hx1
    rw [chungBeta8_eq ⟨hx0, hx1⟩]
    exact ⟨hx0.le.trans hβ.1.le, hβ.2.le⟩

theorem chungBeta8_expands {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < chungBeta8 x := by
  rw [chungBeta8_eq hx]
  exact (chungBeta_mem (d := (8 : ℝ)) (by norm_num) hx.1 hx.2).1

theorem chungBeta8_reversal {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chungBeta8 (1 - chungBeta8 x) = 1 - x := by
  rw [chungBeta8_eq hx]
  have hβ := chungBeta_mem (d := (8 : ℝ)) (by norm_num) hx.1 hx.2
  have hm : 1 - chungBeta 8 x ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hβ.2], by linarith [hx.1, hβ.1]⟩
  rw [chungBeta8_eq hm]
  exact chungBeta_reversal (d := (8 : ℝ)) (by norm_num) hx.1 hx.2

theorem chungBeta8_strictMonoOn :
    StrictMonoOn chungBeta8 (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    rw [chungBeta8_zero]
    rcases eq_or_lt_of_le hy.2 with hone | hy1
    · subst y
      norm_num
    · exact hxy.trans (chungBeta8_expands ⟨hxy, hy1⟩)
  rcases eq_or_lt_of_le hy.2 with hone | hy1
  · subst y
    rw [chungBeta8_one, chungBeta8_eq ⟨hx0, hxy⟩]
    exact (chungBeta_mem (d := (8 : ℝ)) (by norm_num) hx0 hxy).2
  · rw [chungBeta8_eq ⟨hx0, hxy.trans hy1⟩, chungBeta8_eq ⟨hx0.trans hxy, hy1⟩]
    exact chungBeta_strictMonoOn (8 : ℝ) (by norm_num)
      ⟨hx0, hxy.trans hy1⟩ ⟨hx0.trans hxy, hy1⟩ hxy

/-! ### The paper's remaining analytic profile assumptions -/

/-- The global analytic facts about the genuine Chung-8 profile that the paper uses as
standing assumptions but that are not derived from the exponent construction here.

This is intentionally much smaller than `Setting`.  Mapping, strict expansion, strict
monotonicity and the reversal law are absent because they are proved for `chungBeta8`;
the Filecoin numerical inequalities are absent because `ChungNumerics.lean` discharges
them; and the two zeros of `gain_δ` are absent because they are *derived* — `αmin` by the
intermediate value theorem from `gainD8_neg_at_1_256` and `condB_holds_at_1184`
(concavity supplying continuity), and `αmax` from `αmin` by the mirror map.

What remains is exactly two assumptions about the curve: **`chungBeta8` is concave on
`[0,1]`**, and **its unadjusted gain has a unique maximizer**.  Neither is proved here,
and no model of this bundle is exhibited; see the rigidity section below. -/
structure Chung8AnalyticAssumptions where
  /-- Unique maximizer of the unadjusted gain `β(x)-x`. -/
  αg : ℝ
  concaveOn : ConcaveOn ℝ (Icc (0 : ℝ) 1) chungBeta8
  αg_mem : αg ∈ Ioo (0 : ℝ) 1
  αg_max : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → x ≠ αg →
    chungBeta8 x - x < chungBeta8 αg - αg

namespace Chung8AnalyticAssumptions

variable (H : Chung8AnalyticAssumptions)

/-! #### The adjusted gain of the constructed curve

`gain_δ` does not mention `H`: `chung8Setting` fixes `β := chungBeta8` and
`δ := 189/5000` outright.  The three signs below are pure `ChungNumerics` facts, and they
are what turn the two zeros of `gain_δ` from assumptions into consequences. -/

/-- The adjusted gain of the constructed curve, available before any `Setting` exists. -/
noncomputable def gd (x : ℝ) : ℝ := chungBeta8 x - 189 / 5000 - x

theorem gd_pi_pos : 0 < gd ((4 : ℝ)/5) := by
  rw [gd, chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
  linarith [beta_08_lower]

theorem gd_1184_pos : 0 < gd ((74 : ℝ)/625) := by
  rw [gd, chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
  have hcond := condB_holds_at_1184
  have hgpi := gpi8_bounds.1
  simp only [gpi8, gainD8] at hcond hgpi
  linarith

theorem gd_1_256_neg : gd ((1 : ℝ)/256) < 0 := by
  rw [gd, chungBeta8_eq (by norm_num : (1 / 256 : ℝ) ∈ Ioo 0 1)]
  have h := gainD8_neg_at_1_256
  simp only [gainD8] at h
  linarith

theorem gd_concaveOn (H : Chung8AnalyticAssumptions) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) gd := by
  have h : gd = chungBeta8 - fun x : ℝ => x + 189 / 5000 := by
    funext x; simp only [gd, Pi.sub_apply]; ring
  rw [h]
  exact H.concaveOn.sub (convexOn_add_const (convex_Icc 0 1) (189 / 5000))

theorem beta_αg_mem : chungBeta8 H.αg ∈ Ioo (0 : ℝ) 1 := by
  have hαg := H.αg_mem
  have hβ := chungBeta8_maps ⟨hαg.1.le, hαg.2.le⟩
  refine ⟨hαg.1.trans (chungBeta8_expands hαg), ?_⟩
  rcases eq_or_lt_of_le hβ.2 with hone | hlt
  · have hstrict := chungBeta8_strictMonoOn
      ⟨hαg.1.le, hαg.2.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hαg.2
    rw [hone, chungBeta8_one] at hstrict
    exact False.elim (lt_irrefl 1 hstrict)
  · exact hlt

/-- For the constructed curve: the decreasing mirror map `x ↦ 1 - β(x)`
fixes the maximizer.  This is the `Setting.mirror_αg` argument, run before the `Setting`
exists. -/
theorem mirror_αg : 1 - chungBeta8 H.αg = H.αg := by
  have hαg := H.αg_mem
  have hβopen := H.beta_αg_mem
  have hm : (1 - chungBeta8 H.αg) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hβopen.2], by linarith [hβopen.1]⟩
  have hgain : chungBeta8 (1 - chungBeta8 H.αg) - (1 - chungBeta8 H.αg)
      = chungBeta8 H.αg - H.αg := by
    rw [chungBeta8_reversal hαg]; ring
  by_contra hne
  have hmax := H.αg_max ⟨hm.1.le, hm.2.le⟩ hne
  linarith

/-- The maximizer is its own mirror, so it lies below `1/2` and a fortiori below `π`. -/
theorem αg_lt_pi : H.αg < (4 : ℝ)/5 := by
  have hexp := chungBeta8_expands H.αg_mem
  have hfix := H.mirror_αg
  linarith

/-- The gain at the maximizer dominates the gain at `π`, which is positive. -/
theorem gd_αg_pos : 0 < gd H.αg := by
  have hmax := H.αg_max (by norm_num : ((4 : ℝ) / 5) ∈ Icc (0 : ℝ) 1)
    (ne_of_gt H.αg_lt_pi)
  have hpi := gd_pi_pos
  simp only [gd] at hpi ⊢
  linarith

/-- Concavity gives continuity on the open interval, which is all the intermediate value
theorem needs. -/
theorem gd_continuousOn (H : Chung8AnalyticAssumptions) :
    ContinuousOn gd (Ioo (0 : ℝ) 1) := by
  have h := (H.gd_concaveOn).continuousOn_interior
  rwa [interior_Icc] at h

/-- **The left zero of `gain_δ` exists.**  `gain_δ` is negative at `1/256`
(`gainD8_neg_at_1_256`) and positive at `0.1184` (`condB_holds_at_1184`), and concavity
supplies continuity in between.  The statement does not mention `H`. -/
theorem exists_left_root (H : Chung8AnalyticAssumptions) :
    ∃ r ∈ Icc ((1 : ℝ)/256) ((74 : ℝ)/625), gd r = 0 := by
  have hsub : Icc ((1 : ℝ)/256) ((74 : ℝ)/625) ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcont := (H.gd_continuousOn).mono hsub
  have hmem : (0 : ℝ) ∈ Icc (gd ((1 : ℝ)/256)) (gd ((74 : ℝ)/625)) :=
    ⟨gd_1_256_neg.le, gd_1184_pos.le⟩
  exact intermediate_value_Icc (by norm_num : ((1 : ℝ)/256) ≤ (74 : ℝ)/625) hcont hmem

/-- `α_δ^min`, the left zero of the adjusted gain.  Derived, not assumed.  Because the
statement proved by `exists_left_root` does not mention `H`, proof irrelevance makes this
value literally the same for every instance — see `chung8_αmin_unique`. -/
noncomputable def αmin (H : Chung8AnalyticAssumptions) : ℝ :=
  Classical.choose H.exists_left_root

theorem αmin_mem_bracket : H.αmin ∈ Icc ((1 : ℝ)/256) ((74 : ℝ)/625) :=
  (Classical.choose_spec H.exists_left_root).1

theorem gainD_αmin : chungBeta8 H.αmin - (189 : ℝ) / 5000 - H.αmin = 0 :=
  (Classical.choose_spec H.exists_left_root).2

theorem αmin_pos : 0 < H.αmin := lt_of_lt_of_le (by norm_num) H.αmin_mem_bracket.1

theorem αmin_lt_pi : H.αmin < (4 : ℝ)/5 :=
  lt_of_le_of_lt H.αmin_mem_bracket.2 (by norm_num)

theorem αmin_mem_Ioo : H.αmin ∈ Ioo (0 : ℝ) 1 :=
  ⟨H.αmin_pos, H.αmin_lt_pi.trans (by norm_num)⟩

/-- The left zero lies at or below the maximizer: if it lay strictly above, the chord from
`αg` to `π` — both points where `gain_δ` is positive — would force it positive. -/
theorem αmin_mem : H.αmin ∈ Icc (0 : ℝ) H.αg := by
  refine ⟨H.αmin_pos.le, ?_⟩
  by_contra hcon
  push Not at hcon
  have hchord := concaveOn_chord_le H.gd_concaveOn
    ⟨H.αg_mem.1.le, H.αg_mem.2.le⟩
    (by norm_num : ((4 : ℝ)/5) ∈ Icc (0 : ℝ) 1) hcon H.αmin_lt_pi
  have hzero : gd H.αmin = 0 := H.gainD_αmin
  rw [hzero] at hchord
  have h1 : 0 < ((4 : ℝ)/5 - H.αmin) / ((4 : ℝ)/5 - H.αg) :=
    div_pos (by linarith [H.αmin_lt_pi]) (by linarith [H.αg_lt_pi])
  have h2 : 0 < (H.αmin - H.αg) / ((4 : ℝ)/5 - H.αg) :=
    div_pos (by linarith) (by linarith [H.αg_lt_pi])
  nlinarith [H.gd_αg_pos, gd_pi_pos]

/-- **The right root is the mirror of the left one.**  The mirror identity of
`eq:reversal` says the map
`x ↦ 1 - β(x)` preserves the gain, so it carries one zero of `gain_δ` to the other.  The
right root therefore does not have to be assumed: it is `1 - β(α_min)`. -/
noncomputable def αmax : ℝ := 1 - chungBeta8 H.αmin

theorem gainD_αmax : chungBeta8 H.αmax - (189 : ℝ) / 5000 - H.αmax = 0 := by
  have hrev := chungBeta8_reversal H.αmin_mem_Ioo
  have hroot := H.gainD_αmin
  change chungBeta8 (1 - chungBeta8 H.αmin) - (189 : ℝ) / 5000
      - (1 - chungBeta8 H.αmin) = 0
  rw [hrev]
  linarith

theorem αmax_mem : H.αmax ∈ Icc H.αg 1 := by
  constructor
  · have hmono : chungBeta8 H.αmin ≤ chungBeta8 H.αg := by
      rcases eq_or_lt_of_le H.αmin_mem.2 with heq | hlt
      · rw [heq]
      · exact (chungBeta8_strictMonoOn ⟨H.αmin_mem.1, H.αmin_mem_Ioo.2.le⟩
          ⟨H.αg_mem.1.le, H.αg_mem.2.le⟩ hlt).le
    have := H.mirror_αg
    change H.αg ≤ 1 - chungBeta8 H.αmin
    linarith
  · have := (chungBeta8_maps ⟨H.αmin_mem.1, H.αmin_mem_Ioo.2.le⟩).1
    change 1 - chungBeta8 H.αmin ≤ 1
    linarith

end Chung8AnalyticAssumptions

/-- The unique gain maximizer is fixed by the mirror involution, hence lies below `1/2`
(and therefore below Filecoin's `π = 4/5`). -/
theorem chung8_αg_lt_pi (H : Chung8AnalyticAssumptions) : H.αg < (4 : ℝ) / 5 :=
  H.αg_lt_pi

/-! ### Exact Chung-8 `Setting` and Filecoin bundles -/

/-- The paper's parameter setting with the *actual constructed Chung-8 curve* as `β`. -/
noncomputable def chung8Setting (H : Chung8AnalyticAssumptions) : Setting where
  β := chungBeta8
  αg := H.αg
  δ := 189 / 5000
  pi := 4 / 5
  ρ := 4 / 5
  ζδ := 4311 / 5000
  αmin := H.αmin
  αmax := H.αmax
  β_maps := fun _ hx => chungBeta8_maps hx
  β_zero := chungBeta8_zero
  β_strictMonoOn := chungBeta8_strictMonoOn
  β_concaveOn := H.concaveOn
  β_expands := fun _ hx => chungBeta8_expands hx
  β_reversal := fun _ hx => chungBeta8_reversal hx
  αg_mem := H.αg_mem
  αg_max := fun _ hx hne => H.αg_max hx hne
  δ_nonneg := by norm_num
  ρ_nonneg := by norm_num
  pi_mem := by norm_num
  αg_lt_pi := chung8_αg_lt_pi H
  gpi_pos := by
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower]
  αmin_mem := H.αmin_mem
  αmax_mem := H.αmax_mem
  gainD_αmin := H.gainD_αmin
  gainD_αmax := H.gainD_αmax

@[simp] theorem chung8Setting_β (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).β = chungBeta8 := rfl


@[simp] theorem chung8Setting_delta (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).δ = (189 : ℝ) / 5000 := rfl

@[simp] theorem chung8Setting_pi (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).pi = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_rho (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).ρ = (4 : ℝ) / 5 := rfl

@[simp] theorem chung8Setting_zetaDelta (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).ζδ = (4311 : ℝ) / 5000 := rfl

/-! ### Rigidity of the analytic assumption bundle

After the reductions above, `Chung8AnalyticAssumptions` carries a single piece of data,
the gain maximizer `αg`, and three `Prop` fields.  `chung8_αg_unique` shows even `αg` is
pinned down by `αg_max`, and `αmin`/`αmax` are outright definitions, so any two instances
give literally the same `chung8Setting`.  Nothing in the Filecoin specialization depends
on *which* instance is supplied.

This is a rigidity statement, **not** a consistency one.  Unlike `Setting`, for which
`Witness.lean` exhibits a model, nothing shows `Chung8AnalyticAssumptions` is inhabited:
if `chungBeta8` failed to be concave on the *closed* interval, every `chung8_*` corollary
would be vacuously true.  The delicate half is the endpoint extension.  Setting `β(0)=0`
is concavity-compatible for free — a concave function on `(0,1)` with nonnegative values
stays concave when the left endpoint is lowered to `0`.  Setting `β(1)=1` is not free: it
needs `chungBeta 8 x → 1` as `x → 1⁻`, which is true but is not proved here.
-/

theorem chung8_gainD_pi_pos (H : Chung8AnalyticAssumptions) :
    0 < (chung8Setting H).gainD ((4 : ℝ) / 5) :=
  (chung8Setting H).gpi_pos'

/-- The unique gain maximizer is determined by the assumption `αg_max` alone. -/
theorem chung8_αg_unique (H₁ H₂ : Chung8AnalyticAssumptions) : H₁.αg = H₂.αg := by
  by_contra hne
  have h1 := H₁.αg_max ⟨H₂.αg_mem.1.le, H₂.αg_mem.2.le⟩ (Ne.symm hne)
  have h2 := H₂.αg_max ⟨H₁.αg_mem.1.le, H₁.αg_mem.2.le⟩ hne
  linarith

/-- `αmin` is defined by a `Classical.choose` on an `H`-free statement, so proof
irrelevance makes it the same real number for every instance. -/
theorem chung8_αmin_unique (H₁ H₂ : Chung8AnalyticAssumptions) :
    H₁.αmin = H₂.αmin := rfl

theorem chung8_αmax_unique (H₁ H₂ : Chung8AnalyticAssumptions) :
    H₁.αmax = H₂.αmax := rfl


/-- `π` sits strictly inside the active interval `(α_δ^min, α_δ^max)`: the left zero is
below `0.1184` by construction, and the right zero is above `π` because `gain_δ(π) > 0`
while `gain_δ` is concave. -/
theorem chung8_pi_lt_αmax (H : Chung8AnalyticAssumptions) : (4 : ℝ) / 5 < H.αmax := by
  have hgpos := chung8_gainD_pi_pos H
  have hroot : (chung8Setting H).gainD H.αmax = 0 := H.gainD_αmax
  have hαgpi := chung8_αg_lt_pi H
  have hαg : 0 < (chung8Setting H).gainD H.αg := H.gd_αg_pos
  rcases lt_trichotomy H.αmax ((4 : ℝ) / 5) with h | h | h
  · rcases eq_or_lt_of_le H.αmax_mem.1 with heq | hlt
    · rw [heq] at hαg; linarith
    · have hchord := (chung8Setting H).concave_interior
        ⟨H.αg_mem.1.le, H.αg_mem.2.le⟩
        (by norm_num : ((4 : ℝ) / 5) ∈ Icc (0 : ℝ) 1) hαgpi ⟨hlt, h⟩
      rw [hroot] at hchord
      have h1 : 0 < ((4 : ℝ) / 5 - H.αmax) / ((4 : ℝ) / 5 - H.αg) :=
        div_pos (by linarith) (by linarith)
      have h2 : 0 < (H.αmax - H.αg) / ((4 : ℝ) / 5 - H.αg) :=
        div_pos (by linarith) (by linarith)
      nlinarith
  · rw [h] at hroot; linarith
  · exact h

/-- The abstract `Setting.gpi` is exactly the `gpi8` computed from the constructed
degree-eight Chung threshold. -/
theorem chung8Setting_gpi (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).gpi = gpi8 := by
  simp only [Setting.gpi, Setting.gainD, chung8Setting_β, chung8Setting_delta,
    chung8Setting_pi, gpi8, gainD8]
  rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]

/-- The abstract `Setting.gainD` at the mid-point `σ̃ = 3/5`, in terms of the
constructed degree-eight Chung threshold. -/
theorem chung8Setting_gainD_06 (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).gainD (3/5) = gainD8 (3/5) := by
  simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta, gainD8]
  rw [chungBeta8_eq (by norm_num : (3 / 5 : ℝ) ∈ Ioo 0 1)]

/-- Filecoin's tracked source weight, now attached to the genuine Chung-8 setting. -/
noncomputable def chung8Tracking (H : Chung8AnalyticAssumptions) :
    Tracking (chung8Setting H) where
  σ := 74 / 625
  σ_gt := by
    have hpositive : 0 < (chung8Setting H).gainD ((74 : ℝ) / 625) := by
      simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta]
      rw [chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
      have hcond := condB_holds_at_1184
      have hgpi := gpi8_bounds.1
      simp only [gpi8, gainD8] at hcond hgpi
      linarith
    by_contra hcon
    push Not at hcon
    have hnonpos := (chung8Setting H).gainD_nonpos_of_le_αmin
      (by norm_num : (74 / 625 : ℝ) ∈ Icc 0 1) hcon
    linarith
  σ_lt := by norm_num
  mid := 3 / 5
  mid_ge := by norm_num
  mid_le := by norm_num
  mid_gain := by
    have hmin : min (chung8Setting H).gpi ((chung8Setting H).gainD (74 / 625) / 2)
        ≤ (chung8Setting H).gpi := min_le_left _ _
    have hcert : 2 * (chung8Setting H).gpi ≤ (chung8Setting H).gainD (3 / 5) := by
      rw [chung8Setting_gainD_06, chung8Setting_gpi]
      exact two_gpi_le_gainD8_06
    linarith

@[simp] theorem chung8Tracking_mid (H : Chung8AnalyticAssumptions) :
    (chung8Tracking H).mid = (3 : ℝ) / 5 := rfl

@[simp] theorem chung8Tracking_sigma (H : Chung8AnalyticAssumptions) :
    (chung8Tracking H).σ = (74 : ℝ) / 625 := rfl

/-! ### The scalar facts that collapse the general constants

The Filecoin specialization does not assume these; it proves them of the constructed
curve, and `chung8Filecoin` records the three collapses they imply.  They are the
inequalities `eq:no-break-conditions` of `app:filecoin`. -/

/-- `π̄ < ζ_δ - ρ`: the challenge floor stays above the tracking floor. -/
theorem chung8_entry (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).piBar < (chung8Setting H).ζδ - (chung8Setting H).ρ := by
    simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi,
      chung8Setting_zetaDelta, chung8Setting_rho]
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower]

/-- `ζ_δ ≤ α_δ^max`: the challenge weight is inside the positive-gain interval. -/
theorem chung8_zeta_le (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).ζδ ≤ (chung8Setting H).αmax := by
    have hpi : (4 / 5 : ℝ) ∈ Icc 0 1 := by norm_num
    have hzeta : (4311 / 5000 : ℝ) ∈ Icc 0 1 := by norm_num
    have hmono := chungBeta8_strictMonoOn hpi hzeta (by norm_num)
    have hpositive : 0 < (chung8Setting H).gainD ((4311 : ℝ) / 5000) := by
      simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta]
      rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)] at hmono
      linarith [hmono, beta_08_lower]
    by_contra hcon
    push Not at hcon
    have hnonpos := (chung8Setting H).gainD_nonpos_of_αmax_le hzeta hcon.le
    linarith

/-- `gain_δ(σ) ≥ 2 g_π` at `σ = 0.1184`, with `0.22268… ≥ 0.22262…` of little room. -/
theorem chung8_condB (H : Chung8AnalyticAssumptions) :
    2 * (chung8Setting H).gpi ≤ (chung8Setting H).gainD (chung8Tracking H).σ := by
    rw [chung8Setting_gpi]
    simp only [Setting.gainD, chung8Setting_β, chung8Setting_delta,
      chung8Tracking_sigma]
    rw [chungBeta8_eq (by norm_num : (74 / 625 : ℝ) ∈ Ioo 0 1)]
    exact condB_holds_at_1184

/-- `ρ < β_δ(π) - π̄`: the whole budget cannot pay for one chain break. -/
theorem chung8_condC (H : Chung8AnalyticAssumptions) :
    (chung8Setting H).ρ <
      (chung8Setting H).pi + (chung8Setting H).gpi - (chung8Setting H).piBar := by
    simp only [Setting.piBar, chung8Setting_β, chung8Setting_pi,
      chung8Setting_rho]
    rw [chung8Setting_gpi]
    rw [chungBeta8_eq (by norm_num : (4 / 5 : ℝ) ∈ Ioo 0 1)]
    linarith [beta_08_lower, gpi8_bounds.1]

theorem chung8Filecoin (H : Chung8AnalyticAssumptions) :
    FilecoinLatencyParameters (chung8Setting H) (chung8Tracking H) where
  pi_eq := rfl
  rho_eq := rfl
  zetaDelta_eq := rfl
  sigma_eq := rfl
  gpi_lower := by rw [chung8Setting_gpi]; exact gpi8_bounds.1
  gpi_upper := by rw [chung8Setting_gpi]; exact gpi8_bounds.2
  ghat_eq := (chung8Tracking H).ghat_eq_gpi (chung8_condB H)
  gtilde_eq :=
    gtilde_eq_gpi
      (by simp only [Setting.zetaFloor]; linarith [chung8_entry H])
      (by
        simp only [Setting.zetaFloor, chung8Setting_zetaDelta, chung8Setting_rho,
          chung8Setting_pi]
        norm_num)
  mid_eq := rfl
  bMax_eq :=
    bMax_eq_zero (by
      have hb : (chung8Setting H).betaD (chung8Setting H).pi
          = (chung8Setting H).pi + (chung8Setting H).gpi := by
        simp only [Setting.betaD_eq]; rfl
      rw [(chung8Tracking H).lam_eq_piBar (chung8_condB H), hb]
      linarith [chung8_condC H])

/-- The Filecoin setting satisfies `eq:scalar-conditions`, so `latency_general` is not
vacuous here.  The entry condition follows from the stronger `chung8_entry`, since
`α_δ^min < π̄` always. -/
theorem chung8GeneralRegime (H : Chung8AnalyticAssumptions) :
    GeneralRegime (chung8Setting H) where
  entry := by
    have h := chung8_entry H
    have hmin := (chung8Setting H).αmin_lt_piBar
    simp only [Setting.zetaFloor]
    linarith
  zeta_le := chung8_zeta_le H

/-- The two bundles used by the public latency theorem are simultaneously satisfied by
the defined Chung-8 curve, conditional only on the paper's explicitly isolated global
analytic profile assumptions. -/
theorem chung8_filecoin_bundles (H : Chung8AnalyticAssumptions) :
    FilecoinLatencyParameters (chung8Setting H) (chung8Tracking H) ∧
      GeneralRegime (chung8Setting H) :=
  ⟨chung8Filecoin H, chung8GeneralRegime H⟩

/-! ### Public latency corollaries specialized to the genuine Chung curve -/

/-- `cor:filecoin`, with `Setting.β` definitionally equal to the constructed
Chung-8 threshold (up to its endpoint extension). -/
theorem chung8_latency_corollary (H : Chung8AnalyticAssumptions)
    {V : Type u} {ℓ n : ℕ}
    (G : Concrete.LayeredGraph V (chung8Setting H) ℓ n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5) (hℓ : 14 < ℓ)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting H).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((FilecoinLatencyParameters.filecoinZMin (chung8Setting H).gpi ℓ : ℝ) - 1) *
          ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) :=
  (chung8Filecoin H).latency_corollary G P (chung8GeneralRegime H)
    hn hαpi hℓ hDepth A hA hred hweight

/-- The first two-link endpoint of the generic Filecoin ledger. -/
theorem chung8_latency_21 (H : Chung8AnalyticAssumptions)
    {V : Type u} {n : ℕ}
    (G : Concrete.LayeredGraph V (chung8Setting H) 21 n)
    (P : Concrete.Pebbling G)
    (hn : 0 < n) (hαpi : G.αpi = (1 : ℝ) / 5)
    (hDepth : G.DepthRobust G.αpi)
    (A : Finset V) (hA : A ⊆ G.layer 0)
    (hred : ∀ v ∈ A, v ∉ P.red 0)
    (hweight : (chung8Setting H).ζδ ≤ Concrete.Pebbling.weight n A) :
    P.HasUnpebbledPathInFootprint A
      ((1 : ℝ) / 5 * n +
        ((1 : ℝ) / 5 - (74 : ℝ) / 625) * n) :=
  (chung8Filecoin H).latency_21 G P (chung8GeneralRegime H)
    hn hαpi hDepth A hA hred hweight

/-! ### The improved growth constant

The two-piece potential `ProofOfSpace.growthPot` replaces the single-constant level
count `a = max{1, (π - σ)/ĝ}` by `Φ_{σ̃}(π) + 1`, charging `2 ĝ` per level on
`[σ, σ̃]`.  At the Filecoin Chung-8 parameters the mid-point `σ̃ = 3/5` is certified
by `two_gpi_le_gainD8_06`.

The two window constants to compare are `Φ_{3/5}(π) + 1 < 4.961` and `a > 6.118`: the
`+1` is the free level that `gain_sum_ge` extracts at the source and that the potential
argument does not recover (see the section header of `Growth.lean`).  The certified
saving is therefore `1.15` levels per chain link, not `2.15`;
`chung8_growthPot_window_gap` states it.

**This is wired into the ledger** through `chung8Tracking`'s mid-point field
`σ̃ = 3/5`: `growthConst` takes the minimum of the two, `h₁ = growthConst + 1` becomes
`5.957 < h₁ < 5.961` instead of `7.118 < h₁ < 7.125`, and the certified per-link slope
`(α_π - σ)/h₁` rises from `0.01146` to `0.01370`.  The results below are the standalone
comparison of the two constants; `FilecoinLatencyParameters.growthConst_eq` is what the
numerics actually use.
-/

/-- The mid-point certificate `2 ĝ ≤ gain_δ(3/5)`, transported to the abstract
`Setting`. -/
theorem chung8_midpoint (H : Chung8AnalyticAssumptions) :
    2 * (chung8Tracking H).ghat ≤ (chung8Setting H).gainD (3/5) := by
  rw [chung8Setting_gainD_06, (chung8Filecoin H).ghat_eq, chung8Setting_gpi]
  exact two_gpi_le_gainD8_06

/-- the source condition plus concavity spread the certificate over the whole segment
`[σ, 3/5]`, which is exactly the hypothesis `growthPot_window` needs. -/
theorem chung8_midpoint_seg (H : Chung8AnalyticAssumptions) :
    ∀ x, (chung8Tracking H).σ ≤ x → x ≤ (3 : ℝ)/5 →
      2 * (chung8Tracking H).ghat ≤ (chung8Setting H).gainD x :=
  fun _ hx hxc =>
    two_ghat_le_gainD_of_mem (chung8_midpoint H) (by norm_num) hx hxc

/-- The two-piece level count at the Filecoin Chung-8 parameters is below `3.961`.  The
window constant it produces is one more than this, `Φ_{3/5}(π) + 1 < 4.961`; the
comparison against `a` is `chung8_growthPot_window_gap`. -/
theorem chung8_growthPot_lt (H : Chung8AnalyticAssumptions) :
    growthPot (chung8Setting H) (chung8Tracking H) (3/5) ((chung8Setting H).pi)
      < (3961 : ℝ)/1000 := by
  have hcπ : (3 : ℝ)/5 ≤ (chung8Setting H).pi := by
    rw [chung8Setting_pi]; norm_num
  have hg : (chung8Tracking H).ghat = (chung8Setting H).gpi :=
    (chung8Filecoin H).ghat_eq
  have hlow : (1113 : ℝ)/10000 < (chung8Setting H).gpi := by
    rw [chung8Setting_gpi]; exact gpi8_bounds.1
  have hpos : 0 < (chung8Tracking H).ghat := (chung8Tracking H).ghat_pos
  rw [growthPot_pi hcπ, chung8Setting_pi, hg]
  change ((3 : ℝ)/5 - (74 : ℝ)/625) / (2 * (chung8Setting H).gpi)
      + ((4 : ℝ)/5 - (3 : ℝ)/5) / (chung8Setting H).gpi < (3961 : ℝ)/1000
  rw [hg] at hpos
  rw [div_add_div _ _ (by positivity) (ne_of_gt hpos), div_lt_iff₀ (by positivity)]
  nlinarith [hlow, hpos]

/-- The same count under the old single-constant bound, for comparison.  This is the
bare quotient; `chung8_asymptoticGrowth_gt` transports it to `asymptoticGrowth` itself,
which is what `growth_window` uses. -/
theorem chung8_asymptoticGrowthDiv_gt (H : Chung8AnalyticAssumptions) :
    (6118 : ℝ)/1000 <
      ((chung8Setting H).pi - (chung8Tracking H).σ) / (chung8Tracking H).ghat := by
  have hg : (chung8Tracking H).ghat = (chung8Setting H).gpi :=
    (chung8Filecoin H).ghat_eq
  have hhigh : (chung8Setting H).gpi < (557 : ℝ)/5000 := by
    rw [chung8Setting_gpi]; exact gpi8_bounds.2
  have hpos : 0 < (chung8Tracking H).ghat := (chung8Tracking H).ghat_pos
  rw [hg] at hpos
  rw [chung8Setting_pi, hg]
  change (6118 : ℝ)/1000 < ((4 : ℝ)/5 - (74 : ℝ)/625) / (chung8Setting H).gpi
  rw [lt_div_iff₀ hpos]
  nlinarith [hhigh, hpos]

/-- `a > 6.118`: the constant that `growth_window` actually charges. -/
theorem chung8_asymptoticGrowth_gt (H : Chung8AnalyticAssumptions) :
    (6118 : ℝ)/1000 < asymptoticGrowth (chung8Setting H) (chung8Tracking H) :=
  lt_of_lt_of_le (chung8_asymptoticGrowthDiv_gt H) (le_max_right _ _)

/-- **The certified improvement, as a comparison of the two window constants.**

`growthPot_window` charges `Φ_{3/5}(π) + 1` levels per chain link and `growth_window`
charges `a`.  At the Filecoin Chung-8 parameters the gap is at least `1.15` levels —
`Φ_{3/5}(π) + 1 < 4.961` against `a > 6.118`.  The saving is the half-price segment
`(σ̃ - σ)/(2 ĝ) ≈ 2.16` less the one free source level that the potential forgoes. -/
theorem chung8_growthPot_window_gap (H : Chung8AnalyticAssumptions) :
    growthPot (chung8Setting H) (chung8Tracking H) (3/5) ((chung8Setting H).pi) + 1
        + (115 : ℝ)/100
      < asymptoticGrowth (chung8Setting H) (chung8Tracking H) := by
  have hlt := chung8_growthPot_lt H
  have hgt := chung8_asymptoticGrowth_gt H
  linarith

/-- The same conclusion via the abstract criterion
`growthPot_pi_succ_lt_asymptoticGrowth`, which asks only that the doubled-gain segment
exceed `2 ĝ`.  At Chung-8 that segment `[σ, 3/5]` has length `0.482`, comfortably
above `2 ĝ < 0.223`. -/
theorem chung8_growthPot_succ_lt (H : Chung8AnalyticAssumptions) :
    growthPot (chung8Setting H) (chung8Tracking H) (3/5) ((chung8Setting H).pi) + 1
      < asymptoticGrowth (chung8Setting H) (chung8Tracking H) := by
  have hcπ : (3 : ℝ)/5 ≤ (chung8Setting H).pi := by
    rw [chung8Setting_pi]; norm_num
  refine growthPot_pi_succ_lt_asymptoticGrowth hcπ ?_
  have hg : (chung8Tracking H).ghat = (chung8Setting H).gpi :=
    (chung8Filecoin H).ghat_eq
  have hhigh : (chung8Setting H).gpi < (557 : ℝ)/5000 := by
    rw [chung8Setting_gpi]; exact gpi8_bounds.2
  rw [hg]
  change 2 * (chung8Setting H).gpi < (3 : ℝ)/5 - (74 : ℝ)/625
  linarith

end ChungCurve
end ProofOfSpace

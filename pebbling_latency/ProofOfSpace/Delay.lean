import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # The reference-trajectory delay clock

The scalar recurrence is a lower bound on graph footprints. This module does
not assert an upper bound on actual graph expansion.
-/
namespace ProofOfSpace.Delay
open Set

/-- Linear interpolation of the times `0, ..., t` at the knots `y 0, ..., y t`.
Only its restriction to that knot interval is used. -/
noncomputable def scale (y : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | t + 1, x => if x ≤ y 1 then (x - y 0) / (y 1 - y 0)
      else 1 + scale (fun i => y (i + 1)) t x

/-- Every reference step before fertility is at least the base gain. -/
def Spaced (y : ℕ → ℝ) (t : ℕ) (g : ℝ) : Prop :=
  ∀ i < t, g ≤ y (i + 1) - y i

lemma Spaced.tail {y : ℕ → ℝ} {t : ℕ} {g : ℝ}
    (h : Spaced y (t + 1) g) : Spaced (fun i => y (i + 1)) t g := by
  intro i hi
  exact h (i + 1) (by omega)

lemma Spaced.mono {y : ℕ → ℝ} {t : ℕ} {g : ℝ} (hg : 0 < g)
    (h : Spaced y t g) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ t) : y i ≤ y j := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; rfl
    · have hprev := ih (by omega) (by omega)
      have hstep := h j (by omega)
      linarith

lemma scale_zero {y : ℕ → ℝ} {t : ℕ} {g : ℝ} (hg : 0 < g)
    (h : Spaced y t g) : scale y t (y 0) = 0 := by
  cases t with
  | zero => rfl
  | succ t =>
    have hs := h 0 (by omega)
    simp only [Nat.zero_add] at hs
    rw [scale, if_pos (by linarith)]
    simp

lemma scale_shift {y : ℕ → ℝ} {t : ℕ} {g x : ℝ} (hg : 0 < g)
    (h : Spaced y (t + 1) g) (ht : 0 < t) (hx : y 1 ≤ x) :
    scale y (t + 1) x = 1 + scale (fun i => y (i + 1)) t x := by
  by_cases he : x = y 1
  · subst x
    have hs := h 0 (by omega)
    simp only [Nat.zero_add] at hs
    rw [scale, if_pos le_rfl]
    rw [show (y 1 - y 0) / (y 1 - y 0) = 1 from div_self (by linarith)]
    rw [show scale (fun i => y (i + 1)) t (y 1) = 0 from scale_zero hg h.tail]
    simp
  · rw [scale, if_neg (fun hx' => he (le_antisymm hx' hx))]

lemma scale_last {y : ℕ → ℝ} {t : ℕ} {g : ℝ} (hg : 0 < g)
    (h : Spaced y t g) : scale y t (y t) = t := by
  induction t generalizing y with
  | zero => simp [scale]
  | succ t ih =>
    cases t with
    | zero =>
      have hs := h 0 (by omega)
      simp only [Nat.zero_add] at hs
      simp [scale, div_self (show y 1 - y 0 ≠ 0 by linarith)]
    | succ t =>
      rw [scale_shift hg h (by omega) (h.mono hg (by omega) le_rfl)]
      rw [show y (t + 1 + 1) = (fun i => y (i + 1)) (t + 1) from rfl,
        ih h.tail]
      push_cast; ring

/-- The interpolated clock is increasing and has slope at most `1/g`. -/
theorem scale_calculus {y : ℕ → ℝ} {t : ℕ} {g : ℝ} (hg : 0 < g)
    (h : Spaced y t g) {u v : ℝ} (hu : y 0 ≤ u) (huv : u ≤ v) (hv : v ≤ y t) :
    0 ≤ scale y t v - scale y t u ∧
      scale y t v - scale y t u ≤ (v - u) / g := by
  induction t generalizing y u v with
  | zero => simp only [scale, sub_self]; exact ⟨le_rfl, div_nonneg (by linarith) hg.le⟩
  | succ t ih =>
    have hs := h 0 (by omega)
    simp only [Nat.zero_add] at hs
    have hgap : 0 < y 1 - y 0 := by linarith
    by_cases hv1 : v ≤ y 1
    · rw [scale, if_pos hv1, scale, if_pos (huv.trans hv1)]
      rw [← sub_div]
      have he : v - y 0 - (u - y 0) = v - u := by ring
      rw [he]
      exact ⟨div_nonneg (sub_nonneg.mpr huv) hgap.le,
        div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hg hs⟩
    · have ht : 0 < t := by
        by_contra hn
        have he : t = 0 := by omega
        subst t
        exact hv1 hv
      by_cases hu1 : y 1 ≤ u
      · rw [scale_shift hg h ht (by linarith), scale_shift hg h ht hu1]
        simpa only [add_sub_add_left_eq_sub] using ih h.tail hu1 huv hv
      · have hleft : 0 ≤ (y 1 - u) / (y 1 - y 0) ∧
            (y 1 - u) / (y 1 - y 0) ≤ (y 1 - u) / g :=
          ⟨div_nonneg (by linarith) hgap.le,
            div_le_div_of_nonneg_left (by linarith) hg hs⟩
        have hright := ih h.tail (u := y 1) (v := v) le_rfl (by linarith) hv
        rw [scale_zero hg h.tail] at hright
        rw [scale_shift hg h ht (by linarith), scale, if_pos (by linarith)]
        have hid : 1 - (u - y 0) / (y 1 - y 0) = (y 1 - u) / (y 1 - y 0) := by
          field_simp; ring
        constructor
        · linarith [hleft.1, hright.1]
        · have hsum : (y 1 - u) / g + (v - y 1) / g = (v - u) / g := by ring
          linarith [hleft.2, hright.2]

lemma exists_segment {y : ℕ → ℝ} {t : ℕ} {g v : ℝ} (_hg : 0 < g)
    (h : Spaced y t g) (ht : 0 < t) (hv : v ∈ Icc (y 0) (y t)) :
    ∃ i < t, v ∈ Icc (y i) (y (i + 1)) := by
  induction t generalizing y with
  | zero => omega
  | succ t ih =>
    by_cases hv1 : v ≤ y 1
    · exact ⟨0, by omega, hv.1, hv1⟩
    · have ht' : 0 < t := by
        by_contra hn
        have he : t = 0 := by omega
        subst t
        exact hv1 hv.2
      obtain ⟨i, hi, hlo, hhi⟩ := ih h.tail ht' ⟨by linarith, hv.2⟩
      exact ⟨i + 1, by omega, hlo, hhi⟩

lemma scale_segment {y : ℕ → ℝ} {t i : ℕ} {g v : ℝ} (hg : 0 < g)
    (h : Spaced y t g) (hi : i < t) (hv : v ∈ Icc (y i) (y (i + 1))) :
    scale y t v = (i : ℝ) + (v - y i) / (y (i + 1) - y i) := by
  induction t generalizing y i with
  | zero => omega
  | succ t ih =>
    cases i with
    | zero => simp [scale, if_pos hv.2]
    | succ i =>
      have hv1 : y 1 ≤ v := (h.mono hg (by omega) (by omega)).trans hv.1
      rw [scale_shift hg h (by omega) hv1, ih h.tail (by omega) hv]
      push_cast; ring

/-- A finite free trajectory, stopped at its first certified fertile value. -/
structure Trajectory (F : ℝ → ℝ) (p g : ℝ) where
  y : ℕ → ℝ
  t : ℕ
  positive : 0 < g
  time_pos : 0 < t
  spaced : Spaced y t g
  below : ∀ i < t, y i < p
  reaches : p ≤ y t
  next : ∀ i < t, F (y i) = y (i + 1)
  at_top : F p = p + g
  concave : ConcaveOn ℝ (Icc (y 0) p) F

namespace Trajectory
variable {F : ℝ → ℝ} {p g : ℝ} (T : Trajectory F p g)

private lemma affine_concave (A C : ℝ) :
    ConcaveOn ℝ (Icc (T.y 0) p) (fun x => F x + A * x + C) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz a b ha hb hab
  have hc := T.concave.2 hx hz ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have hC : a * C + b * C = C := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- Progress charged at the base rate, including a free step that overshoots
fertility. The endpoint `v' = p` is allowed for later graph accounting. -/
theorem progress {v v' : ℝ} (hv : v ∈ Icc (T.y 0) p)
    (hv' : v' ∈ Icc (T.y 0) p) (hcost : v' ≤ F v) :
    g ≤ g * (scale T.y T.t v' - scale T.y T.t v) + (F v - v') := by
  have hg := T.positive
  obtain ⟨i, hi, hvi⟩ := exists_segment hg T.spaced T.time_pos
    ⟨hv.1, hv.2.trans T.reaches⟩
  have hbase : T.y 0 ≤ T.y i := T.spaced.mono hg (by omega) (by omega)
  have hw : 0 < T.y (i + 1) - T.y i := lt_of_lt_of_le hg (T.spaced i hi)
  have hscalev := scale_segment hg T.spaced hi hvi
  by_cases hi' : i + 1 < T.t
  · let θ := (v - T.y i) / (T.y (i + 1) - T.y i)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hvi.1]) hw.le
    have hθ1 : θ ≤ 1 := (div_le_one hw).mpr (by linarith [hvi.2])
    have hθeq : θ * (T.y (i + 1) - T.y i) = v - T.y i := by
      dsimp [θ]; exact div_mul_cancel₀ _ (ne_of_gt hw)
    have hvcombo : (1 - θ) * T.y i + θ * T.y (i + 1) = v := by nlinarith
    let w := (1 - θ) * T.y (i + 1) + θ * T.y (i + 2)
    have hgap2 := T.spaced (i + 1) hi'
    have hwi : w ∈ Icc (T.y (i + 1)) (T.y (i + 2)) := by
      dsimp [w]; constructor <;> nlinarith
    have hwbase : T.y 0 ≤ w :=
      (T.spaced.mono hg (by omega) (by omega)).trans hwi.1
    have hwtop : w ≤ T.y T.t := hwi.2.trans (T.spaced.mono hg (by omega) le_rfl)
    have hF : w ≤ F v := by
      have hc := T.concave.2 ⟨hbase, (T.below i hi).le⟩
        ⟨T.spaced.mono hg (by omega) (by omega), (T.below (i + 1) hi').le⟩
        (by linarith : 0 ≤ 1 - θ) hθ0 (by ring : 1 - θ + θ = 1)
      simp only [smul_eq_mul, T.next i hi, T.next (i + 1) hi', hvcombo] at hc
      exact hc
    have hscalew := scale_segment hg T.spaced hi' hwi
    have hwdiff : scale T.y T.t w = scale T.y T.t v + 1 := by
      rw [hscalew, hscalev]
      have hden : T.y (i + 2) - T.y (i + 1) ≠ 0 := by linarith
      have he : (w - T.y (i + 1)) / (T.y (i + 2) - T.y (i + 1)) = θ := by
        apply (div_eq_iff hden).mpr
        dsimp [w]; ring
      rw [he]
      change (i + 1 : ℕ) + θ = (i : ℝ) + θ + 1
      push_cast; ring
    rcases le_total v' w with hvw | hwv
    · have hcal := (scale_calculus hg T.spaced hv'.1 hvw hwtop).2
      have hmul := (le_div_iff₀ hg).mp hcal
      rw [hwdiff] at hmul
      nlinarith
    · have hcal := (scale_calculus hg T.spaced hwbase hwv
        (hv'.2.trans T.reaches)).1
      rw [hwdiff] at hcal
      nlinarith
  · have hit : i + 1 = T.t := by omega
    have hip : T.y i < p := T.below i hi
    have hlast : p ≤ T.y (i + 1) := by rw [hit]; exact T.reaches
    let r := g / (T.y (i + 1) - T.y i)
    have hr0 : 0 ≤ r := div_nonneg hg.le hw.le
    have hr1 : r ≤ 1 := (div_le_one hw).mpr (T.spaced i hi)
    have hreq : r * (T.y (i + 1) - T.y i) = g := by
      dsimp [r]; exact div_mul_cancel₀ _ (ne_of_gt hw)
    let H := fun x => F x - r * x + p * r - p - g
    have hc : ConcaveOn ℝ (Icc (T.y 0) p) H := by
      convert T.affine_concave (-r) (p * r - p - g) using 1
      ext x; dsimp [H]; ring
    have hleft : 0 ≤ H (T.y i) := by
      dsimp [H]; rw [T.next i hi]
      have := mul_nonneg (sub_nonneg.mpr hlast) (sub_nonneg.mpr hr1)
      nlinarith
    have hright : H p = 0 := by dsimp [H]; rw [T.at_top]; ring
    have hHv : 0 ≤ H v := by
      have hm := hc.ge_on_segment ⟨hbase, hip.le⟩ ⟨hbase.trans hip.le, le_rfl⟩
        (show v ∈ segment ℝ (T.y i) p by rw [segment_eq_Icc hip.le]; exact ⟨hvi.1, hv.2⟩)
      rw [hright, min_eq_right hleft] at hm
      exact hm
    have hscalep := scale_segment hg T.spaced hi ⟨hip.le, hlast⟩
    have hdifference : g * (scale T.y T.t p - scale T.y T.t v) = (p - v) * r := by
      rw [hscalep, hscalev]; dsimp [r]; ring
    have hcal := (scale_calculus hg T.spaced hv'.1 hv'.2 T.reaches).2
    have hmul := (le_div_iff₀ hg).mp hcal
    dsimp [H] at hHv
    nlinarith

/-- The manuscript's delay bound in its general, floor-based form. -/
theorem delay_bound {b : ℕ} (hb : 1 ≤ b) (f r : ℕ → ℝ)
    (hband : ∀ i < b, f i ∈ Icc (T.y 0) p)
    (hr : ∀ i, 0 ≤ r i)
    (hstep : ∀ i, i + 1 < b → f (i + 1) = F (f i) - r (i + 1)) :
    ((b : ℝ) - 1 - (scale T.y T.t p - scale T.y T.t (f 0))) * g ≤
      ∑ i ∈ Finset.range b, r i := by
  have htel : ∀ k < b,
      (k : ℝ) * g ≤ g * (scale T.y T.t (f k) - scale T.y T.t (f 0)) +
        ∑ i ∈ Finset.range (k + 1), r i := by
    intro k hk
    induction k with
    | zero => simpa using hr 0
    | succ k ih =>
      have hp := T.progress (hband k (by omega)) (hband (k + 1) hk)
        (by rw [hstep k hk]; linarith [hr (k + 1)])
      have hi := ih (by omega)
      have he : F (f k) - f (k + 1) = r (k + 1) := by rw [hstep k hk]; ring
      rw [he] at hp
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  have ht := htel (b - 1) (by omega)
  have hm := (scale_calculus T.positive T.spaced (hband (b - 1) (by omega)).1
    (hband (b - 1) (by omega)).2 T.reaches).1
  rw [show b - 1 + 1 = b by omega, Nat.cast_sub hb] at ht
  push_cast at ht
  nlinarith [T.positive]

/-- Convert the step clock to footprint units, anchored at `p`. Above fertility
it is linear, so an overshoot still pays for the first regrowth step. -/
noncomputable def clock (x : ℝ) : ℝ :=
  if x ≤ p then p + g * (scale T.y T.t x - scale T.y T.t p) else x

lemma clock_of_top {x : ℝ} (hx : p ≤ x) : T.clock x = x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [clock]
  · rw [clock, if_neg (not_le.mpr hx)]

lemma clock_calculus {x z : ℝ} (hx : T.y 0 ≤ x) (hxz : x ≤ z) :
    0 ≤ T.clock z - T.clock x ∧ T.clock z - T.clock x ≤ z - x := by
  have hg := T.positive
  by_cases hz : z ≤ p
  · have hc := scale_calculus hg T.spaced hx hxz (hz.trans T.reaches)
    have hmul := (le_div_iff₀ hg).mp hc.2
    rw [clock, if_pos hz, clock, if_pos (hxz.trans hz)]
    constructor <;> nlinarith [hc.1]
  · by_cases hxp : x ≤ p
    · have hc := scale_calculus hg T.spaced hx hxp T.reaches
      have hmul := (le_div_iff₀ hg).mp hc.2
      rw [clock, if_neg hz, clock, if_pos hxp]
      constructor <;> nlinarith [hc.1]
    · rw [clock, if_neg hz, clock, if_neg hxp]
      exact ⟨sub_nonneg.mpr hxz, le_rfl⟩

lemma le_clock {x : ℝ} (hx : T.y 0 ≤ x) : x ≤ T.clock x := by
  by_cases hxp : x ≤ p
  · have h := (T.clock_calculus hx hxp).2
    rw [T.clock_of_top le_rfl] at h
    linarith
  · rw [T.clock_of_top (le_of_not_ge hxp)]

lemma clock_le {x z : ℝ} (hx : T.y 0 ≤ x) (hxz : x ≤ z) (hz : p ≤ z) :
    T.clock x ≤ z := by
  have h := (T.clock_calculus hx hxz).1
  rw [T.clock_of_top hz] at h
  linarith

lemma clock_sub {x z r : ℝ} (hx : T.y 0 ≤ x) (hz : T.y 0 ≤ z)
    (hr : 0 ≤ r) (h : x - r ≤ z) : T.clock x - r ≤ T.clock z := by
  rcases le_total x z with hxz | hzx
  · have hc := (T.clock_calculus hx hxz).1; linarith
  · have hc := (T.clock_calculus hz hzx).2; linarith

/-- Concavity turns a free expansion into at least one clock step. -/
lemma clock_free {x : ℝ} (hx : x ∈ Icc (T.y 0) p) (hFx : x ≤ F x) :
    T.clock x + g ≤ T.clock (F x) := by
  by_cases htop : F x ≤ p
  · have hp := T.progress hx ⟨hx.1.trans hFx, htop⟩ le_rfl
    rw [clock, if_pos hx.2, clock, if_pos htop]
    nlinarith
  · have hp := T.progress hx ⟨hx.1.trans hx.2, le_rfl⟩ (le_of_not_ge htop)
    rw [clock, if_pos hx.2, T.clock_of_top (le_of_not_ge htop)]
    nlinarith

end Trajectory

/-- Build the clock from a concave expansion profile and its first crossing.
The finite trajectory hypotheses only specify the free stopping time. -/
noncomputable def ofFunction (F : ℝ → ℝ) (a p g : ℝ) (t : ℕ)
    (hg : 0 < g) (ha : a < p)
    (hgain : ∀ x ∈ Icc a p, x + g ≤ F x)
    (hfirst : ∀ i < t, F^[i] a < p) (hreach : p ≤ F^[t] a)
    (htop : F p = p + g) (hconc : ConcaveOn ℝ (Icc a p) F) :
    Trajectory F p g := by
  have ht : 0 < t := by
    by_contra hn
    have he : t = 0 := by omega
    subst t
    simpa using (not_le.mpr ha) hreach
  have hlow : ∀ i ≤ t, a ≤ F^[i] a := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hlo := ih (by omega)
      have hs := hgain (F^[i] a) ⟨hlo, (hfirst i (by omega)).le⟩
      rw [Function.iterate_succ_apply']
      linarith
  refine {
    y := fun i => F^[i] a
    t := t
    positive := hg
    time_pos := ht
    below := hfirst
    reaches := hreach
    at_top := htop
    concave := hconc
    next := ?_
    spaced := ?_ }
  · intro i hi
    have hs := hgain (F^[i] a) ⟨hlow i (by omega), (hfirst i hi).le⟩
    dsimp only
    rw [Function.iterate_succ_apply']
    linarith
  · intro i _
    exact (Function.iterate_succ_apply' F i a).symm

/-- Concavity reduces the gain condition throughout the band to its endpoints. -/
theorem gain_on_band {β : ℝ → ℝ} {a p δ g : ℝ}
    (hc : ConcaveOn ℝ (Icc a p) β)
    (ha : a + g ≤ β a - δ) (hp : p + g ≤ β p - δ)
    {x : ℝ} (hx : x ∈ Icc a p) : x + g ≤ β x - δ := by
  have hgain : ConcaveOn ℝ (Icc a p) (fun v => β v - v - δ) := by
    convert (hc.sub (convexOn_id (convex_Icc a p))).add_const (-δ) using 1 <;> rfl
  have hlow : g ≤ min (β a - a - δ) (β p - p - δ) := le_min (by linarith) (by linarith)
  have h := hgain.ge_on_segment ⟨le_rfl, hx.1.trans hx.2⟩
    ⟨hx.1.trans hx.2, le_rfl⟩
    (show x ∈ segment ℝ a p by rw [segment_eq_Icc (hx.1.trans hx.2)]; exact hx)
  exact (by linarith : x + g ≤ β x - δ)

/-- With the trajectory anchored at the seed, the general delay bound implies
`(b-t-1)g`. For a different floor, the scale difference must be retained. -/
theorem Trajectory.seeded_delay_bound {F : ℝ → ℝ} {p g : ℝ}
    (T : Trajectory F p g) {b : ℕ} (hb : 1 ≤ b) (f r : ℕ → ℝ)
    (hseed : f 0 = T.y 0) (hband : ∀ i < b, f i ∈ Icc (T.y 0) p)
    (hr : ∀ i, 0 ≤ r i)
    (hstep : ∀ i, i + 1 < b → f (i + 1) = F (f i) - r (i + 1)) :
    ((b : ℝ) - (T.t : ℝ) - 1) * g ≤ ∑ i ∈ Finset.range b, r i := by
  have h := T.delay_bound hb f r hband hr hstep
  rw [hseed, scale_zero T.positive T.spaced] at h
  have hm := (scale_calculus T.positive T.spaced
    (T.below 0 T.time_pos).le T.reaches le_rfl).1
  rw [scale_last T.positive T.spaced] at hm
  nlinarith [T.positive]

end ProofOfSpace.Delay

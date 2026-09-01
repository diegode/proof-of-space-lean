import ProofOfSpace.ChungCurve

/-!
# Finite-size Chung thresholds

Reyzin's finite-size construction does not use the asymptotic level `E = 0`.
For a failure exponent `ε > 0` it uses the smaller threshold cut out by

  `E d x y = -ε`,

and `shiftedBeta d ε x` is its root.  The level `ε` is a *parameter* here, not a
constant, and that matters: `shiftedSec_left` gives `E(x,x) + ε = (2 - d) H(x) + ε`, so
the root exists exactly when `ε < (d - 2) H(x)`.  A fixed `ε` therefore fails near the
endpoints, where `H(x) → 0`.  `ChungRelative.lean` instantiates `ε` at a level
proportional to `H(x)` instead, for which that side condition is automatic on all of
`(0,1)` — which is what lets the statement's failure profile be uniform in the layer
width.
-/

namespace ProofOfSpace
namespace ChungCurve

open Real Set

/-- The shifted section whose zero is the finite-size Chung threshold. -/
noncomputable def shiftedSec (d ε x y : ℝ) : ℝ := sec d x y + ε

theorem shiftedSec_left (d ε x : ℝ) :
    shiftedSec d ε x x = (2 - d) * binEntropy x + ε := by
  simp only [shiftedSec, sec_left]

theorem shiftedSec_right {d ε x : ℝ} (hx : x < 1) :
    shiftedSec d ε x 1 = binEntropy x + ε := by
  simp only [shiftedSec, sec_right hx]

theorem continuous_shiftedSec (d ε x : ℝ) :
    Continuous (fun y => shiftedSec d ε x y) :=
  (continuous_sec d x).add continuous_const

theorem strictConcaveOn_shiftedSec {d ε x : ℝ} (hd : 1 ≤ d)
    (hx : 0 < x) (hx1 : x < 1) :
    StrictConcaveOn ℝ (Icc x 1) (fun y => shiftedSec d ε x y) := by
  change StrictConcaveOn ℝ (Icc x 1) ((fun y => sec d x y) + fun _ => ε)
  exact (strictConcaveOn_sec hd hx hx1).add_const ε

theorem shiftedSec_left_neg {d ε x : ℝ} (_hd : 2 < d)
    (hlevel : ε < (d - 2) * binEntropy x) : shiftedSec d ε x x < 0 := by
  rw [shiftedSec_left]
  nlinarith

theorem shiftedSec_right_pos {d ε x : ℝ} (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) : 0 < shiftedSec d ε x 1 := by
  rw [shiftedSec_right hx1]
  exact add_pos_of_pos_of_nonneg (binEntropy_pos hx hx1) hε

/-- A negative shifted section at any interior point forces the finite-size level to
lie below its admissible endpoint value `(d - 2) H(x)`. This is the side condition
used in Reyzin's simplified expansion union bound. -/
theorem level_lt_of_shiftedSec_neg {d ε x y : ℝ} (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hxy : x < y) (hy : y < 1)
    (hneg : shiftedSec d ε x y < 0) :
    ε < (d - 2) * binEntropy x := by
  by_contra hlevel
  push Not at hlevel
  have hleft : 0 ≤ shiftedSec d ε x x := by
    rw [shiftedSec_left]
    linarith
  have hright : 0 ≤ shiftedSec d ε x 1 :=
    (shiftedSec_right_pos hε hx (hxy.trans hy)).le
  have hconc := (strictConcaveOn_shiftedSec (d := d) (ε := ε) hd hx
    (hxy.trans hy)).concaveOn
  have hxmem : x ∈ Icc x 1 := ⟨le_rfl, (hxy.trans hy).le⟩
  have h1mem : (1 : ℝ) ∈ Icc x 1 := ⟨(hxy.trans hy).le, le_rfl⟩
  have hden : (0 : ℝ) < 1 - x := by linarith
  have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt hden
  have ha : 0 ≤ (1 - y) / (1 - x) := by positivity
  have hb : 0 ≤ (y - x) / (1 - x) := by positivity
  have hab : (1 - y) / (1 - x) + (y - x) / (1 - x) = 1 := by
    field_simp
    ring
  have hc := hconc.2 hxmem h1mem ha hb hab
  simp only [smul_eq_mul] at hc
  have hcomb : (1 - y) / (1 - x) * x + (y - x) / (1 - x) * 1 = y := by
    rw [show (1 - y) / (1 - x) * x + (y - x) / (1 - x) * 1 =
      ((1 - y) * x + (y - x)) / (1 - x) by ring, div_eq_iff hne]
    ring
  rw [hcomb] at hc
  nlinarith

theorem exists_shifted_root {d ε x : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hlevel : ε < (d - 2) * binEntropy x) :
    ∃ r ∈ Ioo x 1, shiftedSec d ε x r = 0 := by
  have hmem : (0 : ℝ) ∈ Ioo (shiftedSec d ε x x) (shiftedSec d ε x 1) :=
    ⟨shiftedSec_left_neg hd hlevel, shiftedSec_right_pos hε hx hx1⟩
  obtain ⟨r, hr, hval⟩ :=
    intermediate_value_Ioo hx1.le (continuous_shiftedSec d ε x).continuousOn hmem
  exact ⟨r, hr, hval⟩

theorem shiftedSec_pos_of_root_lt {d ε x r y : ℝ} (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hr : r ∈ Ioo x 1)
    (hroot : shiftedSec d ε x r = 0) (hy : y ∈ Ioo r 1) :
    0 < shiftedSec d ε x y := by
  have hconc := strictConcaveOn_shiftedSec (d := d) (ε := ε) hd hx hx1
  have hrmem : r ∈ Icc x 1 := ⟨hr.1.le, hr.2.le⟩
  have h1mem : (1 : ℝ) ∈ Icc x 1 := ⟨hx1.le, le_rfl⟩
  have hden : (0 : ℝ) < 1 - r := by linarith [hr.2]
  have hne : (1 : ℝ) - r ≠ 0 := ne_of_gt hden
  have hapos : 0 < (1 - y) / (1 - r) := div_pos (by linarith [hy.2]) hden
  have hbpos : 0 < (y - r) / (1 - r) := div_pos (by linarith [hy.1]) hden
  have hab : (1 - y) / (1 - r) + (y - r) / (1 - r) = 1 := by
    field_simp
    ring
  have hstrict := hconc.2 hrmem h1mem (ne_of_lt hr.2) hapos hbpos hab
  simp only [smul_eq_mul] at hstrict
  have hcomb : (1 - y) / (1 - r) * r + (y - r) / (1 - r) * 1 = y := by
    rw [show (1 - y) / (1 - r) * r + (y - r) / (1 - r) * 1 =
      ((1 - y) * r + (y - r)) / (1 - r) by ring, div_eq_iff hne]
    ring
  rw [hcomb, hroot] at hstrict
  nlinarith [shiftedSec_right_pos (d := d) hε hx hx1]

theorem shiftedSec_neg_of_lt_root {d ε x r y : ℝ} (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hr : r ∈ Ioo x 1)
    (hroot : shiftedSec d ε x r = 0) (hy : y ∈ Ioo x r) :
    shiftedSec d ε x y < 0 := by
  by_contra hcon
  push Not at hcon
  have hconc := strictConcaveOn_shiftedSec (d := d) (ε := ε) hd hx hx1
  have hylt1 : y < 1 := hy.2.trans hr.2
  have hymem : y ∈ Icc x 1 := ⟨hy.1.le, hylt1.le⟩
  have h1mem : (1 : ℝ) ∈ Icc x 1 := ⟨hx1.le, le_rfl⟩
  have hden : (0 : ℝ) < 1 - y := by linarith
  have hne : (1 : ℝ) - y ≠ 0 := ne_of_gt hden
  have hapos : 0 < (1 - r) / (1 - y) := div_pos (by linarith [hr.2]) hden
  have hbpos : 0 < (r - y) / (1 - y) := div_pos (by linarith [hy.2]) hden
  have hab : (1 - r) / (1 - y) + (r - y) / (1 - y) = 1 := by
    field_simp
    ring
  have hstrict := hconc.2 hymem h1mem (ne_of_lt hylt1) hapos hbpos hab
  simp only [smul_eq_mul] at hstrict
  have hcomb : (1 - r) / (1 - y) * y + (r - y) / (1 - y) * 1 = r := by
    rw [show (1 - r) / (1 - y) * y + (r - y) / (1 - y) * 1 =
      ((1 - r) * y + (r - y)) / (1 - y) by ring, div_eq_iff hne]
    ring
  rw [hcomb, hroot] at hstrict
  nlinarith [shiftedSec_right_pos (d := d) hε hx hx1]

/-- The finite-size Chung threshold.  It has the intended root characterization
when `ε < (d-2) H(x)`; outside that range the defining set may be empty. -/
noncomputable def shiftedBeta (d ε x : ℝ) : ℝ :=
  sSup {y | y ∈ Ioo x 1 ∧ shiftedSec d ε x y < 0}

theorem shiftedBeta_eq_root {d ε x r : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hr : r ∈ Ioo x 1)
    (hroot : shiftedSec d ε x r = 0) : shiftedBeta d ε x = r := by
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hset : {y | y ∈ Ioo x 1 ∧ shiftedSec d ε x y < 0} = Ioo x r := by
    ext y
    constructor
    · rintro ⟨hy, hneg⟩
      refine ⟨hy.1, ?_⟩
      by_contra hcon
      push Not at hcon
      rcases eq_or_lt_of_le hcon with heq | hlt
      · rw [heq] at hroot
        linarith
      · linarith [shiftedSec_pos_of_root_lt hd1 hε hx hx1 hr hroot ⟨hlt, hy.2⟩]
    · intro hy
      exact ⟨⟨hy.1, hy.2.trans hr.2⟩,
        shiftedSec_neg_of_lt_root hd1 hε hx hx1 hr hroot hy⟩
  rw [shiftedBeta, hset, csSup_Ioo hr.1]
theorem shiftedSec_neg_iff {d ε x y : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hlevel : ε < (d - 2) * binEntropy x)
    (hxy : x < y) (hy : y < 1) :
    shiftedSec d ε x y < 0 ↔ y < shiftedBeta d ε x := by
  obtain ⟨r, hr, hroot⟩ := exists_shifted_root hd hε hx hx1 hlevel
  have hd1 : (1 : ℝ) ≤ d := by linarith
  rw [shiftedBeta_eq_root hd hε hx hx1 hr hroot]
  constructor
  · intro hneg
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq] at hroot
      linarith
    · linarith [shiftedSec_pos_of_root_lt hd1 hε hx hx1 hr hroot ⟨hlt, hy⟩]
  · intro hlt
    exact shiftedSec_neg_of_lt_root hd1 hε hx hx1 hr hroot ⟨hxy, hlt⟩
theorem shiftedSec_symm {d ε x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    shiftedSec d ε (1 - y) (1 - x) = shiftedSec d ε x y := by
  simp only [shiftedSec]
  rw [← chungExponent_eq_sec hx hxy hy,
    ← chungExponent_eq_sec (by linarith) (by linarith) (by linarith),
    chungExponent_symm hx hxy hy]
end ChungCurve
end ProofOfSpace

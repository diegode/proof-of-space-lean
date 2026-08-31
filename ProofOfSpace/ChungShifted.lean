import ProofOfSpace.ChungCurve

/-!
# Finite-size Chung thresholds

Reyzin's finite-size construction does not use the asymptotic level `E = 0`.
For a failure exponent `ε > 0` it uses the smaller threshold cut out by

  `E d x y = -ε`.

This file constructs that threshold wherever the diagonal value is below `-ε`.
The extra hypothesis `ε < (d - 2) * H(x)` is necessary: without it the certified
sublevel set can be empty near the endpoints.  This endpoint obstruction is why the
raw shifted threshold cannot simply replace the closed zero-level profile globally.
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

/-- At `ε = 0` the finite-size threshold is the asymptotic one of `ChungCurve.lean`.
The two constructions therefore agree exactly where the shift vanishes, and the whole
finite-size theory is a deformation of the zero-level curve. -/
theorem shiftedBeta_zero (d x : ℝ) : shiftedBeta d 0 x = chungBeta d x := by
  have h : ∀ y : ℝ, shiftedSec d 0 x y = sec d x y := by
    intro y
    simp [shiftedSec]
  simp only [shiftedBeta, chungBeta, h]

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

theorem shiftedBeta_mem {d ε x : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hlevel : ε < (d - 2) * binEntropy x) :
    shiftedBeta d ε x ∈ Ioo x 1 := by
  obtain ⟨r, hr, hroot⟩ := exists_shifted_root hd hε hx hx1 hlevel
  rw [shiftedBeta_eq_root hd hε hx hx1 hr hroot]
  exact hr

theorem shiftedSec_shiftedBeta {d ε x : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hlevel : ε < (d - 2) * binEntropy x) :
    shiftedSec d ε x (shiftedBeta d ε x) = 0 := by
  obtain ⟨r, hr, hroot⟩ := exists_shifted_root hd hε hx hx1 hlevel
  rw [shiftedBeta_eq_root hd hε hx hx1 hr hroot]
  exact hroot

theorem shiftedSec_symm {d ε x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    shiftedSec d ε (1 - y) (1 - x) = shiftedSec d ε x y := by
  simp only [shiftedSec]
  rw [← chungExponent_eq_sec hx hxy hy,
    ← chungExponent_eq_sec (by linarith) (by linarith) (by linarith),
    chungExponent_symm hx hxy hy]

theorem shiftedBeta_reversal {d ε x : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : 0 < x) (hx1 : x < 1) (hlevel : ε < (d - 2) * binEntropy x) :
    shiftedBeta d ε (1 - shiftedBeta d ε x) = 1 - x := by
  have hβ := shiftedBeta_mem hd hε hx hx1 hlevel
  have hm0 : 0 < 1 - shiftedBeta d ε x := by linarith [hβ.2]
  have hm1 : 1 - shiftedBeta d ε x < 1 := by linarith [hβ.1]
  have hr : 1 - x ∈ Ioo (1 - shiftedBeta d ε x) 1 :=
    ⟨by linarith [hβ.1], by linarith⟩
  apply shiftedBeta_eq_root hd hε hm0 hm1 hr
  rw [shiftedSec_symm hx hβ.1 hβ.2]
  exact shiftedSec_shiftedBeta hd hε hx hx1 hlevel

/-- The shifted threshold is strictly increasing wherever the shifted root exists,
provided it also exists at the reflected source used by the symmetry argument. -/
theorem shiftedBeta_lt_shiftedBeta {d ε x y : ℝ} (hd : 2 < d) (hε : 0 ≤ ε)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (hxy : x < y)
    (hxlevel : ε < (d - 2) * binEntropy x)
    (hylevel : ε < (d - 2) * binEntropy y)
    (hmlevel : ε < (d - 2) * binEntropy (1 - shiftedBeta d ε x)) :
    shiftedBeta d ε x < shiftedBeta d ε y := by
  have hβx := shiftedBeta_mem hd hε hx.1 hx.2 hxlevel
  have hβy := shiftedBeta_mem hd hε hy.1 hy.2 hylevel
  by_cases hle : shiftedBeta d ε x ≤ y
  · exact hle.trans_lt hβy.1
  · have hyβ : y < shiftedBeta d ε x := lt_of_not_ge hle
    have hm0 : 0 < 1 - shiftedBeta d ε x := by linarith [hβx.2]
    have hm1 : 1 - shiftedBeta d ε x < 1 := by linarith [hx.1, hβx.1]
    have hmt : 1 - shiftedBeta d ε x < 1 - y := by linarith
    have ht1 : 1 - y < 1 := by linarith [hy.1]
    have hroot : shiftedBeta d ε (1 - shiftedBeta d ε x) = 1 - x :=
      shiftedBeta_reversal hd hε hx.1 hx.2 hxlevel
    have hnegMirror : shiftedSec d ε (1 - shiftedBeta d ε x) (1 - y) < 0 :=
      (shiftedSec_neg_iff hd hε hm0 hm1 hmlevel hmt ht1).2 (by rw [hroot]; linarith)
    have hneg : shiftedSec d ε y (shiftedBeta d ε x) < 0 := by
      calc
        shiftedSec d ε y (shiftedBeta d ε x) =
            shiftedSec d ε (1 - shiftedBeta d ε x) (1 - y) :=
          (shiftedSec_symm hy.1 hyβ hβx.2).symm
        _ < 0 := hnegMirror
    exact (shiftedSec_neg_iff hd hε hy.1 hy.2 hylevel hyβ hβx.2).1 hneg

end ChungCurve
end ProofOfSpace

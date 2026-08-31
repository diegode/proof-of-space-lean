import ProofOfSpace.ChungNumerics

/-!
# The Filecoin polygon lies inside the finite-size Chung region

`ChungNumerics.lean` certifies the eleven non-endpoint *vertices* of `filecoinBeta`
against `E₈(x,y) < -2⁻²²`.  Vertices alone say nothing about the segments between them:
that step needs the region to be convex, i.e. the exact threshold to be concave, which
is not proved anywhere and is not needed.  `ChungChord.lean` supplies the cheaper
argument — along a straight chord the restricted exponent is strictly convex wherever an
explicit *rational* function is positive, so it is bounded by its endpoint values — and
this file runs it on all twelve segments.

The result is `filecoinBeta_shiftedSec_neg`: on `[2⁻²⁵, 1 - 2⁻²³]` the whole polygon,
not merely its vertices, satisfies `E₈(x, β x) < -2⁻²²`, and therefore lies strictly
below the exact finite-size threshold `shiftedBeta 8 2⁻²²`.

**The range is not an artifact.**  `shiftedSec_left` forces
`E_d(x,x) = (2-d) H(x) > -ε` once `H(x)` is small enough, so the certified region is
*empty* near `0` and `1` and no profile with `β x > x` can lie inside it there.
`filecoinBeta_outside_region_near_zero` records that obstruction, and
`filecoin_region_empty_below` locates it: everything below `x ≈ 1.9·10⁻⁹` is
uncertifiable at this level, whatever profile is used.
-/

namespace ProofOfSpace
namespace ChungCurve

open Real Set

private theorem cert_of {ε a y z : ℝ} (h : z = y) (hc : shiftedSec 8 ε a y < 0) :
    shiftedSec 8 ε a z < 0 := by rw [h]; exact hc

/-! ### The opening segment, a chord through the origin -/

theorem filecoin_region_0 {x : ℝ} (h0 : 1 / 2 ^ 25 ≤ x) (h1 : x ≤ 5089 / 100000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_0 (by norm_num at h0 ⊢; linarith) h1]
  refine shiftedSec_neg_on_chord (a := 1 / 2 ^ 25) (b := 5089 / 100000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    norm_num at ht0
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    norm_num at ht0
    have hx0 : (0 : ℝ) < t := by linarith
    have h1x : (0 : ℝ) < 1 - t := by linarith
    have h1y : (0 : ℝ) < 1 - 20000 / 5089 * t := by linarith
    rw [chordSec''_ray_eq (ne_of_gt hx0) (by norm_num) (by norm_num)
      (ne_of_gt h1x) (ne_of_gt h1y)]
    have b1 : (8 - 1 - 20000 / 5089 : ℝ) / (5089 / 100000)
        ≤ (8 - 1 - 20000 / 5089) / t :=
      div_le_div_of_nonneg_left (by norm_num) hx0 (by linarith)
    have b2 : (8 - 1 : ℝ) / 1 ≤ (8 - 1) / (1 - t) :=
      div_le_div_of_nonneg_left (by norm_num) h1x (by linarith)
    have b3 : ((20000 / 5089 : ℝ)) ^ 2 / (1 - 20000 / 5089 * t)
        ≤ ((20000 / 5089 : ℝ)) ^ 2 / (1 - 20000 / 5089 * (5089 / 100000)) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have n1 : (8 - 1 - 20000 / 5089 : ℝ) / (5089 / 100000) = 1562300000 / 25897921 := by
      norm_num
    have n3 : ((20000 / 5089 : ℝ)) ^ 2 / (1 - 20000 / 5089 * (5089 / 100000))
        = 500000000 / 25897921 := by norm_num
    rw [n1] at b1
    rw [n3] at b3
    linarith
  · exact cert_of (by norm_num) shiftedSec_neg_ray_2_25
  · exact cert_of (by norm_num) shiftedSec_neg_05089_vertex

/-! ### The ten interior segments -/

theorem filecoin_region_1 {x : ℝ} (h0 : 5089 / 100000 ≤ x) (h1 : x ≤ 46 / 625) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_1 h0 h1]
  refine shiftedSec_neg_on_chord (a := 5089 / 100000) (b := 46 / 625)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 5089 / 100000) (v := 1331 / 5000) (w := 14911 / 100000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_05089_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_0736_vertex

theorem filecoin_region_2 {x : ℝ} (h0 : 46 / 625 ≤ x) (h1 : x ≤ 74 / 625) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_2 h0 h1]
  refine shiftedSec_neg_on_chord (a := 46 / 625) (b := 74 / 625)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 46 / 625) (v := 3031 / 8000) (w := 963 / 5000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_0736_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_1184_vertex

theorem filecoin_region_3 {x : ℝ} (h0 : 74 / 625 ≤ x) (h1 : x ≤ 811 / 5000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_3 h0 h1]
  refine shiftedSec_neg_on_chord (a := 74 / 625) (b := 811 / 5000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 74 / 625) (v := 4663 / 10000) (w := 10419 / 40000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_1184_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_1622_vertex

theorem filecoin_region_4 {x : ℝ} (h0 : 811 / 5000 ≤ x) (h1 : x ≤ 571 / 2500) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_4 h0 h1]
  refine shiftedSec_neg_on_chord (a := 811 / 5000) (b := 571 / 2500)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 811 / 5000) (v := 1143 / 2000) (w := 3041 / 10000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_1622_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_2284_vertex

theorem filecoin_region_5 {x : ℝ} (h0 : 571 / 2500 ≤ x) (h1 : x ≤ 3201 / 10000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_5 h0 h1]
  refine shiftedSec_neg_on_chord (a := 571 / 2500) (b := 3201 / 10000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 571 / 2500) (v := 6799 / 10000) (w := 3431 / 10000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_2284_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_center_vertex

theorem filecoin_region_6 {x : ℝ} (h0 : 3201 / 10000 ≤ x) (h1 : x ≤ 857 / 2000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_6 h0 h1]
  refine shiftedSec_neg_on_chord (a := 3201 / 10000) (b := 857 / 2000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 3201 / 10000) (v := 1929 / 2500) (w := 3431 / 10000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_center_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_4285_vertex

theorem filecoin_region_7 {x : ℝ} (h0 : 857 / 2000 ≤ x) (h1 : x ≤ 5337 / 10000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_7 h0 h1]
  refine shiftedSec_neg_on_chord (a := 857 / 2000) (b := 5337 / 10000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 857 / 2000) (v := 4189 / 5000) (w := 3041 / 10000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_4285_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_5337_vertex

theorem filecoin_region_8 {x : ℝ} (h0 : 5337 / 10000 ≤ x) (h1 : x ≤ 4969 / 8000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_8 h0 h1]
  refine shiftedSec_neg_on_chord (a := 5337 / 10000) (b := 4969 / 8000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 5337 / 10000) (v := 551 / 625) (w := 10419 / 40000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_5337_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_621125_vertex

theorem filecoin_region_9 {x : ℝ} (h0 : 4969 / 8000 ≤ x) (h1 : x ≤ 3669 / 5000) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_9 h0 h1]
  refine shiftedSec_neg_on_chord (a := 4969 / 8000) (b := 3669 / 5000)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 4969 / 8000) (v := 579 / 625) (w := 963 / 5000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_621125_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_7338_vertex

theorem filecoin_region_10 {x : ℝ} (h0 : 3669 / 5000 ≤ x) (h1 : x ≤ 4 / 5) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_10 h0 h1]
  refine shiftedSec_neg_on_chord (a := 3669 / 5000) (b := 4 / 5)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    exact chordSec''_pos (u := 3669 / 5000) (v := 94911 / 100000) (w := 14911 / 100000)
      (by norm_num) (by norm_num)
      ht0.le (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  · exact cert_of (by norm_num) shiftedSec_neg_7338_vertex
  · exact cert_of (by norm_num) shiftedSec_neg_08_vertex

/-! ### The closing segment, a chord into the corner `(1,1)`

Its far endpoint is the anti-diagonal reflection of a point of the opening segment, so
the corner certificate `shiftedSec_neg_ray_2_25` serves at both ends of the polygon. -/

theorem shiftedSec_neg_top_right :
    shiftedSec 8 filecoinEpsilon (1 - 1 / 2 ^ 23)
      (5089 / 20000 * (1 - 1 / 2 ^ 23) + (1 - 5089 / 20000)) < 0 := by
  have key := filecoin_region_0 (x := 5089 / (20000 * 2 ^ 23)) (by norm_num) (by norm_num)
  rw [filecoinBeta_affine_0 (by norm_num) (by norm_num),
    show (20000 / 5089 : ℝ) * (5089 / (20000 * 2 ^ 23)) + 0 = 1 / 2 ^ 23 by norm_num] at key
  have hsym := shiftedSec_symm (d := 8) (ε := filecoinEpsilon)
    (x := (5089 / (20000 * 2 ^ 23) : ℝ)) (y := (1 / 2 ^ 23 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [show (5089 / 20000 : ℝ) * (1 - 1 / 2 ^ 23) + (1 - 5089 / 20000)
      = 1 - 5089 / (20000 * 2 ^ 23) by ring, hsym]
  exact key

theorem filecoin_region_11 {x : ℝ} (h0 : 4 / 5 ≤ x) (h1 : x ≤ 1 - 1 / 2 ^ 23) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rw [filecoinBeta_affine_11 h0 (by norm_num at h1 ⊢; linarith),
    show (14911 / 20000 : ℝ) = 1 - 5089 / 20000 by norm_num]
  refine shiftedSec_neg_on_chord (a := 4 / 5) (b := 1 - 1 / 2 ^ 23)
    (by norm_num) ?_ ?_ ?_ ?_ ⟨h0, h1⟩
  · rintro t ⟨ht0, ht1⟩
    norm_num at ht1
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro t ⟨ht0, ht1⟩
    norm_num at ht1
    have hx0 : (0 : ℝ) < t := by linarith
    have h1x : (0 : ℝ) < 1 - t := by linarith
    have hy : (0 : ℝ) < 5089 / 20000 * t + (1 - 5089 / 20000) := by linarith
    rw [chordSec''_top_eq (ne_of_gt hx0) (by norm_num) (by norm_num)
      (ne_of_gt h1x) (ne_of_gt hy)]
    have b1 : (1 : ℝ) / t ≤ 1 / (4 / 5) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have b2 : ((8 - 1 : ℝ) * (5089 / 20000) - 1) / (1 / 5)
        ≤ ((8 - 1 : ℝ) * (5089 / 20000) - 1) / (1 - t) :=
      div_le_div_of_nonneg_left (by norm_num) h1x (by linarith)
    have b3 : (8 - 1 : ℝ) * (5089 / 20000) ^ 2 / 1
        ≤ (8 - 1 : ℝ) * (5089 / 20000) ^ 2 / (5089 / 20000 * t + (1 - 5089 / 20000)) :=
      div_le_div_of_nonneg_left (by norm_num) hy (by linarith)
    norm_num at b1 b2 b3 ⊢
    linarith
  · exact cert_of (by norm_num) shiftedSec_neg_08_vertex
  · exact shiftedSec_neg_top_right

/-! ### The polygon, whole -/

/-- **The certified range.**  Every point of the Filecoin polygon between `2⁻²⁵` and
`1 - 2⁻²³` — not merely its vertices — lies strictly inside the finite-size Chung region
`E₈(x,y) < -2⁻²²`. -/
theorem filecoinBeta_shiftedSec_neg {x : ℝ} (h0 : 1 / 2 ^ 25 ≤ x)
    (h1 : x ≤ 1 - 1 / 2 ^ 23) :
    shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  rcases le_total x (5089 / 100000 : ℝ) with h | h
  · exact filecoin_region_0 h0 h
  rcases le_total x (46 / 625 : ℝ) with h' | h'
  · exact filecoin_region_1 h h'
  rcases le_total x (74 / 625 : ℝ) with h'' | h''
  · exact filecoin_region_2 h' h''
  rcases le_total x (811 / 5000 : ℝ) with h3 | h3
  · exact filecoin_region_3 h'' h3
  rcases le_total x (571 / 2500 : ℝ) with h4 | h4
  · exact filecoin_region_4 h3 h4
  rcases le_total x (3201 / 10000 : ℝ) with h5 | h5
  · exact filecoin_region_5 h4 h5
  rcases le_total x (857 / 2000 : ℝ) with h6 | h6
  · exact filecoin_region_6 h5 h6
  rcases le_total x (5337 / 10000 : ℝ) with h7 | h7
  · exact filecoin_region_7 h6 h7
  rcases le_total x (4969 / 8000 : ℝ) with h8 | h8
  · exact filecoin_region_8 h7 h8
  rcases le_total x (3669 / 5000 : ℝ) with h9 | h9
  · exact filecoin_region_9 h8 h9
  rcases le_total x (4 / 5 : ℝ) with h10 | h10
  · exact filecoin_region_10 h9 h10
  · exact filecoin_region_11 h10 h1

/-- The same statement as a comparison with the exact finite-size threshold. -/
theorem filecoinBeta_lt_shiftedBeta {x : ℝ} (h0 : 1 / 2 ^ 25 ≤ x)
    (h1 : x ≤ 1 - 1 / 2 ^ 23)
    (hlevel : filecoinEpsilon < 6 * binEntropy x) :
    filecoinBeta x < shiftedBeta 8 filecoinEpsilon x := by
  have hx0 : (0 : ℝ) < x := by norm_num at h0 ⊢; linarith
  have hx1 : x < 1 := by norm_num at h1 ⊢; linarith
  refine (shiftedSec_neg_iff (by norm_num) (by norm_num [filecoinEpsilon]) hx0 hx1
    (by norm_num; linarith [hlevel]) (filecoinBeta_expands ⟨hx0, hx1⟩)
    ?_).1 (filecoinBeta_shiftedSec_neg h0 h1)
  exact (filecoinBeta_maps ⟨hx0.le, hx1.le⟩).2.lt_of_ne (by
    intro hcon
    have := filecoinBeta_strictMono (show x < 1 from hx1)
    rw [hcon, filecoinBeta_one] at this
    exact lt_irrefl 1 this)

/-! ### Why the range stops where it does

Below the level where `(d-2) H(x)` drops under `ε` the certified region is empty, so no
expansion profile whatsoever is certifiable there at this `ε`.  This is the endpoint
obstruction of `ChungShifted.lean`, made concrete. -/

/-- Wherever `6 H(x) ≤ 2⁻²²`, *no* `y` is certified: the region degenerates. -/
theorem filecoin_region_empty_below {x y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hxy : x < y) (hy : y < 1) (hdeg : 6 * binEntropy x ≤ filecoinEpsilon) :
    ¬ shiftedSec 8 filecoinEpsilon x y < 0 := by
  intro hneg
  have hconc := strictConcaveOn_shiftedSec (d := 8) (ε := filecoinEpsilon)
    (by norm_num) hx hx1
  have hleft : ¬ shiftedSec 8 filecoinEpsilon x x < 0 := by
    rw [shiftedSec_left]
    push Not
    linarith
  have hright : 0 < shiftedSec 8 filecoinEpsilon x 1 :=
    shiftedSec_right_pos (by norm_num [filecoinEpsilon]) hx hx1
  push Not at hleft
  have hmem : x ∈ Icc x 1 := ⟨le_rfl, hx1.le⟩
  have h1mem : (1 : ℝ) ∈ Icc x 1 := ⟨hx1.le, le_rfl⟩
  have hden : (0 : ℝ) < 1 - x := by linarith
  have ha : 0 < (1 - y) / (1 - x) := div_pos (by linarith) hden
  have hb : 0 < (y - x) / (1 - x) := div_pos (by linarith) hden
  have hab : (1 - y) / (1 - x) + (y - x) / (1 - x) = 1 := by
    field_simp
    ring
  have hstrict := hconc.2 hmem h1mem (ne_of_lt hx1) ha hb hab
  simp only [smul_eq_mul] at hstrict
  have hcomb : (1 - y) / (1 - x) * x + (y - x) / (1 - x) * 1 = y := by
    field_simp
    ring
  rw [hcomb] at hstrict
  nlinarith

/-- The polygon itself is *not* certified in the degenerate zone: no profile with
`x < β x < 1` can be. -/
theorem filecoinBeta_outside_region_near_zero {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hdeg : 6 * binEntropy x ≤ filecoinEpsilon) :
    ¬ shiftedSec 8 filecoinEpsilon x (filecoinBeta x) < 0 := by
  have hexp := filecoinBeta_expands ⟨hx, hx1⟩
  have hlt : filecoinBeta x < 1 :=
    (filecoinBeta_maps ⟨hx.le, hx1.le⟩).2.lt_of_ne (by
      intro hcon
      have h := filecoinBeta_strictMono hx1
      rw [hcon, filecoinBeta_one] at h
      exact lt_irrefl 1 h)
  exact filecoin_region_empty_below hx hx1 hexp hlt hdeg

/-- And the zone is not empty: at `x = 2⁻³⁰` the level `-2⁻²²` already certifies
nothing.  So a certified range that stops short of `0` is forced, not a convenience. -/
theorem filecoin_region_degenerate_at_2_30 :
    6 * binEntropy ((1 : ℝ) / 2 ^ 30) ≤ filecoinEpsilon := by
  have hx : (0 : ℝ) < 1 / 2 ^ 30 := by norm_num
  have hlog : log ((1 : ℝ) / 2 ^ 30) = -(30 * log 2) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have htail : -((1 - (1 : ℝ) / 2 ^ 30) * log (1 - 1 / 2 ^ 30)) ≤ 1 / 2 ^ 30 :=
    neg_one_sub_mul_log_le (by norm_num)
  rw [binEntropy_eq_neg, hlog]
  simp only [filecoinEpsilon]
  nlinarith [Real.log_two_lt_d9, htail]

end ChungCurve
end ProofOfSpace

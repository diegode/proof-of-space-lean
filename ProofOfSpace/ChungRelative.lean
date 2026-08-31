import ProofOfSpace.ChungRegion

/-!
# The polygon lies inside the Chung region at a *relative* level, on all of `(0,1)`

`ChungRegion.lean` certifies the polygon against the fixed level `E₈ < -2⁻²²`, and can
only do so on `[2⁻²⁵, 1 - 2⁻²³]`.  That restriction is forced, not lazy: `E₈(x, x) =
-6 H(x)`, so a *fixed* negative level cuts out an empty region — no `y` at all is
certified — once `H(x)` drops below it.  A statement whose failure profile is defined by a
fixed level therefore cannot be uniform in the layer width: at `n ≳ 5·10⁸` the source size
`k = 1` already falls into that degenerate zone, well below Filecoin's `n ≈ 10⁹`.

The cure is to measure the level in the same units as the exponent itself.  Take

  `level(x) = H(x) / 2²³`.

Then `E₈(x, x) = -6 H(x) < -level(x)` for *every* `x ∈ (0,1)`, so the region is never
empty, and the polygon still sits strictly inside it everywhere:

* on `[2⁻²⁵, 1 - 2⁻²³]` because `level(x) ≤ log 2 / 2²³ < 2⁻²²`, so the existing fixed-level
  certificates are already strong enough;
* on `(0, 2⁻²⁵]` and `[1 - 2⁻²³, 1)` by the ray estimate `sec_ray_le` below, which is what
  the fixed level could not reach.

Both corners are the same chord seen twice: the polygon opens along `y = c x` with
`c = 20000/5089` and closes along its anti-diagonal mirror, so one ray bound serves both.
-/

namespace ProofOfSpace
namespace ChungCurve

open Real Set

/-- The opening slope of the polygon, `β(x)/x` on the first segment. -/
noncomputable def rayC : ℝ := 20000 / 5089

/-- The relative certification level.  Proportional to `H(x)`, so it vanishes at the
endpoints exactly as the exponent does. -/
noncomputable def chungLevel (x : ℝ) : ℝ := binEntropy x / 2 ^ 23

theorem chungLevel_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ chungLevel x :=
  div_nonneg (binEntropy_nonneg h0 h1) (by norm_num)

/-- **The region is never empty.**  This is the whole point of the relative level: the
side condition `ε < (d-2) H(x)` that `ChungShifted.lean` needs becomes automatic. -/
theorem chungLevel_lt_level {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    chungLevel x < 6 * binEntropy x := by
  have hH : 0 < binEntropy x := binEntropy_pos h0 h1
  rw [chungLevel]
  nlinarith

/-- The relative level never exceeds the fixed level of `ChungRegion.lean`, so every
certificate proved there is already a certificate at this level. -/
theorem chungLevel_le_filecoinEpsilon (x : ℝ) : chungLevel x ≤ filecoinEpsilon := by
  have h := binEntropy_le_log_two (p := x)
  have h2 := Real.log_two_lt_d9
  rw [chungLevel, filecoinEpsilon]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 ^ 23)]
  norm_num
  linarith

/-! ### The elementary entropy bound used at the corners -/

/-- `H(x) ≤ x (1 - log x)`.  Only the `-(1-x) log (1-x) ≤ x` half of
`neg_one_sub_mul_log_le` is doing work. -/
theorem binEntropy_le_ray {x : ℝ} (h1 : x < 1) :
    binEntropy x ≤ x * (1 - log x) := by
  have h := neg_one_sub_mul_log_le h1
  rw [binEntropy_eq_neg]
  nlinarith

/-! ### The ray estimate -/

/-- Bracket for `log (20000/5089)`, the opening slope. -/
theorem log_rayC : (1.368650905 : ℝ) < log rayC ∧ log rayC < (1.368650946 : ℝ) := by
  have h5 := log_5089_100000
  have h1 := log_1_5
  have hsplit : rayC = ((1 : ℝ)/5) / (5089 / 100000) := by
    rw [rayC]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num)]
  constructor <;> [linarith [h5.2, h1.1]; linarith [h5.1, h1.2]]

/-- Bracket for `log (14911/5089)`, the slope of the gap `y - x` along the ray. -/
theorem log_rayC_sub_one : (1.075017828 : ℝ) < log (rayC - 1) ∧
    log (rayC - 1) < (1.075017869 : ℝ) := by
  have h5 := log_5089_100000
  have h14 := log_14911_100000
  have hsplit : rayC - 1 = ((14911 : ℝ)/100000) / (5089 / 100000) := by
    rw [rayC]; norm_num
  rw [hsplit, Real.log_div (by norm_num) (by norm_num)]
  constructor <;> [linarith [h5.2, h14.1]; linarith [h5.1, h14.2]]

/-- **The ray estimate.**  Along the opening chord the exponent is bounded by an explicit
affine function of `log x`.  The `log x` coefficient `7 - c ≈ 3.07` is positive, so the
bound goes to `-∞` faster than any multiple of `H(x)`: that is what lets the corners be
certified all the way to the endpoint, which a fixed level cannot do. -/
theorem sec_ray_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hcx : rayC * x < 1) :
    sec 8 x (rayC * x) ≤ x * ((7 - rayC) * log x + 16.3833) := by
  have hc : (1 : ℝ) < rayC := by rw [rayC]; norm_num
  have hkey := shiftedSec_scaling (d := 8) (ε := 0) hx hc
  simp only [shiftedSec, add_zero] at hkey
  have h1 : (1 - x) * log (1 - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (Real.log_nonpos (by linarith) (by linarith))
  have h2 : -((1 - rayC * x) * log (1 - rayC * x)) ≤ rayC * x :=
    neg_one_sub_mul_log_le hcx
  have hlc := log_rayC
  have hlc1 := log_rayC_sub_one
  -- The scalar content: the two logarithmic constants, bracketed.
  have hscalar : 7 * rayC * log rayC - 8 * (rayC - 1) * log (rayC - 1)
      ≤ 16.3833 - rayC := by
    have hcv : rayC = 20000 / 5089 := rfl
    rw [hcv] at hlc hlc1 ⊢
    nlinarith [hlc.2, hlc1.1]
  have hmul := mul_le_mul_of_nonneg_left hscalar hx.le
  rw [hkey]
  nlinarith [hmul, h1, h2]

end ChungCurve
end ProofOfSpace

namespace ProofOfSpace
namespace ChungCurve

open Real Set

/-! ### The two corners -/

/-- `log x ≤ -8 log 2` below `2⁻⁸`, in the form the corner arithmetic wants. -/
private theorem log_le_of_le_256 {x : ℝ} (hx : 0 < x) (h : x ≤ 1 / 256) :
    log x ≤ -5.5451 := by
  have h1 : log x ≤ log (1 / 256) := Real.log_le_log hx h
  have h2 : log ((1 : ℝ) / 256) = -(8 * log 2) := by
    rw [one_div, Real.log_inv,
      show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [h2] at h1
  linarith [Real.log_two_gt_d9]

/-- **The opening corner.**  On `(0, 2⁻⁸]` the polygon runs along the ray `y = c x`, and
the ray estimate beats the relative level all the way down to `0`.  This is the range the
fixed level `2⁻²²` could not reach. -/
theorem filecoinBeta_corner_left {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 256) :
    sec 8 x (filecoinBeta x) + chungLevel x < 0 := by
  have hx1 : x < 1 := by linarith
  have hcv : rayC = 20000 / 5089 := rfl
  have hbeta : filecoinBeta x = rayC * x := by
    rw [filecoinBeta_affine_0 h0.le (by linarith), hcv]; ring
  have hcx : rayC * x < 1 := by rw [hcv]; linarith
  have hray := sec_ray_le h0 hx1 hcx
  have hent : binEntropy x ≤ x * (1 - log x) := binEntropy_le_ray hx1
  have hlog := log_le_of_le_256 h0 h1
  rw [hbeta, chungLevel]
  rw [hcv] at hray ⊢
  nlinarith [hray, hent, hlog, h0]

/-- **The closing corner.**  The polygon's last chord is the anti-diagonal mirror of its
first, so the same ray estimate certifies it, transported by `shiftedSec_symm`. -/
theorem filecoinBeta_corner_right {x : ℝ} (h0 : 1 - 1 / 128 ≤ x) (h1 : x < 1) :
    sec 8 x (filecoinBeta x) + chungLevel x < 0 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hcv : rayC = 20000 / 5089 := rfl
  have hbeta : filecoinBeta x = 5089 / 20000 * x + 14911 / 20000 :=
    filecoinBeta_affine_11 (by linarith) h1.le
  set u : ℝ := 5089 / 20000 * (1 - x) with hu
  have hu0 : 0 < u := by rw [hu]; nlinarith
  have hu256 : u ≤ 1 / 256 := by rw [hu]; nlinarith
  have hu1 : u < 1 := by linarith
  have hbu : 1 - filecoinBeta x = u := by rw [hbeta, hu]; ring
  have hray_eq : rayC * u = 1 - x := by rw [hcv, hu]; ring
  have hcu : rayC * u < 1 := by rw [hray_eq]; linarith
  -- transport along the anti-diagonal
  have hxb : x < filecoinBeta x := filecoinBeta_expands ⟨hx0, h1⟩
  have hb1 : filecoinBeta x < 1 := by
    have := filecoinBeta_strictMono h1; rwa [filecoinBeta_one] at this
  have hsymm : sec 8 u (rayC * u) = sec 8 x (filecoinBeta x) := by
    have h := shiftedSec_symm (d := 8) (ε := 0) hx0 hxb hb1
    simp only [shiftedSec, add_zero, hbu, ← hray_eq] at h
    exact h
  have hray := sec_ray_le hu0 hu1 hcu
  -- the level, measured at `x`, is the level at `1 - x = c u`
  have hlevel : chungLevel x = binEntropy (rayC * u) / 2 ^ 23 := by
    rw [chungLevel, hray_eq, ← binEntropy_one_sub x]
  have hent : binEntropy (rayC * u) ≤ rayC * u * (1 - log (rayC * u)) :=
    binEntropy_le_ray hcu
  have hlogc := log_rayC
  have hlogmul : log (rayC * u) = log rayC + log u := by
    rw [hcv]; exact Real.log_mul (by norm_num) (ne_of_gt hu0)
  have hlogu := log_le_of_le_256 hu0 hu256
  rw [← hsymm, hlevel]
  rw [hlogmul] at hent
  rw [hcv] at hray hent hlogc ⊢
  nlinarith [hray, hent, hlogu, hu0, hlogc.1, hlogc.2]

/-! ### The polygon is inside the relative region on the whole open interval -/

/-- **The certificate, on all of `(0,1)`.**  Every point of the polygon satisfies
`E₈(x, β x) < -H(x)/2²³`.  Unlike `filecoinBeta_shiftedSec_neg`, this has no range
restriction: the relative level is what removes it. -/
theorem filecoinBeta_sec_lt_level {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    sec 8 x (filecoinBeta x) + chungLevel x < 0 := by
  rcases le_or_gt x (1 / 256 : ℝ) with hl | hl
  · exact filecoinBeta_corner_left h0 hl
  rcases le_or_gt (1 - 1 / 128 : ℝ) x with hr | hr
  · exact filecoinBeta_corner_right hr h1
  -- the middle is already covered by the fixed-level certificate
  have hmid := filecoinBeta_shiftedSec_neg (x := x) (by norm_num; linarith)
    (by norm_num; linarith)
  simp only [shiftedSec] at hmid
  linarith [chungLevel_le_filecoinEpsilon x]

/-- **The polygon lies strictly below the Chung threshold at the relative level**, for
every `x ∈ (0,1)`.  This is the bridge the statement file consumes: the profile it defines
from the exponent alone is at least the expansion the deterministic argument needs. -/
theorem filecoinBeta_lt_shiftedBeta_level {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    filecoinBeta x < shiftedBeta 8 (chungLevel x) x := by
  have hxb : x < filecoinBeta x := filecoinBeta_expands ⟨h0, h1⟩
  have hb1 : filecoinBeta x < 1 := by
    have := filecoinBeta_strictMono h1; rwa [filecoinBeta_one] at this
  refine (shiftedSec_neg_iff (by norm_num)
    (chungLevel_nonneg h0.le h1.le) h0 h1 ?_ hxb hb1).1 ?_
  · have := chungLevel_lt_level h0 h1; norm_num; linarith
  · simpa only [shiftedSec] using filecoinBeta_sec_lt_level h0 h1

end ChungCurve
end ProofOfSpace

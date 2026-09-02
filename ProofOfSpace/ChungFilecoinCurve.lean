import ProofOfSpace.ChungShifted
import Mathlib.Analysis.Convex.Function

/-!
# The rational Chung-8 profile

The probabilistic theorem uses the rational polygon below as its exact finite expansion
requirement. Its right half is the anti-diagonal reflection of its left half, so it
satisfies the reversal identity exactly rather than to numerical tolerance.

The polygon is not a posited profile. `ChungRegion.lean` proves that the whole of it —
not merely its vertices — lies strictly inside the finite-size Chung region
`E₈(x, y) < -2⁻²²` on `[2⁻²⁵, 1 - 2⁻²³]`, so the expansion it demands is the expansion
Reyzin's own union-bound exponent certifies.  The polygon is used in place of the exact
shifted root because that root is not defined near `0` and `1`, where its sublevel set
is empty, and because concavity and the unique gain maximizer are free for a minimum of
affine functions and unproved for the root.

Writing the polygon as the minimum of its supporting affine lines makes its global
concavity a short theorem.  The strictly decreasing positive slopes give strict
monotonicity and a unique gain maximizer, all without analytic hypotheses.
-/

namespace ProofOfSpace
namespace ChungCurve

open Set

/-- The finite-size failure exponent used in the Filecoin calculation. -/
noncomputable def filecoinEpsilon : ℝ := 1 / 2 ^ (22 : ℕ)

/-- The affine line through `(a,u)` and `(b,v)`. -/
noncomputable def chord (a u b v x : ℝ) : ℝ := u + (v - u) / (b - a) * (x - a)

private noncomputable def L0 (x : ℝ) :=
  chord 0 0 (5089 / 100000) (1 / 5) x
private noncomputable def L1 (x : ℝ) :=
  chord (5089 / 100000) (1 / 5) (46 / 625) (1331 / 5000) x
private noncomputable def L2 (x : ℝ) :=
  chord (46 / 625) (1331 / 5000) (74 / 625) (3031 / 8000) x
private noncomputable def L3 (x : ℝ) :=
  chord (74 / 625) (3031 / 8000) (811 / 5000) (4663 / 10000) x
private noncomputable def L4 (x : ℝ) :=
  chord (811 / 5000) (4663 / 10000) (571 / 2500) (1143 / 2000) x
private noncomputable def L5 (x : ℝ) :=
  chord (571 / 2500) (1143 / 2000) (3201 / 10000) (6799 / 10000) x
private noncomputable def L6 (x : ℝ) :=
  chord (3201 / 10000) (6799 / 10000) (857 / 2000) (1929 / 2500) x
private noncomputable def L7 (x : ℝ) :=
  chord (857 / 2000) (1929 / 2500) (5337 / 10000) (4189 / 5000) x
private noncomputable def L8 (x : ℝ) :=
  chord (5337 / 10000) (4189 / 5000) (4969 / 8000) (551 / 625) x
private noncomputable def L9 (x : ℝ) :=
  chord (4969 / 8000) (551 / 625) (3669 / 5000) (579 / 625) x
private noncomputable def L10 (x : ℝ) :=
  chord (3669 / 5000) (579 / 625) (4 / 5) (94911 / 100000) x
private noncomputable def L11 (x : ℝ) :=
  chord (4 / 5) (94911 / 100000) 1 1 x

/-- A rational, finite-size degree-eight Chung expansion profile. -/
noncomputable def filecoinBeta (x : ℝ) : ℝ :=
  min (L0 x) (min (L1 x) (min (L2 x) (min (L3 x) (min (L4 x) (min (L5 x)
    (min (L6 x) (min (L7 x) (min (L8 x) (min (L9 x) (min (L10 x) (L11 x)))))))))))

private theorem affine_concaveOn (a b : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x => a * x + b) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x _ y _ u v hu hv huv
  simp only [smul_eq_mul]
  linear_combination b * huv

private theorem line_concaveOn (a u b v : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (chord a u b v) := by
  convert affine_concaveOn ((v-u)/(b-a)) (u-(v-u)/(b-a)*a) using 1
  funext x
  simp only [chord]
  ring

/-- The Filecoin polygon is globally concave. -/
theorem filecoinBeta_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) filecoinBeta := by
  unfold filecoinBeta L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11
  exact (line_concaveOn 0 0 (5089 / 100000) (1 / 5)).inf
    ((line_concaveOn (5089 / 100000) (1 / 5) (46 / 625) (1331 / 5000)).inf
    ((line_concaveOn (46 / 625) (1331 / 5000) (74 / 625) (3031 / 8000)).inf
    ((line_concaveOn (74 / 625) (3031 / 8000) (811 / 5000) (4663 / 10000)).inf
    ((line_concaveOn (811 / 5000) (4663 / 10000) (571 / 2500) (1143 / 2000)).inf
    ((line_concaveOn (571 / 2500) (1143 / 2000) (3201 / 10000) (6799 / 10000)).inf
    ((line_concaveOn (3201 / 10000) (6799 / 10000) (857 / 2000) (1929 / 2500)).inf
    ((line_concaveOn (857 / 2000) (1929 / 2500) (5337 / 10000) (4189 / 5000)).inf
    ((line_concaveOn (5337 / 10000) (4189 / 5000) (4969 / 8000) (551 / 625)).inf
    ((line_concaveOn (4969 / 8000) (551 / 625) (3669 / 5000) (579 / 625)).inf
    ((line_concaveOn (3669 / 5000) (579 / 625) (4 / 5) (94911 / 100000)).inf
      (line_concaveOn (4 / 5) (94911 / 100000) 1 1)))))))))))

private theorem filecoinBeta_eq_L0 {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 5089 / 100000) :
    filecoinBeta x = L0 x := by
  unfold filecoinBeta
  rw [min_eq_left]
  simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
  norm_num at *
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

private theorem filecoinBeta_eq_L1 {x : ℝ} (h0 : 5089 / 100000 ≤ x)
    (h1 : x ≤ 46 / 625) : filecoinBeta x = L1 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L2 {x : ℝ} (h0 : 46 / 625 ≤ x)
    (h1 : x ≤ 74 / 625) : filecoinBeta x = L2 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L3 {x : ℝ} (h0 : 74 / 625 ≤ x)
    (h1 : x ≤ 811 / 5000) : filecoinBeta x = L3 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L4 {x : ℝ} (h0 : 811 / 5000 ≤ x)
    (h1 : x ≤ 571 / 2500) : filecoinBeta x = L4 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L5 {x : ℝ} (h0 : 571 / 2500 ≤ x)
    (h1 : x ≤ 3201 / 10000) : filecoinBeta x = L5 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L6 {x : ℝ} (h0 : 3201 / 10000 ≤ x)
    (h1 : x ≤ 857 / 2000) : filecoinBeta x = L6 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L7 {x : ℝ} (h0 : 857 / 2000 ≤ x)
    (h1 : x ≤ 5337 / 10000) : filecoinBeta x = L7 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L8 {x : ℝ} (h0 : 5337 / 10000 ≤ x)
    (h1 : x ≤ 4969 / 8000) : filecoinBeta x = L8 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L9 {x : ℝ} (h0 : 4969 / 8000 ≤ x)
    (h1 : x ≤ 3669 / 5000) : filecoinBeta x = L9 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L10 {x : ℝ} (h0 : 3669 / 5000 ≤ x)
    (h1 : x ≤ 4 / 5) : filecoinBeta x = L10 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

private theorem filecoinBeta_eq_L11 {x : ℝ} (h0 : 4 / 5 ≤ x)
    (_h1 : x ≤ 1) : filecoinBeta x = L11 x := by
  apply le_antisymm
  · simp [filecoinBeta]
  · simp only [filecoinBeta, le_min_iff]
    simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
    norm_num at *
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor; · linarith
    constructor <;> linarith

@[simp] theorem filecoinBeta_zero : filecoinBeta 0 = 0 := by
  rw [filecoinBeta_eq_L0 (by norm_num) (by norm_num)]
  norm_num [L0, chord]

@[simp] theorem filecoinBeta_one : filecoinBeta 1 = 1 := by
  rw [filecoinBeta_eq_L11 (by norm_num) (by norm_num)]
  norm_num [L11, chord]

/-- Every supporting line has slope at least the positive final slope. -/
private theorem filecoinBeta_add_slope_le (x y : ℝ) (hxy : x ≤ y) :
    filecoinBeta x + (5089 / 20000) * (y-x) ≤ filecoinBeta y := by
  have h0 : filecoinBeta x ≤ L0 x := by simp [filecoinBeta]
  have h1 : filecoinBeta x ≤ L1 x := by simp [filecoinBeta]
  have h2 : filecoinBeta x ≤ L2 x := by simp [filecoinBeta]
  have h3 : filecoinBeta x ≤ L3 x := by simp [filecoinBeta]
  have h4 : filecoinBeta x ≤ L4 x := by simp [filecoinBeta]
  have h5 : filecoinBeta x ≤ L5 x := by simp [filecoinBeta]
  have h6 : filecoinBeta x ≤ L6 x := by simp [filecoinBeta]
  have h7 : filecoinBeta x ≤ L7 x := by simp [filecoinBeta]
  have h8 : filecoinBeta x ≤ L8 x := by simp [filecoinBeta]
  have h9 : filecoinBeta x ≤ L9 x := by simp [filecoinBeta]
  have h10 : filecoinBeta x ≤ L10 x := by simp [filecoinBeta]
  have h11 : filecoinBeta x ≤ L11 x := by simp [filecoinBeta]
  rw [show filecoinBeta y =
    min (L0 y) (min (L1 y) (min (L2 y) (min (L3 y) (min (L4 y) (min (L5 y)
      (min (L6 y) (min (L7 y) (min (L8 y) (min (L9 y) (min (L10 y) (L11 y)))))))))))
    from rfl]
  simp only [le_min_iff]
  simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord] at *
  norm_num at *
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

/-- The finite-size polygon is strictly increasing (in fact, on all of `ℝ`). -/
theorem filecoinBeta_strictMono : StrictMono filecoinBeta := by
  intro x y hxy
  have h := filecoinBeta_add_slope_le x y hxy.le
  have hs : (0 : ℝ) < 5089 / 20000 := by norm_num
  nlinarith

theorem filecoinBeta_strictMonoOn :
    StrictMonoOn filecoinBeta (Icc (0 : ℝ) 1) := filecoinBeta_strictMono.strictMonoOn _

theorem filecoinBeta_maps {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    filecoinBeta x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rcases hx.1.eq_or_lt with rfl | h
    · simp
    · simpa using (filecoinBeta_strictMono h).le
  · rcases hx.2.eq_or_lt with rfl | h
    · simp
    · simpa using (filecoinBeta_strictMono h).le

theorem filecoinBeta_expands {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < filecoinBeta x := by
  simp only [filecoinBeta, lt_min_iff]
  simp only [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, chord]
  norm_num at *
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

/-- Anti-diagonal symmetry was built into the rational vertices. -/
theorem filecoinBeta_reversal {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    filecoinBeta (1 - filecoinBeta x) = 1 - x := by
  by_cases h1 : x ≤ 5089 / 100000
  · rw [filecoinBeta_eq_L0 hx.1.le h1]
    have hz : 1 - L0 x ∈ Icc (4 / 5 : ℝ) 1 := by
      simp only [L0, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L11 hz.1 hz.2]
    norm_num [L0, L11, chord]
    ring
  by_cases h2 : x ≤ 46 / 625
  · have hx0 : 5089 / 100000 ≤ x := by linarith
    rw [filecoinBeta_eq_L1 hx0 h2]
    have hz : 1 - L1 x ∈ Icc (3669 / 5000 : ℝ) (4 / 5) := by
      simp only [L1, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L10 hz.1 hz.2]
    norm_num [L1, L10, chord]
    ring
  by_cases h3 : x ≤ 74 / 625
  · have hx0 : 46 / 625 ≤ x := by linarith
    rw [filecoinBeta_eq_L2 hx0 h3]
    have hz : 1 - L2 x ∈ Icc (4969 / 8000 : ℝ) (3669 / 5000) := by
      simp only [L2, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L9 hz.1 hz.2]
    norm_num [L2, L9, chord]
    ring
  by_cases h4 : x ≤ 811 / 5000
  · have hx0 : 74 / 625 ≤ x := by linarith
    rw [filecoinBeta_eq_L3 hx0 h4]
    have hz : 1 - L3 x ∈ Icc (5337 / 10000 : ℝ) (4969 / 8000) := by
      simp only [L3, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L8 hz.1 hz.2]
    norm_num [L3, L8, chord]
    ring
  by_cases h5 : x ≤ 571 / 2500
  · have hx0 : 811 / 5000 ≤ x := by linarith
    rw [filecoinBeta_eq_L4 hx0 h5]
    have hz : 1 - L4 x ∈ Icc (857 / 2000 : ℝ) (5337 / 10000) := by
      simp only [L4, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L7 hz.1 hz.2]
    norm_num [L4, L7, chord]
    ring
  by_cases h6 : x ≤ 3201 / 10000
  · have hx0 : 571 / 2500 ≤ x := by linarith
    rw [filecoinBeta_eq_L5 hx0 h6]
    have hz : 1 - L5 x ∈ Icc (3201 / 10000 : ℝ) (857 / 2000) := by
      simp only [L5, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L6 hz.1 hz.2]
    norm_num [L5, L6, chord]
    ring
  by_cases h7 : x ≤ 857 / 2000
  · have hx0 : 3201 / 10000 ≤ x := by linarith
    rw [filecoinBeta_eq_L6 hx0 h7]
    have hz : 1 - L6 x ∈ Icc (571 / 2500 : ℝ) (3201 / 10000) := by
      simp only [L6, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L5 hz.1 hz.2]
    norm_num [L5, L6, chord]
    ring
  by_cases h8 : x ≤ 5337 / 10000
  · have hx0 : 857 / 2000 ≤ x := by linarith
    rw [filecoinBeta_eq_L7 hx0 h8]
    have hz : 1 - L7 x ∈ Icc (811 / 5000 : ℝ) (571 / 2500) := by
      simp only [L7, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L4 hz.1 hz.2]
    norm_num [L4, L7, chord]
    ring
  by_cases h9 : x ≤ 4969 / 8000
  · have hx0 : 5337 / 10000 ≤ x := by linarith
    rw [filecoinBeta_eq_L8 hx0 h9]
    have hz : 1 - L8 x ∈ Icc (74 / 625 : ℝ) (811 / 5000) := by
      simp only [L8, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L3 hz.1 hz.2]
    norm_num [L3, L8, chord]
    ring
  by_cases h10 : x ≤ 3669 / 5000
  · have hx0 : 4969 / 8000 ≤ x := by linarith
    rw [filecoinBeta_eq_L9 hx0 h10]
    have hz : 1 - L9 x ∈ Icc (46 / 625 : ℝ) (74 / 625) := by
      simp only [L9, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L2 hz.1 hz.2]
    norm_num [L2, L9, chord]
    ring
  by_cases h11 : x ≤ 4 / 5
  · have hx0 : 3669 / 5000 ≤ x := by linarith
    rw [filecoinBeta_eq_L10 hx0 h11]
    have hz : 1 - L10 x ∈ Icc (5089 / 100000 : ℝ) (46 / 625) := by
      simp only [L10, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L1 hz.1 hz.2]
    norm_num [L1, L10, chord]
    ring
  · have hx0 : 4 / 5 ≤ x := by linarith
    rw [filecoinBeta_eq_L11 hx0 hx.2.le]
    have hz : 1 - L11 x ∈ Icc (0 : ℝ) (5089 / 100000) := by
      simp only [L11, chord]
      norm_num at *
      constructor <;> linarith
    rw [filecoinBeta_eq_L0 hz.1 hz.2]
    norm_num [L0, L11, chord]
    ring

/-! ### The twelve segments in affine form

`filecoinBeta` is a `min` of chords; on each segment it agrees with one of them, and the
`p x + q` presentation is what `ChungChord.lean` consumes. -/

theorem filecoinBeta_affine_0 {x : ℝ} (_h0 : (0 : ℝ) ≤ x) (h1 : x ≤ 5089 / 100000) :
    filecoinBeta x = 20000 / 5089 * x + 0 := by
  rw [filecoinBeta_eq_L0 _h0 h1]
  simp only [L0, chord]
  ring

theorem filecoinBeta_affine_1 {x : ℝ} (h0 : 5089 / 100000 ≤ x) (h1 : x ≤ 46 / 625) :
    filecoinBeta x = 6620 / 2271 * x + 586541 / 11355000 := by
  rw [filecoinBeta_eq_L1 h0 h1]
  simp only [L1, chord]
  ring

theorem filecoinBeta_affine_2 {x : ℝ} (h0 : 46 / 625 ≤ x) (h1 : x ≤ 74 / 625) :
    filecoinBeta x = 4507 / 1792 * x + 45411 / 560000 := by
  rw [filecoinBeta_eq_L2 h0 h1]
  simp only [L2, chord]
  ring

theorem filecoinBeta_affine_3 {x : ℝ} (h0 : 74 / 625 ≤ x) (h1 : x ≤ 811 / 5000) :
    filecoinBeta x = 3497 / 1752 * x + 1248721 / 8760000 := by
  rw [filecoinBeta_eq_L3 h0 h1]
  simp only [L3, chord]
  ring

theorem filecoinBeta_affine_4 {x : ℝ} (h0 : 811 / 5000 ≤ x) (h1 : x ≤ 571 / 2500) :
    filecoinBeta x = 526 / 331 * x + 690281 / 3310000 := by
  rw [filecoinBeta_eq_L4 h0 h1]
  simp only [L4, chord]
  ring

theorem filecoinBeta_affine_5 {x : ℝ} (h0 : 571 / 2500 ≤ x) (h1 : x ≤ 3201 / 10000) :
    filecoinBeta x = 1084 / 917 * x + 2764799 / 9170000 := by
  rw [filecoinBeta_eq_L5 h0 h1]
  simp only [L5, chord]
  ring

theorem filecoinBeta_affine_6 {x : ℝ} (h0 : 3201 / 10000 ≤ x) (h1 : x ≤ 857 / 2000) :
    filecoinBeta x = 917 / 1084 * x + 4434799 / 10840000 := by
  rw [filecoinBeta_eq_L6 h0 h1]
  simp only [L6, chord]
  ring

theorem filecoinBeta_affine_7 {x : ℝ} (h0 : 857 / 2000 ≤ x) (h1 : x ≤ 5337 / 10000) :
    filecoinBeta x = 331 / 526 * x + 2640281 / 5260000 := by
  rw [filecoinBeta_eq_L7 h0 h1]
  simp only [L7, chord]
  ring

theorem filecoinBeta_affine_8 {x : ℝ} (h0 : 5337 / 10000 ≤ x) (h1 : x ≤ 4969 / 8000) :
    filecoinBeta x = 1752 / 3497 * x + 9973721 / 17485000 := by
  rw [filecoinBeta_eq_L8 h0 h1]
  simp only [L8, chord]
  ring

theorem filecoinBeta_affine_9 {x : ℝ} (h0 : 4969 / 8000 ≤ x) (h1 : x ≤ 3669 / 5000) :
    filecoinBeta x = 1792 / 4507 * x + 1787697 / 2816875 := by
  rw [filecoinBeta_eq_L9 h0 h1]
  simp only [L9, chord]
  ring

theorem filecoinBeta_affine_10 {x : ℝ} (h0 : 3669 / 5000 ≤ x) (h1 : x ≤ 4 / 5) :
    filecoinBeta x = 2271 / 6620 * x + 22331541 / 33100000 := by
  rw [filecoinBeta_eq_L10 h0 h1]
  simp only [L10, chord]
  ring

theorem filecoinBeta_affine_11 {x : ℝ} (h0 : 4 / 5 ≤ x) (_h1 : x ≤ (1 : ℝ)) :
    filecoinBeta x = 5089 / 20000 * x + 14911 / 20000 := by
  rw [filecoinBeta_eq_L11 h0 _h1]
  simp only [L11, chord]
  ring

/-- The unique maximizer of the polygon's unadjusted gain. -/
noncomputable def filecoinAlphaG : ℝ := 3201 / 10000

@[simp] theorem filecoinBeta_alphaG : filecoinBeta filecoinAlphaG = 6799 / 10000 := by
  rw [filecoinBeta_eq_L5 (by norm_num [filecoinAlphaG]) (by norm_num [filecoinAlphaG])]
  norm_num [filecoinAlphaG, L5, chord]

theorem filecoinAlphaG_mem : filecoinAlphaG ∈ Ioo (0 : ℝ) 1 := by
  norm_num [filecoinAlphaG]

/-- The gain increases through the first six segments and decreases through the last
six, so the anti-diagonal fixed vertex is its unique maximizer. -/
theorem filecoinAlphaG_max {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hne : x ≠ filecoinAlphaG) :
    filecoinBeta x - x < filecoinBeta filecoinAlphaG - filecoinAlphaG := by
  rcases lt_or_gt_of_ne hne with hleft | hright
  · by_cases h1 : x ≤ 5089 / 100000
    · rw [filecoinBeta_eq_L0 hx.1 h1, filecoinBeta_alphaG]
      norm_num [L0, chord, filecoinAlphaG] at *
      linarith
    by_cases h2 : x ≤ 46 / 625
    · rw [filecoinBeta_eq_L1 (by linarith) h2, filecoinBeta_alphaG]
      norm_num [L1, chord, filecoinAlphaG] at *
      linarith
    by_cases h3 : x ≤ 74 / 625
    · rw [filecoinBeta_eq_L2 (by linarith) h3, filecoinBeta_alphaG]
      norm_num [L2, chord, filecoinAlphaG] at *
      linarith
    by_cases h4 : x ≤ 811 / 5000
    · rw [filecoinBeta_eq_L3 (by linarith) h4, filecoinBeta_alphaG]
      norm_num [L3, chord, filecoinAlphaG] at *
      linarith
    by_cases h5 : x ≤ 571 / 2500
    · rw [filecoinBeta_eq_L4 (by linarith) h5, filecoinBeta_alphaG]
      norm_num [L4, chord, filecoinAlphaG] at *
      linarith
    · rw [filecoinBeta_eq_L5 (by linarith) hleft.le, filecoinBeta_alphaG]
      norm_num [L5, chord, filecoinAlphaG] at *
      linarith
  · by_cases h7 : x ≤ 857 / 2000
    · rw [filecoinBeta_eq_L6 hright.le h7, filecoinBeta_alphaG]
      norm_num [L6, chord, filecoinAlphaG] at *
      linarith
    by_cases h8 : x ≤ 5337 / 10000
    · rw [filecoinBeta_eq_L7 (by linarith) h8, filecoinBeta_alphaG]
      norm_num [L7, chord, filecoinAlphaG] at *
      linarith
    by_cases h9 : x ≤ 4969 / 8000
    · rw [filecoinBeta_eq_L8 (by linarith) h9, filecoinBeta_alphaG]
      norm_num [L8, chord, filecoinAlphaG] at *
      linarith
    by_cases h10 : x ≤ 3669 / 5000
    · rw [filecoinBeta_eq_L9 (by linarith) h10, filecoinBeta_alphaG]
      norm_num [L9, chord, filecoinAlphaG] at *
      linarith
    by_cases h11 : x ≤ 4 / 5
    · rw [filecoinBeta_eq_L10 (by linarith) h11, filecoinBeta_alphaG]
      norm_num [L10, chord, filecoinAlphaG] at *
      linarith
    · rw [filecoinBeta_eq_L11 (by linarith) hx.2, filecoinBeta_alphaG]
      norm_num [L11, chord, filecoinAlphaG] at *
      linarith

/-! Exact values used by the Filecoin latency certificates. -/

@[simp] theorem filecoinBeta_08 : filecoinBeta (4 / 5) = 94911 / 100000 := by
  rw [filecoinBeta_eq_L10 (by norm_num) (by norm_num)]
  norm_num [L10, chord]

@[simp] theorem filecoinBeta_1184 : filecoinBeta (74 / 625) = 3031 / 8000 := by
  rw [filecoinBeta_eq_L2 (by norm_num) (by norm_num)]
  norm_num [L2, chord]

@[simp] theorem filecoinBeta_1622 : filecoinBeta (811 / 5000) = 4663 / 10000 := by
  rw [filecoinBeta_eq_L3 (by norm_num) (by norm_num)]
  norm_num [L3, chord]

@[simp] theorem filecoinBeta_4285 : filecoinBeta (857 / 2000) = 1929 / 2500 := by
  rw [filecoinBeta_eq_L6 (by norm_num) (by norm_num)]
  norm_num [L6, chord]

@[simp] theorem filecoinBeta_7338 : filecoinBeta (3669 / 5000) = 579 / 625 := by
  rw [filecoinBeta_eq_L9 (by norm_num) (by norm_num)]
  norm_num [L9, chord]
@[simp] theorem filecoinBeta_8886 : filecoinBeta (4443 / 5000) = 97165427 / 100000000 := by
  rw [filecoinBeta_eq_L11 (by norm_num) (by norm_num)]
  norm_num [L11, chord]

/-! The four extra evaluations the raised-threshold certificate of
`ChungFilecoinMirror.lean` needs.  Its reference chain is the `β_δ` orbit of
`1 - β(0.8886)`, and the reversal symmetry of the polygon makes every one of its points a
breakpoint of the polygon read backwards: `0.02834573`, `0.0736`, `0.2284`, `0.5337`,
`0.8`.  The last two evaluations below are the new ones; `β(0.8)` is `filecoinBeta_08`. -/

@[simp] theorem filecoinBeta_0283 :
    filecoinBeta (2834573 / 100000000) = 557 / 5000 := by
  rw [filecoinBeta_eq_L0 (by norm_num) (by norm_num)]
  norm_num [L0, chord]

@[simp] theorem filecoinBeta_0736 : filecoinBeta (46 / 625) = 1331 / 5000 := by
  rw [filecoinBeta_eq_L2 (by norm_num) (by norm_num)]
  norm_num [L2, chord]

@[simp] theorem filecoinBeta_0886 :
    filecoinBeta (443 / 5000) = 2723177 / 8960000 := by
  rw [filecoinBeta_eq_L2 (by norm_num) (by norm_num)]
  norm_num [L2, chord]

@[simp] theorem filecoinBeta_2284 : filecoinBeta (571 / 2500) = 1143 / 2000 := by
  rw [filecoinBeta_eq_L5 (by norm_num) (by norm_num)]
  norm_num [L5, chord]

@[simp] theorem filecoinBeta_5337 : filecoinBeta (5337 / 10000) = 4189 / 5000 := by
  rw [filecoinBeta_eq_L8 (by norm_num) (by norm_num)]
  norm_num [L8, chord]

/-- The polygon's top piece, in closed form.  The raised-threshold certificate's `chord`
obligation compares one free level against the top bucket over `[0.8, 0.8886]`, which is
inside this piece. -/
theorem filecoinBeta_top {x : ℝ} (h0 : 4 / 5 ≤ x) (h1 : x ≤ 1) :
    filecoinBeta x = 94911 / 100000 + 5089 / 20000 * (x - 4 / 5) := by
  rw [filecoinBeta_eq_L11 h0 h1]
  norm_num [L11, chord]

@[simp] theorem filecoinBeta_06 :
    filecoinBeta (3 / 5) = 1171517 / 1345000 := by
  rw [filecoinBeta_eq_L8 (by norm_num) (by norm_num)]
  norm_num [L8, chord]
/-- The two exact intersections with the `δ = 0.0378` gain line. -/
noncomputable def filecoinAlphaMin : ℝ := 961821 / 74555000
noncomputable def filecoinAlphaMax : ℝ := 14155 / 14911

@[simp] theorem filecoinBeta_alphaMin :
    filecoinBeta filecoinAlphaMin = 3780000 / 74555000 := by
  rw [filecoinBeta_eq_L0 (by norm_num [filecoinAlphaMin])
    (by norm_num [filecoinAlphaMin])]
  norm_num [filecoinAlphaMin, L0, chord]

@[simp] theorem filecoinBeta_half_alphaMin :
    filecoinBeta (filecoinAlphaMin / 2) = 378 / 14911 := by
  rw [filecoinBeta_eq_L0 (by norm_num [filecoinAlphaMin])
    (by norm_num [filecoinAlphaMin])]
  norm_num [filecoinAlphaMin, L0, chord]

@[simp] theorem filecoinBeta_alphaMax :
    filecoinBeta filecoinAlphaMax = 73593179 / 74555000 := by
  rw [filecoinBeta_eq_L11 (by norm_num [filecoinAlphaMax])
    (by norm_num [filecoinAlphaMax])]
  norm_num [filecoinAlphaMax, L11, chord]

end ChungCurve
end ProofOfSpace

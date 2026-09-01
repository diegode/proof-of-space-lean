import ProofOfSpace.PortExpansionProbability
import ProofOfSpace.ChungFilecoin
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Probabilistic expansion for the Filecoin Chung-8 polygon

This file supplies the finite-grid and endpoint bookkeeping needed to combine the
one-port-permutation bound with the rational Filecoin polygon. The sampling interval is
slightly wider than the deterministic pebbling interval, so arbitrary source sets can
be rounded to a sampled grid point without strengthening the deterministic graph
hypothesis.
-/

namespace ProofOfSpace
namespace ChungCurve

open Finset Set Real
open scoped ENNReal

/-- Lower endpoint used by the probabilistic estimate. -/
noncomputable def expansionAlphaMin : ℝ := filecoinAlphaMin / 2

/-- Its anti-diagonal partner. -/
noncomputable def expansionAlphaMax : ℝ := 1 - filecoinBeta expansionAlphaMin

/-- Uniform gain available on the wider probabilistic expansion interval. -/
noncomputable def expansionMargin : ℝ := 189 / 10000

/-- Reyzin's `ε_chung`, measured in bits. -/
noncomputable def expansionEpsilon : ℝ := 1 / 2 ^ (22 : ℕ)

/-- One unit of finite-grid rounding is reserved from the polygon gain. -/
noncomputable def finiteExpansionMargin (n : ℕ) : ℝ := expansionMargin - 1 / n

/-- Largest integer neighbourhood size still treated as a failure at source size `k`.
The outer `min` makes the profile bounded even away from its active range. -/
noncomputable def roundedExpansionProfile (n k : ℕ) : ℕ :=
  min n (Nat.ceil (filecoinBeta ((k : ℝ) / n) * n) - 1)

/-- The simplified expansion-failure bound. -/
noncomputable def expansionFailureBound (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (1 / 8) /
        (2 * Real.pi * expansionAlphaMin * Real.sqrt (finiteExpansionMargin n)) *
      Real.exp (-(n : ℝ) * expansionEpsilon * Real.log 2))

/-- The explicit width conditions needed by the rounded finite-size argument. -/
class FiniteExpansionConditions (n : ℕ) : Prop where
  n_pos : 0 < n
  delta_pos : 0 < finiteExpansionMargin n
  grid_buffer : 1 / (n : ℝ) ≤ expansionAlphaMax - filecoinAlphaMax

/-- Reyzin's sufficient graph-width bound for the requested security level. The
constant `12/5 = 2.4` bounds the degree-independent prefactor. -/
class ExpansionSecurityConditions (n : ℕ) (lambda : ℝ) : Prop
    extends FiniteExpansionConditions n where
  security :
    (lambda - 12 / 5 - Real.logb 2 expansionAlphaMin -
      Real.logb 2 (finiteExpansionMargin n) / 2) / expansionEpsilon < n

theorem expansionAlphaMin_mem : expansionAlphaMin ∈ Ioo (0 : ℝ) 1 := by
  norm_num [expansionAlphaMin, filecoinAlphaMin]

theorem expansionAlphaMin_certificate_range :
    1 / 2 ^ 25 ≤ expansionAlphaMin := by
  norm_num [expansionAlphaMin, filecoinAlphaMin]

theorem expansionAlphaMin_gain :
    expansionMargin ≤ filecoinBeta expansionAlphaMin - expansionAlphaMin := by
  have hconc := filecoinBeta_concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show filecoinAlphaMin ∈ Set.Icc (0 : ℝ) 1 by
      norm_num [filecoinAlphaMin])
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconc
  rw [show (1 / 2 : ℝ) * 0 + 1 / 2 * filecoinAlphaMin = expansionAlphaMin by
    simp only [expansionAlphaMin]
    ring] at hconc
  rw [filecoinBeta_zero, filecoinBeta_alphaMin] at hconc
  norm_num [expansionMargin, expansionAlphaMin, filecoinAlphaMin] at hconc ⊢
  linarith

theorem expansionAlphaMax_mem : expansionAlphaMax ∈ Ioo (0 : ℝ) 1 := by
  have ha := expansionAlphaMin_mem
  have hb0 : 0 < filecoinBeta expansionAlphaMin := by
    simpa using filecoinBeta_strictMono ha.1
  have hb1 : filecoinBeta expansionAlphaMin < 1 := by
    simpa using filecoinBeta_strictMono ha.2
  exact ⟨by simp only [expansionAlphaMax]; linarith,
    by simp only [expansionAlphaMax]; linarith⟩

@[simp] theorem expansionAlphaMax_eq : expansionAlphaMax = (14533 : ℝ) / 14911 := by
  rw [expansionAlphaMax, expansionAlphaMin, filecoinBeta_half_alphaMin]
  norm_num

@[simp] theorem filecoinBeta_expansionAlphaMax :
    filecoinBeta expansionAlphaMax = 1 - expansionAlphaMin := by
  exact filecoinBeta_reversal expansionAlphaMin_mem

theorem expansion_gain {x : ℝ} (hx : x ∈ Icc expansionAlphaMin expansionAlphaMax) :
    expansionMargin ≤ filecoinBeta x - x := by
  have ha := expansionAlphaMin_mem
  have hb := expansionAlphaMax_mem
  have hgain : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => filecoinBeta t - t) := by
    exact filecoinBeta_concaveOn.sub (convexOn_id (convex_Icc (0 : ℝ) 1))
  have hendA := expansionAlphaMin_gain
  have hendB : expansionMargin ≤ filecoinBeta expansionAlphaMax - expansionAlphaMax := by
    rw [filecoinBeta_expansionAlphaMax, expansionAlphaMax]
    linarith [expansionAlphaMin_gain]
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · exact hendA
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · exact hendB
  have hden : 0 < expansionAlphaMax - expansionAlphaMin := sub_pos.mpr (hax.trans hxb)
  have hne : expansionAlphaMax - expansionAlphaMin ≠ 0 := ne_of_gt hden
  let u := (expansionAlphaMax - x) / (expansionAlphaMax - expansionAlphaMin)
  let v := (x - expansionAlphaMin) / (expansionAlphaMax - expansionAlphaMin)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have huv : u + v = 1 := by
    dsimp [u, v]
    field_simp
    ring
  have hc := hgain.2 (x := expansionAlphaMin) (y := expansionAlphaMax)
    (show expansionAlphaMin ∈ Set.Icc (0 : ℝ) 1 from ⟨ha.1.le, ha.2.le⟩)
    (show expansionAlphaMax ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.1.le, hb.2.le⟩)
    hu hv huv
  simp only [smul_eq_mul] at hc
  have hcomb : u * expansionAlphaMin + v * expansionAlphaMax = x := by
    dsimp [u, v]
    rw [show (expansionAlphaMax - x) / (expansionAlphaMax - expansionAlphaMin) *
        expansionAlphaMin +
        (x - expansionAlphaMin) / (expansionAlphaMax - expansionAlphaMin) *
          expansionAlphaMax =
      ((expansionAlphaMax - x) * expansionAlphaMin +
        (x - expansionAlphaMin) * expansionAlphaMax) /
          (expansionAlphaMax - expansionAlphaMin) by ring,
      div_eq_iff hne]
    ring
  rw [hcomb] at hc
  have hA := mul_le_mul_of_nonneg_left hendA hu
  have hB := mul_le_mul_of_nonneg_left hendB hv
  calc
    expansionMargin = u * expansionMargin + v * expansionMargin := by
      rw [← add_mul, huv, one_mul]
    _ ≤ u * (filecoinBeta expansionAlphaMin - expansionAlphaMin) +
        v * (filecoinBeta expansionAlphaMax - expansionAlphaMax) := add_le_add hA hB
    _ ≤ filecoinBeta x - x := hc

theorem expansion_complement {x : ℝ} (hx : x ∈ Icc expansionAlphaMin expansionAlphaMax) :
    expansionAlphaMin ≤ 1 - filecoinBeta x := by
  have hmono := filecoinBeta_strictMono.monotone hx.2
  rw [filecoinBeta_expansionAlphaMax] at hmono
  linarith

theorem expansion_beta_lt_one {x : ℝ} (hx : x ∈ Icc expansionAlphaMin expansionAlphaMax) :
    filecoinBeta x < 1 := by
  have := expansion_complement hx
  linarith [expansionAlphaMin_mem.1]

theorem expansion_exponent_certificate {x : ℝ}
    (hx : x ∈ Icc expansionAlphaMin expansionAlphaMax) :
    shiftedSec 8 (expansionEpsilon * Real.log 2) x (filecoinBeta x) < 0 := by
  have hright : x ≤ 1 - 1 / 2 ^ 23 := by
    calc
      x ≤ expansionAlphaMax := hx.2
      _ ≤ 1 - 1 / 2 ^ 23 := by
        have hba : expansionAlphaMin ≤ filecoinBeta expansionAlphaMin :=
          (filecoinBeta_expands expansionAlphaMin_mem).le
        norm_num [expansionAlphaMax, expansionAlphaMin, filecoinAlphaMin] at hba ⊢
        linarith
  have hfixed := filecoinBeta_shiftedSec_neg
    (expansionAlphaMin_certificate_range.trans hx.1) hright
  have hlog : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have heps : 0 < expansionEpsilon := by
    norm_num [expansionEpsilon]
  simp only [shiftedSec, expansionEpsilon, filecoinEpsilon] at hfixed ⊢
  nlinarith

theorem roundedExpansionProfile_le (n k : ℕ) : roundedExpansionProfile n k ≤ n := by
  exact min_le_left _ _

/-- All integer-rounding hypotheses consumed by the exponential union-bound theorem. -/
theorem roundedExpansionProfile_spec (n : ℕ) [C : FiniteExpansionConditions n] (k : ℕ)
    (hk : expansionAlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ expansionAlphaMax) :
    0 < k ∧ k < roundedExpansionProfile n k ∧ roundedExpansionProfile n k < n ∧
      expansionAlphaMin ≤ 1 - (roundedExpansionProfile n k : ℝ) / n ∧
      finiteExpansionMargin n ≤
        (roundedExpansionProfile n k : ℝ) / n - (k : ℝ) / n ∧
      chungExponent 8 ((k : ℝ) / n) ((roundedExpansionProfile n k : ℝ) / n) ≤
        -expansionEpsilon * Real.log 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  let x : ℝ := (k : ℝ) / n
  have hx : x ∈ Icc expansionAlphaMin expansionAlphaMax := hk
  have hx0 : 0 < x := expansionAlphaMin_mem.1.trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt expansionAlphaMax_mem.2
  have hk0R : (0 : ℝ) < k := by
    dsimp [x] at hx0
    rcases (div_pos_iff.mp hx0) with h | h
    · exact h.1
    · linarith
  have hk0 : 0 < k := by exact_mod_cast hk0R
  have hgain := expansion_gain hx
  have hcomp := expansion_complement hx
  have hxb : x < filecoinBeta x := filecoinBeta_expands ⟨hx0, hx1⟩
  have hb0 : 0 < filecoinBeta x := hx0.trans hxb
  have hb1 := expansion_beta_lt_one hx
  let c : ℕ := Nat.ceil (filecoinBeta x * n)
  have hcpos : 0 < c := by
    exact Nat.one_le_ceil_iff.mpr (mul_pos hb0 hnR)
  have hcle : c ≤ n := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hb1.le hnR.le).trans_eq (one_mul (n : ℝ))
  have hmdef : roundedExpansionProfile n k = c - 1 := by
    change min n (c - 1) = c - 1
    rw [Nat.min_eq_right]
    exact (Nat.sub_le c 1).trans hcle
  have hxn : x * n = k := by
    dsimp [x]
    field_simp
  have hdelta : 1 < expansionMargin * n := by
    have := C.delta_pos
    rw [finiteExpansionMargin] at this
    have hinv : 1 / (n : ℝ) * n = 1 := by field_simp
    nlinarith
  have hkn : (k : ℝ) + 1 < filecoinBeta x * n := by
    have hg := mul_le_mul_of_nonneg_right hgain hnR.le
    rw [sub_mul, hxn] at hg
    nlinarith
  have hkceil : k + 1 < c := by
    rw [Nat.lt_ceil]
    exact_mod_cast hkn
  have hkm : k < roundedExpansionProfile n k := by
    rw [hmdef]
    omega
  have hmn : roundedExpansionProfile n k < n := by
    rw [hmdef]
    omega
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hz0 : 0 ≤ filecoinBeta x * n := (mul_pos hb0 hnR).le
  have hceilUpper : (c : ℝ) < filecoinBeta x * n + 1 := by
    exact Nat.ceil_lt_add_one hz0
  have hceilLower : filecoinBeta x * n ≤ (c : ℝ) := Nat.le_ceil _
  have hmUpper : (roundedExpansionProfile n k : ℝ) / n < filecoinBeta x := by
    rw [hmdef, hcast]
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have hmLower : filecoinBeta x - 1 / n ≤
      (roundedExpansionProfile n k : ℝ) / n := by
    rw [hmdef, hcast]
    apply (le_div_iff₀ hnR).2
    have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
    nlinarith
  have hya : expansionAlphaMin ≤
      1 - (roundedExpansionProfile n k : ℝ) / n := by
    linarith
  have hgap : finiteExpansionMargin n ≤
      (roundedExpansionProfile n k : ℝ) / n - (k : ℝ) / n := by
    rw [← show x = (k : ℝ) / n by rfl, finiteExpansionMargin]
    linarith
  let y : ℝ := (roundedExpansionProfile n k : ℝ) / n
  have hxy : x < y := by
    dsimp [x, y]
    exact div_lt_div_of_pos_right (by exact_mod_cast hkm) hnR
  have hy1 : y < 1 := by
    dsimp [y]
    rw [div_lt_one hnR]
    exact_mod_cast hmn
  have heps0 : 0 ≤ expansionEpsilon * Real.log 2 := by
    exact mul_nonneg (by norm_num [expansionEpsilon]) (Real.log_nonneg (by norm_num))
  have hcert := expansion_exponent_certificate hx
  have hlevel := level_lt_of_shiftedSec_neg (d := 8) (hd := by norm_num) heps0 hx0 hxb hb1 hcert
  have hbroot := (shiftedSec_neg_iff (d := 8) (by norm_num) heps0 hx0 hx1 hlevel
    hxb hb1).1 hcert
  have hyroot : y < shiftedBeta 8 (expansionEpsilon * Real.log 2) x :=
    (show y < filecoinBeta x from hmUpper).trans hbroot
  have hycert := (shiftedSec_neg_iff (d := 8) (by norm_num) heps0 hx0 hx1 hlevel
    hxy hy1).2 hyroot
  have hexp : chungExponent 8 x y ≤ -expansionEpsilon * Real.log 2 := by
    rw [shiftedSec, ← chungExponent_eq_sec hx0 hxy hy1] at hycert
    linarith
  exact ⟨hk0, hkm, hmn, hya, hgap, by simpa [x, y] using hexp⟩

/-- The Chung port-expansion bound instantiated with the Filecoin polygon and its
rounded finite-grid profile. -/
theorem portExpansion_whp_filecoin (n : ℕ) [C : FiniteExpansionConditions n] :
    Concrete.HoldsWithFailureAtMost (Concrete.PortInterlayer.uniformLaw n)
      (fun P => P.ExpandsProfileOn expansionAlphaMin expansionAlphaMax
        (roundedExpansionProfile n))
      (expansionFailureBound n) := by
  apply Concrete.portExpansion_whp_exponential n expansionAlphaMin expansionAlphaMax
    (finiteExpansionMargin n) expansionEpsilon (roundedExpansionProfile n)
    C.n_pos expansionAlphaMin_mem.1 C.delta_pos (roundedExpansionProfile_le n)
  exact roundedExpansionProfile_spec n

/-- The numerical prefactor estimate used in Reyzin's graph-width condition. -/
theorem expansion_prefactor_logb_lt :
    Real.logb 2 (Real.exp (1 / 8) / (2 * Real.pi)) < -(12 / 5 : ℝ) := by
  have hlogpi : Real.log 3 < Real.log Real.pi :=
    Real.strictMonoOn_log (by norm_num) (by exact Real.pi_pos) Real.pi_gt_three
  have hnum : (1 / 8 : ℝ) + (7 / 5) * Real.log 2 < Real.log 3 := by
    nlinarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.log_div_log, Real.log_div (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
  apply (div_lt_iff₀ hlog2).2
  nlinarith

/-- Under the paper's displayed width condition, the expansion-failure bound is at
most `2⁻ˡᵃᵐᵇᵈᵃ`. -/
theorem expansionFailureBound_le_security (n : ℕ) (lambda : ℝ)
    [C : ExpansionSecurityConditions n lambda] :
    expansionFailureBound n ≤ ENNReal.ofReal (Real.exp (-lambda * Real.log 2)) := by
  let a := expansionAlphaMin
  let delta := finiteExpansionMargin n
  let eps := expansionEpsilon
  have ha : 0 < a := expansionAlphaMin_mem.1
  have hd : 0 < delta := C.delta_pos
  have he : 0 < eps := by norm_num [eps, expansionEpsilon]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt delta := Real.sqrt_pos.2 hd
  have hcore := expansion_prefactor_logb_lt
  have hpref : Real.logb 2
      (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) <
      -(12 / 5 : ℝ) - Real.logb 2 a - Real.logb 2 delta / 2 := by
    rw [show Real.logb 2
        (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) =
        Real.logb 2 (Real.exp (1 / 8) / (2 * Real.pi)) -
          Real.logb 2 a - Real.logb 2 delta / 2 by
      simp only [Real.logb]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity : (2 * Real.pi * a : ℝ) ≠ 0)
          (ne_of_gt hsqrt),
        Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) (ne_of_gt ha),
        Real.log_sqrt hd.le]
      ring]
    nlinarith
  have hsec := C.security
  change (lambda - 12 / 5 - Real.logb 2 a - Real.logb 2 delta / 2) / eps < n at hsec
  have hnexp : lambda + Real.logb 2
      (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) < (n : ℝ) * eps := by
    have := (div_lt_iff₀ he).1 hsec
    nlinarith
  have hlogpref : Real.log
      (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) =
      Real.logb 2 (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) *
        Real.log 2 := by
    rw [Real.logb]
    field_simp
  have hexpArg : Real.log
        (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta)) -
        (n : ℝ) * eps * Real.log 2 < -lambda * Real.log 2 := by
    rw [hlogpref]
    nlinarith [mul_lt_mul_of_pos_right hnexp hl2]
  have hprefpos : 0 < Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta) := by
    positivity
  rw [expansionFailureBound]
  apply ENNReal.ofReal_le_ofReal
  change Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt delta) *
      Real.exp (-(n : ℝ) * eps * Real.log 2) ≤ Real.exp (-lambda * Real.log 2)
  rw [← Real.exp_log hprefpos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem beta_mul_le_neighborhood_of_profile
    {n : ℕ} [C : FiniteExpansionConditions n] {P : Concrete.PortInterlayer n}
    {T : Finset (Fin n)}
    (ht : expansionAlphaMin ≤ (T.card : ℝ) / n ∧
      (T.card : ℝ) / n ≤ expansionAlphaMax)
    (hP : roundedExpansionProfile n T.card < (P.neighborhood T).card) :
    filecoinBeta ((T.card : ℝ) / n) * n ≤ (P.neighborhood T).card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  let t : ℝ := (T.card : ℝ) / n
  have ht' : t ∈ Icc expansionAlphaMin expansionAlphaMax := ht
  have ht0 : 0 < t := expansionAlphaMin_mem.1.trans_le ht'.1
  have ht1 : t < 1 := ht'.2.trans_lt expansionAlphaMax_mem.2
  have hb0 : 0 < filecoinBeta t := ht0.trans (filecoinBeta_expands ⟨ht0, ht1⟩)
  have hb1 := expansion_beta_lt_one ht'
  let c : ℕ := Nat.ceil (filecoinBeta t * n)
  have hcpos : 0 < c := Nat.one_le_ceil_iff.mpr (mul_pos hb0 hnR)
  have hcle : c ≤ n := by
    apply Nat.ceil_le.mpr
    exact (mul_le_mul_of_nonneg_right hb1.le hnR.le).trans_eq (one_mul (n : ℝ))
  have hmdef : roundedExpansionProfile n T.card = c - 1 := by
    change min n (c - 1) = c - 1
    rw [Nat.min_eq_right]
    exact (Nat.sub_le c 1).trans hcle
  have hcN : c ≤ (P.neighborhood T).card := by
    rw [hmdef] at hP
    omega
  calc
    filecoinBeta ((T.card : ℝ) / n) * n = filecoinBeta t * n := rfl
    _ ≤ (c : ℝ) := Nat.le_ceil _
    _ ≤ (P.neighborhood T).card := by exact_mod_cast hcN

/-- A successful rounded profile supplies exactly the operational expansion property
used by the deterministic Filecoin stack. The `grid_buffer` field handles the one
rounded subset needed when an actual source density lies above the sampled interval. -/
theorem portExpands_filecoin_of_profile (n : ℕ) [C : FiniteExpansionConditions n]
    (P : Concrete.PortInterlayer n)
    (hP : P.ExpandsProfileOn expansionAlphaMin expansionAlphaMax
      (roundedExpansionProfile n)) :
    P.Expands chung8Setting := by
  intro T x hx hxt
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.n_pos
  let t : ℝ := (T.card : ℝ) / n
  have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hnR]
    exact_mod_cast hTn
  have hx0 : 0 ≤ x := by
    exact (by norm_num [chung8Setting, FiniteSizeProfile.αmin, filecoinAlphaMin] :
      (0 : ℝ) ≤ chung8Setting.αmin).trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans (by
    norm_num [chung8Setting, FiniteSizeProfile.αmax, filecoinAlphaMax])
  have hmono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hxu : x ≤ u) :
      filecoinBeta x ≤ filecoinBeta u :=
    filecoinBeta_strictMono.monotone hxu
  rw [show chung8Setting.β = filecoinBeta by rfl]
  by_cases htb : t ≤ expansionAlphaMax
  · have hta : expansionAlphaMin ≤ t := by
      have hwide : expansionAlphaMin ≤ filecoinAlphaMin := by
        norm_num [expansionAlphaMin, filecoinAlphaMin]
      have hxmin : filecoinAlphaMin ≤ x := by
        simpa [chung8Setting, FiniteSizeProfile.αmin] using hx.1
      exact hwide.trans (hxmin.trans hxt)
    have hcert := beta_mul_le_neighborhood_of_profile
      (P := P) (T := T) ⟨hta, htb⟩ (hP T hta htb)
    exact (mul_le_mul_of_nonneg_right (hmono ht0 ht1 hxt) hnR.le).trans hcert
  · have hxn : x * n ≤ T.card := by
      apply (le_div_iff₀ hnR).1
      simpa [t] using hxt
    let r : ℕ := Nat.ceil (x * n)
    have hrT : r ≤ T.card := Nat.ceil_le.mpr hxn
    obtain ⟨I, hIT, hIcard⟩ := Finset.exists_subset_card_eq hrT
    let u : ℝ := (I.card : ℝ) / n
    have hxn0 : 0 ≤ x * n := mul_nonneg hx0 hnR.le
    have hxu : x ≤ u := by
      dsimp [u]
      rw [hIcard]
      apply (le_div_iff₀ hnR).2
      exact Nat.le_ceil _
    have hux : u < x + 1 / n := by
      dsimp [u]
      rw [hIcard]
      have hc := Nat.ceil_lt_add_one hxn0
      apply (div_lt_iff₀ hnR).2
      have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
      nlinarith
    have hua : expansionAlphaMin ≤ u := by
      have hwide : expansionAlphaMin ≤ filecoinAlphaMin := by
        norm_num [expansionAlphaMin, filecoinAlphaMin]
      have hxmin : filecoinAlphaMin ≤ x := by
        simpa [chung8Setting, FiniteSizeProfile.αmin] using hx.1
      exact hwide.trans (hxmin.trans hxu)
    have hub : u ≤ expansionAlphaMax := by
      have hxmax : x ≤ filecoinAlphaMax := by
        simpa [chung8Setting, FiniteSizeProfile.αmax] using hx.2
      linarith [C.grid_buffer]
    have hcert := beta_mul_le_neighborhood_of_profile
      (P := P) (T := I) ⟨hua, hub⟩ (hP I hua hub)
    have hneigh : P.neighborhood I ⊆ P.neighborhood T := by
      apply Finset.image_subset_image
      intro q hq
      rw [Concrete.PortInterlayer.ports, Finset.mem_product] at hq ⊢
      exact ⟨hq.1, hIT hq.2⟩
    have hcard : (P.neighborhood I).card ≤ (P.neighborhood T).card :=
      Finset.card_le_card hneigh
    have hu0 : 0 ≤ u := hx0.trans hxu
    have hu1 : u ≤ 1 := hub.trans expansionAlphaMax_mem.2.le
    calc
      filecoinBeta x * n ≤ filecoinBeta u * n :=
        mul_le_mul_of_nonneg_right (hmono hu0 hu1 hxu) hnR.le
      _ ≤ (P.neighborhood I).card := hcert
      _ ≤ (P.neighborhood T).card := by exact_mod_cast hcard

end ChungCurve
end ProofOfSpace

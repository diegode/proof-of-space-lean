import ProofOfSpace.DRSample.Valiant
import ProofOfSpace.DRSample.PaperWidth
import ProofOfSpace.DRSample.AsymptoticRobustness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Balanced robustness is asymptotically optimal

Valiant's theorem with `k = ⌈log₂⌈log₂ n⌉⌉` gives both a deletion set and
remaining depth of order `n/L(n)`. This choice has the same asymptotic order
as the choice in the paper and gives a slightly smaller depth bound.
-/
namespace ProofOfSpace.DRSample
open Finset Filter ProofOfSpaceStatement

theorem balanced_reduction {n Δ : ℕ} (hn : 2 ^ 120 ≤ n) (hΔ : 2 ≤ Δ)
    {edge : Fin n → Fin n → Prop} (hordered : IsOrdered edge)
    (hdegree : IndegreeAtMost edge Δ) :
    ∃ S : Finset (Fin n), ∃ d : ℕ,
      (S.card : ℝ) ≤ 2 * Δ * n / robustnessScale n ∧
      (d : ℝ) ≤ 2 * n / robustnessScale n ∧ DepthAtMost edge S d := by
  let x := Real.logb 2 n
  let y := Real.logb 2 x
  let h := Nat.clog 2 n
  let k := Nat.clog 2 h
  obtain ⟨hx, hy, hxy, _⟩ := log_parameters hn
  change 120 ≤ x at hx
  change 6 ≤ y at hy
  change 16 * y ≤ x at hxy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLo : x ≤ (h : ℝ) := by
    simpa only [x, h, ← Real.natCeil_logb_natCast 2 n, Nat.cast_ofNat] using (Nat.le_ceil x)
  have hHi : (h : ℝ) < x + 1 := by
    simpa only [x, h, ← Real.natCeil_logb_natCast 2 n, Nat.cast_ofNat] using
      (Nat.ceil_lt_add_one hx0.le)
  have hh0 : (0 : ℝ) < h := hx0.trans_le hLo
  have hlogh : 0 ≤ Real.logb 2 (h : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
  have hkHi : (k : ℝ) < Real.logb 2 (h : ℝ) + 1 := by
    simpa only [k, ← Real.natCeil_logb_natCast 2 h, Nat.cast_ofNat] using
      (Nat.ceil_lt_add_one hlogh)
  have hloghHi : Real.logb 2 (h : ℝ) ≤ y + 1 := by
    calc
      _ ≤ Real.logb 2 (2 * x) :=
        Real.logb_le_logb_of_le (by norm_num) hh0 (by linarith)
      _ = y + 1 := by
        rw [Real.logb_mul (by norm_num) hx0.ne', Real.logb_self_eq_one (by norm_num)]
        exact add_comm _ _
  have hkY : (k : ℝ) ≤ 2 * y := by linarith
  have hk : k < h := by exact_mod_cast (show (k : ℝ) < h by linarith)
  obtain ⟨S, hS, hdepth⟩ := valiant_depth_reduction (by omega : 2 ≤ n) hΔ hordered hdegree hk
  refine ⟨S, 2 ^ (h - k), ?_, ?_, hdepth⟩
  · have hcost : S.card * h ≤ Δ * n * k :=
      (Nat.le_div_iff_mul_le (by exact_mod_cast hh0)).mp hS
    have hcostR : (S.card : ℝ) * h ≤ (Δ : ℝ) * n * k := by exact_mod_cast hcost
    have hcostX : (S.card : ℝ) * x ≤ 2 * Δ * n * y := by
      have h1 := mul_le_mul_of_nonneg_left hLo (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
      have h2 := mul_le_mul_of_nonneg_left hkY (by positivity : (0 : ℝ) ≤ Δ * n)
      nlinarith only [h1, h2, hcostR]
    change (S.card : ℝ) ≤ 2 * Δ * n / (x / y)
    rw [div_div_eq_mul_div]
    exact (le_div_iff₀ hx0).mpr (by nlinarith only [hcostX])
  · have hpow : 2 ^ h < 2 * n := by
      have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < n)
      have hh : h - 1 + 1 = h := by
        have : 0 < h := by exact_mod_cast hh0
        omega
      have heq : 2 ^ h = 2 ^ (h - 1) * 2 := by rw [← pow_succ, hh]
      rw [heq]
      change 2 ^ (h - 1) < n at hpred
      omega
    have hpowK : h ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) h
    have hmul : 2 ^ (h - k) * h ≤ 2 ^ h := by
      calc
        _ ≤ 2 ^ (h - k) * 2 ^ k := Nat.mul_le_mul_left _ hpowK
        _ = 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hk.le]
    have hmulR : ((2 ^ (h - k) : ℕ) : ℝ) * (h : ℝ) ≤ 2 * n := by
      exact_mod_cast hmul.trans hpow.le
    have hsmall : ((2 ^ (h - k) : ℕ) : ℝ) ≤ 2 * n / x := by
      apply (le_div_iff₀ hx0).mpr
      exact (mul_le_mul_of_nonneg_left hLo (by positivity)).trans hmulR
    apply hsmall.trans
    apply div_le_div_of_nonneg_left (by positivity)
      (by change 0 < x / y; positivity)
    exact (robustnessScale_bounds hn).2

/-- For each fixed exponent below one, the certified sampler depth eventually
exceeds every fixed multiple of its deletion-budget scale. This verifies the
optimality corollary's concluding claim `min {e,d} = e`. -/
theorem eventually_sampler_depth_dominates {ε c C : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * (ε * n / robustnessScale n) ≤ c * n / (Real.logb 2 n) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ := c * Real.log 2 / (C * ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall := (isLittleO_log_rpow_atTop (show 0 < 1 - ε by linarith)).bound hδ
  have hnat := ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    tendsto_natCast_atTop_atTop).eventually hsmall
  filter_upwards [eventually_ge_atTop (2 ^ 120), hnat] with n hn hlog
  let x := Real.logb 2 n
  have hx : 120 ≤ x := (log_parameters hn).1
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hL : 0 < robustnessScale n := by linarith [(robustnessScale_bounds hn).1]
  have hpow : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hlog' : Real.log x ≤ δ * x ^ (1 - ε) := by
    change ‖Real.log x‖ ≤ δ * ‖x ^ (1 - ε)‖ at hlog
    simpa only [Real.norm_eq_abs, abs_of_pos hlogx,
      abs_of_pos (Real.rpow_pos_of_pos hx0 (1 - ε))] using hlog
  have hcancel : x ^ (1 - ε) * x ^ ε = x := by
    rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  have hcoef : C * ε * Real.log x * x ^ ε ≤ c * Real.log 2 * x := by
    have hh := mul_le_mul_of_nonneg_right hlog' (show 0 ≤ C * ε * x ^ ε by positivity)
    have heq : δ * x ^ (1 - ε) * (C * ε * x ^ ε) = c * Real.log 2 * x := by
      dsimp [δ]
      field_simp
      nlinarith only [hcancel]
    rw [heq] at hh
    nlinarith only [hh]
  have hbase : C * ε / robustnessScale n ≤ c / x ^ ε := by
    change C * ε / (x / (Real.log x / Real.log 2)) ≤ c / x ^ ε
    rw [div_div_eq_mul_div]
    apply (div_le_div_iff₀ hx0 hpow).mpr
    apply (le_of_mul_le_mul_right _ hl2)
    have heq : C * ε * (Real.log x / Real.log 2) * x ^ ε * Real.log 2 =
        C * ε * Real.log x * x ^ ε := by field_simp
    rw [heq]
    nlinarith only [hcoef]
  have hh := mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  calc
    _ = (C * ε / robustnessScale n) * n := by ring
    _ ≤ (c / x ^ ε) * n := hh
    _ = _ := by dsimp [x]; ring

end ProofOfSpace.DRSample

namespace ProofOfSpaceStatement
open Finset Filter ProofOfSpace.DRSample

/-- Paper result `cor:balanced-robustness-optimality`: the universal balanced
upper bound and the strict width obstruction. The constant depends only on Δ. -/
theorem balanced_robustness_optimality (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ edge : Fin n → Fin n → Prop, IsOrdered edge → IndegreeAtMost edge Δ →
      ∀ e b : ℕ, 1 ≤ e → 1 ≤ b → ∀ d : ℝ, 0 < d →
        GraphBlockDepthRobust edge e d b →
        min (e : ℝ) d ≤ C * n / (Real.logb 2 n / Real.logb 2 (Real.logb 2 n)) ∧
          (b : ℝ) < (n : ℝ) / e := by
  refine ⟨2 * Δ, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ 120)] with n hn
  intro edge hordered hdegree e b he hb d _hd hrobust
  refine ⟨?_, block_width_lt (by omega) (by omega) (by omega) hrobust⟩
  obtain ⟨S, d', hS, hd', hdepth⟩ := balanced_reduction hn hΔ hordered hdegree
  by_cases hSe : S.card ≤ e
  · obtain ⟨path, _, hchain, hclean, hlen⟩ := hrobust S hSe
    have hpath : AvoidingPath edge S path := ⟨hchain, by
      intro u hu huS
      exact hclean u hu u huS ⟨le_rfl, by omega⟩⟩
    have hdd' : d ≤ (d' : ℝ) := hlen.trans (Nat.cast_le.mpr (hdepth path hpath))
    apply (min_le_right _ _).trans (hdd'.trans (hd'.trans _))
    have hL0 : 0 < robustnessScale n := by linarith [(robustnessScale_bounds hn).1]
    apply div_le_div_of_nonneg_right _ hL0.le
    have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast (show 1 ≤ Δ by omega)
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  · exact (min_le_left _ _).trans ((Nat.cast_le.mpr (by omega : e ≤ S.card)).trans hS)

end ProofOfSpaceStatement

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.ChungRegion
import ProofOfSpace.UnionBound
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Expansion probability for one permutation of the Chung ports

This file is deliberately separate from the deterministic pebbling development. It
counts one uniform permutation of `8n` ports, proves a fixed-pair estimate, and then
takes the union bound over the active source sizes.
-/

namespace ProofOfSpace
namespace Concrete

open Finset Set Real
open scoped ENNReal

/-! ### The sharp Stirling correction -/

/-- Robbins' stepwise estimate, summed to the Stirling limit. -/
theorem log_stirlingSeq_sub_limit_le {k : ℕ} (hk : 0 < k) :
    Real.log (Stirling.stirlingSeq k) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * (k : ℝ)) := by
  have hfinite : ∀ N : ℕ,
      Real.log (Stirling.stirlingSeq k) - Real.log (Stirling.stirlingSeq (k + N)) ≤
        1 / (12 * (k : ℝ)) := by
    intro N
    let f (j : ℕ) : ℝ := Real.log (Stirling.stirlingSeq (k + j))
    let g (j : ℕ) : ℝ := 1 / (12 * (k + j : ℕ))
    have hstep j (hj : j ∈ Finset.range N) : f j - f (j + 1) ≤ g j - g (j + 1) := by
      have hs := Stirling.log_stirlingSeq_sdiff_le (k + j)
      have hz : (0 : ℝ) < (k + j : ℕ) := by exact_mod_cast Nat.add_pos_left hk j
      have heq : (1 : ℝ) / (12 * (k + j : ℕ) * ((k + j : ℕ) + 1)) =
          1 / (12 * (k + j : ℕ)) - 1 / (12 * ((k + j : ℕ) + 1)) := by
        field_simp
        ring
      rw [heq] at hs
      dsimp only [f, g]
      convert hs using 1 <;> push_cast <;> ring_nf
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hsum
    simp only [f, g, Nat.add_zero] at hsum
    have hnonneg : 0 ≤ 1 / (12 * ((k + N : ℕ) : ℝ)) := by positivity
    exact hsum.trans (sub_le_self _ hnonneg)
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hlimS : Filter.Tendsto (fun N : ℕ => Stirling.stirlingSeq (k + N))
      Filter.atTop (nhds (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (by simpa [Nat.add_comm] using Filter.tendsto_add_atTop_nat k)
  have hlimLog : Filter.Tendsto
      (fun N : ℕ => Real.log (Stirling.stirlingSeq (k + N))) Filter.atTop
      (nhds (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt).tendsto.comp hlimS
  exact le_of_tendsto (tendsto_const_nhds.sub hlimLog)
    (Filter.Eventually.of_forall hfinite)

/-- Exact logarithmic form of the Stirling correction for a binomial coefficient. -/
theorem log_choose_eq_stirling {q k : ℕ} (hk : 0 < k) (hkq : k < q) :
    Real.log (q.choose k) =
      (q : ℝ) * Real.binEntropy ((k : ℝ) / q) -
        Real.log (2 * Real.pi * q * ((k : ℝ) / q) * (1 - (k : ℝ) / q)) / 2 +
      (Real.log (Stirling.stirlingSeq q) - Real.log (Stirling.stirlingSeq k) -
        Real.log (Stirling.stirlingSeq (q - k)) + Real.log Real.pi / 2) := by
  have hkqle : k ≤ q := hkq.le
  have hq : 0 < q := hk.trans hkq
  have hqk : 0 < q - k := Nat.sub_pos_of_lt hkq
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hkqle
  have hfac : ((q.choose k : ℕ) : ℝ) * (Nat.factorial k : ℝ) *
      (Nat.factorial (q - k) : ℝ) = (Nat.factorial q : ℝ) := by
    exact_mod_cast hfacNat
  have hlogfac : Real.log (q.choose k) = Real.log (Nat.factorial q) -
      Real.log (Nat.factorial k) - Real.log (Nat.factorial (q - k)) := by
    have hchoose : (0 : ℝ) < q.choose k := by exact_mod_cast Nat.choose_pos hkqle
    have hkfac : (0 : ℝ) < Nat.factorial k := by positivity
    have hqkfac : (0 : ℝ) < Nat.factorial (q - k) := by positivity
    have hlog := congrArg Real.log hfac
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hchoose) (ne_of_gt hkfac)) (ne_of_gt hqkfac),
      Real.log_mul (ne_of_gt hchoose) (ne_of_gt hkfac)] at hlog
    linarith
  have fq := Stirling.log_stirlingSeq_formula q
  have fk := Stirling.log_stirlingSeq_formula k
  have fqk := Stirling.log_stirlingSeq_formula (q - k)
  rw [hlogfac]
  rw [binEntropy_eq_neg]
  rw [Real.log_div (by positivity : (k : ℝ) ≠ 0) (by positivity : (q : ℝ) ≠ 0)]
  have hratio : 1 - (k : ℝ) / q = (q - k : ℕ) / (q : ℝ) := by
    rw [Nat.cast_sub hkqle]
    field_simp
  rw [hratio, Real.log_div (by positivity : ((q - k : ℕ) : ℝ) ≠ 0)
    (by positivity : (q : ℝ) ≠ 0)]
  rw [Real.log_mul (by positivity : (2 * Real.pi * (q : ℝ) * ((k : ℝ) / q)) ≠ 0)
      (by positivity : ((q - k : ℕ) : ℝ) / q ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi * (q : ℝ)) ≠ 0)
      (by positivity : (k : ℝ) / q ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi) ≠ 0) (by positivity : (q : ℝ) ≠ 0),
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  rw [Real.log_div (by positivity : (k : ℝ) ≠ 0) (by positivity : (q : ℝ) ≠ 0),
    Real.log_div (by positivity : ((q - k : ℕ) : ℝ) ≠ 0)
      (by positivity : (q : ℝ) ≠ 0)]
  have hqcast : ((q - k : ℕ) : ℝ) = (q : ℝ) - k := by
    exact Nat.cast_sub hkqle
  simp only [hqcast] at fqk ⊢
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : (q : ℝ) ≠ 0),
    Real.log_div (by positivity : (q : ℝ) ≠ 0) (by positivity : Real.exp 1 ≠ 0),
    Real.log_exp] at fq
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : (k : ℝ) ≠ 0),
    Real.log_div (by positivity : (k : ℝ) ≠ 0) (by positivity : Real.exp 1 ≠ 0),
    Real.log_exp] at fk
  have hqksub : (0 : ℝ) < (q : ℝ) - k := by exact_mod_cast hqk
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (ne_of_gt hqksub),
    Real.log_div (ne_of_gt hqksub) (by positivity : Real.exp 1 ≠ 0),
    Real.log_exp] at fqk
  field_simp
  linear_combination -2 * fq + 2 * fk + 2 * fqk

noncomputable def binomMainLog (q k : ℕ) : ℝ :=
  (q : ℝ) * Real.binEntropy ((k : ℝ) / q) -
    Real.log (2 * Real.pi * q * ((k : ℝ) / q) * (1 - (k : ℝ) / q)) / 2

private theorem log_stirlingSeq_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (Stirling.stirlingSeq b) ≤ Real.log (Stirling.stirlingSeq a) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  exact Stirling.log_stirlingSeq'_antitone (by omega)

private theorem log_sqrt_pi_le_log_stirlingSeq {a : ℕ} (ha : 0 < a) :
    Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq a) := by
  apply Real.log_le_log (by positivity)
  exact Stirling.sqrt_pi_le_stirlingSeq (ne_of_gt ha)

theorem log_choose_le_main {q k : ℕ} (hk : 0 < k) (hkq : k < q) :
    Real.log (q.choose k) ≤ binomMainLog q k := by
  rw [log_choose_eq_stirling hk hkq, binomMainLog]
  have hmono := log_stirlingSeq_antitone hk hkq.le
  have hsqrt := log_sqrt_pi_le_log_stirlingSeq (Nat.sub_pos_of_lt hkq)
  rw [Real.log_sqrt (le_of_lt Real.pi_pos)] at hsqrt
  linarith

/-- The denominator estimate needed for degree eight.  Both sides of the split are at
least eight, so Robbins' tail gives substantially more room than `1/8`. -/
theorem main_sub_one_eighth_le_log_choose {q k : ℕ} (hk8 : 8 ≤ k)
    (hqk8 : 8 ≤ q - k) :
    binomMainLog q k - 1 / 8 ≤ Real.log (q.choose k) := by
  have hk : 0 < k := by omega
  have hkq : k < q := Nat.lt_of_sub_pos (by omega)
  rw [log_choose_eq_stirling hk hkq, binomMainLog]
  have hsq := log_sqrt_pi_le_log_stirlingSeq (hk.trans_le hkq.le)
  have hsk := log_stirlingSeq_sub_limit_le hk
  have hsqk := log_stirlingSeq_sub_limit_le (Nat.sub_pos_of_lt hkq)
  rw [Real.log_sqrt (le_of_lt Real.pi_pos)] at hsq hsk hsqk
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hqkR : (8 : ℝ) ≤ ((q - k : ℕ) : ℝ) := by exact_mod_cast hqk8
  have hb1 : 1 / (12 * (k : ℝ)) ≤ 1 / 96 := by
    apply one_div_le_one_div_of_le <;> nlinarith
  have hb2 : 1 / (12 * ((q - k : ℕ) : ℝ)) ≤ 1 / 96 := by
    apply one_div_le_one_div_of_le <;> nlinarith
  linarith

/-- The four entropy main terms in the fixed-pair count, including their exact
square-root prefactor. -/
theorem portExpansion_main_identity {n k m : ℕ} (hk : 0 < k) (hkm : k < m) (hmn : m < n) :
    binomMainLog n k + binomMainLog n m + binomMainLog (8 * m) (8 * k) -
        binomMainLog (8 * n) (8 * k) =
      (n : ℝ) * chungExponent 8 ((k : ℝ) / n) ((m : ℝ) / n) - Real.log n -
        Real.log (2 * Real.pi) -
          Real.log (((k : ℝ) / n) * (1 - (m : ℝ) / n) *
            ((m : ℝ) / n - (k : ℝ) / n)) / 2 := by
  have hn : 0 < n := hk.trans (hkm.trans hmn)
  have hm : 0 < m := hk.trans hkm
  have hkn : k < n := hkm.trans hmn
  have h8k : (0 : ℝ) < 8 * k := by positivity
  have h8m : (0 : ℝ) < 8 * m := by positivity
  have h8n : (0 : ℝ) < 8 * n := by positivity
  unfold binomMainLog chungExponent
  push_cast
  have hknratio : (k : ℝ) / n / ((m : ℝ) / n) = (k : ℝ) / m := by field_simp
  have h8km : (8 * (k : ℝ)) / (8 * (m : ℝ)) = (k : ℝ) / m := by field_simp
  have h8kn : (8 * (k : ℝ)) / (8 * (n : ℝ)) = (k : ℝ) / n := by field_simp
  rw [hknratio, h8km, h8kn]
  have hx0 : (0 : ℝ) < (k : ℝ) / n := by positivity
  have hx1 : (k : ℝ) / n < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast hkn
  have hy0 : (0 : ℝ) < (m : ℝ) / n := by positivity
  have hy1 : (m : ℝ) / n < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast hmn
  have hz0 : (0 : ℝ) < (k : ℝ) / m := by positivity
  have hz1 : (k : ℝ) / m < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast hkm
  have hlogA : Real.log (2 * Real.pi * (n : ℝ) * ((k : ℝ) / n) *
      (1 - (k : ℝ) / n)) = Real.log 2 + Real.log Real.pi + Real.log n +
        Real.log ((k : ℝ) / n) + Real.log (1 - (k : ℝ) / n) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hlogB : Real.log (2 * Real.pi * (n : ℝ) * ((m : ℝ) / n) *
      (1 - (m : ℝ) / n)) = Real.log 2 + Real.log Real.pi + Real.log n +
        Real.log ((m : ℝ) / n) + Real.log (1 - (m : ℝ) / n) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hlogC : Real.log (2 * Real.pi * (8 * (m : ℝ)) * ((k : ℝ) / m) *
      (1 - (k : ℝ) / m)) = Real.log 2 + Real.log Real.pi + Real.log (8 * (m : ℝ)) +
        Real.log ((k : ℝ) / m) + Real.log (1 - (k : ℝ) / m) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hlogD : Real.log (2 * Real.pi * (8 * (n : ℝ)) * ((k : ℝ) / n) *
      (1 - (k : ℝ) / n)) = Real.log 2 + Real.log Real.pi + Real.log (8 * (n : ℝ)) +
        Real.log ((k : ℝ) / n) + Real.log (1 - (k : ℝ) / n) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hdiffpos : (0 : ℝ) < (m : ℝ) / n - (k : ℝ) / n := by
    apply sub_pos.mpr
    exact div_lt_div_of_pos_right (by exact_mod_cast hkm) (by exact_mod_cast hn)
  have hlogR : Real.log (((k : ℝ) / n) * (1 - (m : ℝ) / n) *
      ((m : ℝ) / n - (k : ℝ) / n)) = Real.log ((k : ℝ) / n) +
        Real.log (1 - (m : ℝ) / n) +
          Real.log ((m : ℝ) / n - (k : ℝ) / n) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hdiffpos),
      Real.log_mul (by positivity) (by positivity)]
  rw [hlogA, hlogB, hlogC, hlogD, hlogR,
    Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0),
    Real.log_mul (by positivity : (8 : ℝ) ≠ 0) (by positivity : (m : ℝ) ≠ 0),
    Real.log_mul (by positivity : (8 : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  have hzcomp : 1 - (k : ℝ) / m = ((m - k : ℕ) : ℝ) / m := by
    rw [Nat.cast_sub hkm.le]
    field_simp
  have hdiff : (m : ℝ) / n - (k : ℝ) / n = ((m - k : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hkm.le]
    ring
  have hmkne : ((m - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hkm))
  rw [hzcomp, hdiff,
    Real.log_div hmkne (by positivity : (m : ℝ) ≠ 0),
    Real.log_div hmkne (by positivity : (n : ℝ) ≠ 0),
    Real.log_div (by positivity : (k : ℝ) ≠ 0) (by positivity : (m : ℝ) ≠ 0),
    Real.log_div (by positivity : (m : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0),
    Real.log_div (by positivity : (k : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
  field_simp
  ring

noncomputable def portExpansionPairMass (n k m : ℕ) : ℝ :=
  (n.choose k : ℝ) * (n.choose m : ℝ) *
    ((8 * m).choose (8 * k) : ℝ) / ((8 * n).choose (8 * k) : ℝ)

theorem log_portExpansionPairMass_le {n k m : ℕ} (hk : 0 < k) (hkm : k < m) (hmn : m < n) :
    Real.log (portExpansionPairMass n k m) ≤
      (n : ℝ) * chungExponent 8 ((k : ℝ) / n) ((m : ℝ) / n) - Real.log n -
        Real.log (2 * Real.pi) -
          Real.log (((k : ℝ) / n) * (1 - (m : ℝ) / n) *
            ((m : ℝ) / n - (k : ℝ) / n)) / 2 + 1 / 8 := by
  have hkn : k < n := hkm.trans hmn
  have h8km : 8 * k < 8 * m := by omega
  have h8kn : 8 * k < 8 * n := by omega
  have hc1 : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn.le
  have hc2 : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hmn.le
  have hc3 : (0 : ℝ) < (8 * m).choose (8 * k) := by
    exact_mod_cast Nat.choose_pos h8km.le
  have hc4 : (0 : ℝ) < (8 * n).choose (8 * k) := by
    exact_mod_cast Nat.choose_pos h8kn.le
  have hlog : Real.log (portExpansionPairMass n k m) =
      Real.log (n.choose k) + Real.log (n.choose m) + Real.log ((8 * m).choose (8 * k)) -
        Real.log ((8 * n).choose (8 * k)) := by
    unfold portExpansionPairMass
    rw [Real.log_div (ne_of_gt (mul_pos (mul_pos hc1 hc2) hc3)) (ne_of_gt hc4),
      Real.log_mul (ne_of_gt (mul_pos hc1 hc2)) (ne_of_gt hc3),
      Real.log_mul (ne_of_gt hc1) (ne_of_gt hc2)]
  rw [hlog]
  have h1 := log_choose_le_main hk hkn
  have h2 := log_choose_le_main (hk.trans hkm) hmn
  have h3 := log_choose_le_main (Nat.mul_pos (by omega) hk) h8km
  have h4 := main_sub_one_eighth_le_log_choose (q := 8 * n) (k := 8 * k)
    (by omega) (by omega)
  calc
    Real.log (n.choose k) + Real.log (n.choose m) + Real.log ((8 * m).choose (8 * k)) -
        Real.log ((8 * n).choose (8 * k)) ≤
      binomMainLog n k + binomMainLog n m + binomMainLog (8 * m) (8 * k) -
        binomMainLog (8 * n) (8 * k) + 1 / 8 := by linarith
    _ = (n : ℝ) * chungExponent 8 ((k : ℝ) / n) ((m : ℝ) / n) - Real.log n -
        Real.log (2 * Real.pi) -
          Real.log (((k : ℝ) / n) * (1 - (m : ℝ) / n) *
            ((m : ℝ) / n - (k : ℝ) / n)) / 2 + 1 / 8 := by
      rw [portExpansion_main_identity hk hkm hmn]

/-- The fixed-pair estimate with the interval-wise prefactor used by the union bound. -/
theorem portExpansionPairMass_le {n k m : ℕ} {a Δ ε : ℝ}
    (hk : 0 < k) (hkm : k < m) (hmn : m < n) (ha : 0 < a) (hΔ : 0 < Δ)
    (hxa : a ≤ (k : ℝ) / n) (hya : a ≤ 1 - (m : ℝ) / n)
    (hgap : Δ ≤ (m : ℝ) / n - (k : ℝ) / n)
    (hexp : chungExponent 8 ((k : ℝ) / n) ((m : ℝ) / n) ≤ -ε * Real.log 2) :
    portExpansionPairMass n k m ≤
      Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt Δ) *
        Real.exp (-(n : ℝ) * ε * Real.log 2) / n := by
  have hn : 0 < n := hk.trans (hkm.trans hmn)
  have hx : (0 : ℝ) < (k : ℝ) / n := by positivity
  have hyc : (0 : ℝ) < 1 - (m : ℝ) / n := ha.trans_le hya
  have hxy : (0 : ℝ) < (m : ℝ) / n - (k : ℝ) / n := hΔ.trans_le hgap
  have hprod : a * a * Δ ≤
      ((k : ℝ) / n) * (1 - (m : ℝ) / n) *
        ((m : ℝ) / n - (k : ℝ) / n) := by
    exact mul_le_mul (mul_le_mul hxa hya ha.le hx.le) hgap hΔ.le
      (mul_nonneg hx.le hyc.le)
  have hlogprod := Real.log_le_log (mul_pos (mul_pos ha ha) hΔ) hprod
  have hmasspos : 0 < portExpansionPairMass n k m := by
    unfold portExpansionPairMass
    have hc1 : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (hkm.trans hmn).le
    have hc2 : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hmn.le
    have hc3 : (0 : ℝ) < (8 * m).choose (8 * k) := by
      exact_mod_cast Nat.choose_pos (by omega : 8 * k ≤ 8 * m)
    have hc4 : (0 : ℝ) < (8 * n).choose (8 * k) := by
      exact_mod_cast Nat.choose_pos (by omega : 8 * k ≤ 8 * n)
    positivity
  have hlogmass := log_portExpansionPairMass_le hk hkm hmn
  have hsqrt : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔ
  have htarget : 0 < Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt Δ) *
      Real.exp (-(n : ℝ) * ε * Real.log 2) / n := by positivity
  rw [← Real.exp_log hmasspos, ← Real.exp_log htarget]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt hΔ.le]
  have hloga : Real.log (a * a * Δ) = 2 * Real.log a + Real.log Δ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hloga] at hlogprod
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)] at hlogmass
  have hnexp := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg n)
  linarith

theorem hitProb_eq_choose_div_choose {Q K M : ℕ} :
    hitProb Q K M = (M.choose K : ℝ≥0∞) / (Q.choose K : ℝ≥0∞) := by
  rw [hitProb, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  exact ENNReal.mul_div_mul_left _ _ (by simp [Nat.factorial_ne_zero]) (by simp)

theorem portTerm_eq_ofReal_pairMass {n k m : ℕ} (_hk : 0 < k)
    (hkm : k < m) (hmn : m < n) :
    (n.choose k : ℝ≥0∞) * ((n.choose m : ℝ≥0∞) *
      hitProb (8 * n) (8 * k) (8 * m)) = ENNReal.ofReal (portExpansionPairMass n k m) := by
  rw [hitProb_eq_choose_div_choose]
  have hc1 : (0 : ℝ) ≤ n.choose k := by positivity
  have hc2 : (0 : ℝ) ≤ n.choose m := by positivity
  have hc3 : (0 : ℝ) ≤ (8 * m).choose (8 * k) := by positivity
  have hc4 : (0 : ℝ) < (8 * n).choose (8 * k) := by
    exact_mod_cast Nat.choose_pos (by omega : 8 * k ≤ 8 * n)
  unfold portExpansionPairMass
  rw [ENNReal.ofReal_div_of_pos hc4, ENNReal.ofReal_mul (mul_nonneg hc1 hc2),
    ENNReal.ofReal_mul hc1]
  simp only [ENNReal.ofReal_natCast]
  simp [div_eq_mul_inv, mul_assoc]

namespace PortInterlayer

/-- Expansion against an integer failure profile, restricted to a density interval. -/
def ExpandsProfileOn (P : PortInterlayer n) (a b : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ T : Finset (Fin n), a ≤ (T.card : ℝ) / n → (T.card : ℝ) / n ≤ b →
    m T.card < (P.neighborhood T).card

/-- `N(T) ⊆ U` is equivalent to the port permutation carrying every port of `T`
into a port belonging to `U`. -/
theorem neighborhood_subset_iff (P : PortInterlayer n) (T U : Finset (Fin n)) :
    P.neighborhood T ⊆ U ↔ ∀ q ∈ ports T, P.perm q ∈ ports U := by
  classical
  simp only [neighborhood, ports, Finset.subset_iff, Finset.mem_image,
    Finset.mem_product, Finset.mem_univ, true_and]
  constructor
  · rintro h q hq
    exact h ⟨q, hq, rfl⟩
  · rintro h x ⟨q, hq, rfl⟩
    exact h q hq

theorem card_portInterlayer (n : ℕ) :
    Fintype.card (PortInterlayer n) = Nat.factorial (8 * n) := by
  rw [show Fintype.card (PortInterlayer n) =
      Fintype.card (Equiv.Perm (Fin 8 × Fin n)) by
    apply Fintype.card_congr
    exact ⟨PortInterlayer.perm, fun p => ⟨p⟩, fun P => by cases P; rfl, fun _ => rfl⟩,
    Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The fixed-pair probability in the one-permutation port model. -/
theorem prob_neighborhood_subset_le (T U : Finset (Fin n)) (hT : T.card ≤ n) :
    probabilityOf (PortInterlayer.uniformLaw n) (fun P => P.neighborhood T ⊆ U)
      ≤ hitProb (8 * n) (8 * T.card) (8 * U.card) := by
  classical
  rw [PortInterlayer.uniformLaw, probabilityOf_uniformOfFintype, card_portInterlayer]
  have hports : 8 * T.card ≤ 8 * n := Nat.mul_le_mul_left 8 hT
  have hcount := card_maps_le' (ports T) (ports U)
    ((Finset.univ.filter fun P : PortInterlayer n => P.neighborhood T ⊆ U).image
      PortInterlayer.perm) (fun qperm hqperm => by
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hqperm
        exact (neighborhood_subset_iff P T U).1 (Finset.mem_filter.1 hP).2)
  have hinj : Function.Injective (@PortInterlayer.perm n) := by
    intro P Q h
    cases P; cases Q
    simpa using h
  have himage :
      ((Finset.univ.filter fun P : PortInterlayer n => P.neighborhood T ⊆ U).image
        PortInterlayer.perm).card =
      (Finset.univ.filter fun P : PortInterlayer n => P.neighborhood T ⊆ U).card :=
    Finset.card_image_of_injective _ hinj
  rw [himage, card_ports, card_ports, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hcount
  have hfac : (8 * n).descFactorial (8 * T.card) *
      Nat.factorial (8 * n - 8 * T.card) = Nat.factorial (8 * n) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.mul_comm (Nat.factorial (8 * T.card)) ((8 * n).choose (8 * T.card))]
    exact Nat.choose_mul_factorial_mul_factorial hports
  have hne : (Nat.factorial (8 * n - 8 * T.card) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (8 * n - 8 * T.card)
  have hnt : (Nat.factorial (8 * n - 8 * T.card) : ℝ≥0∞) ≠ ⊤ := by simp
  refine le_trans (ENNReal.div_le_div_right (b :=
    (↑((8 * U.card).descFactorial (8 * T.card) *
      Nat.factorial (8 * n - 8 * T.card)) : ℝ≥0∞)) ?_ _) ?_
  · exact_mod_cast hcount
  · rw [hitProb, ← hfac]
    push_cast
    exact (ENNReal.mul_div_mul_right _ _ hne hnt).le

end PortInterlayer

/-- A failed profile has a source set whose neighbourhood can be padded to the profile
size. -/
theorem exists_port_cover_of_not_expandsProfileOn {m : ℕ → ℕ} (hmn : ∀ k, m k ≤ n)
    (P : PortInterlayer n) (hP : ¬ P.ExpandsProfileOn a b m) :
    ∃ T : Finset (Fin n), a ≤ (T.card : ℝ) / n ∧ (T.card : ℝ) / n ≤ b ∧
      ∃ U ∈ Finset.univ.powersetCard (m T.card), P.neighborhood T ⊆ U := by
  classical
  rw [PortInterlayer.ExpandsProfileOn] at hP
  push Not at hP
  obtain ⟨T, ha, hb, hcard⟩ := hP
  obtain ⟨U, hsub, hU, hUcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (P.neighborhood T)) hcard (by simpa using hmn T.card)
  exact ⟨T, ha, hb, U, Finset.mem_powersetCard.2 ⟨hU, hUcard⟩, hsub⟩

/-- The exact port-model union bound, before applying Stirling's estimate. -/
theorem portExpansion_failure_le (n : ℕ) (a b : ℝ) (m : ℕ → ℕ)
    (ha : 0 < a) (hmn : ∀ k, m k ≤ n) :
    probabilityOf (PortInterlayer.uniformLaw n)
      (fun P => ¬ P.ExpandsProfileOn a b m) ≤
      ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
          (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b),
        (n.choose k : ℝ≥0∞) * ((n.choose (m k) : ℝ≥0∞) *
          hitProb (8 * n) (8 * k) (8 * m k)) := by
  classical
  let p := PortInterlayer.uniformLaw n
  let active : ℕ → Prop := fun k => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b
  let R : Finset (Fin n) → PortInterlayer n → Prop := fun T P =>
    active T.card ∧ ∃ U ∈ Finset.univ.powersetCard (m T.card), P.neighborhood T ⊆ U
  have hstage1 : probabilityOf p (fun P => ¬ P.ExpandsProfileOn a b m) ≤
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => active T.card),
        probabilityOf p (R T) :=
    probabilityOf_le_sum p _ _ R fun P hP => by
      obtain ⟨T, ha, hb, U, hU, hsub⟩ := exists_port_cover_of_not_expandsProfileOn hmn P hP
      exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, hb⟩, ⟨⟨ha, hb⟩, U, hU, hsub⟩⟩
  have hstage2 : ∀ T : Finset (Fin n), probabilityOf p (R T) ≤
      (n.choose (m T.card) : ℝ≥0∞) * hitProb (8 * n) (8 * T.card) (8 * m T.card) := by
    intro T
    by_cases hactive : active T.card
    · have hsplit : probabilityOf p (R T) ≤
          ∑ U ∈ Finset.univ.powersetCard (m T.card),
            probabilityOf p (fun P => P.neighborhood T ⊆ U) :=
        probabilityOf_le_sum p _ _ _ fun P hP => by
          obtain ⟨_, U, hU, hsub⟩ := hP
          exact ⟨U, hU, hsub⟩
      refine hsplit.trans ?_
      have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
      have hterm : ∀ U ∈ Finset.univ.powersetCard (m T.card),
          probabilityOf p (fun P => P.neighborhood T ⊆ U) ≤
            hitProb (8 * n) (8 * T.card) (8 * m T.card) := by
        intro U hU
        have hUcard : U.card = m T.card := (Finset.mem_powersetCard.1 hU).2
        simpa [p, hUcard] using PortInterlayer.prob_neighborhood_subset_le T U hTn
      refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    · have hfalse : ∀ P, ¬ R T P := fun P h => hactive h.1
      simp only [probabilityOf, hfalse, if_false, tsum_zero]
      exact bot_le
  refine hstage1.trans ?_
  refine (Finset.sum_le_sum fun T _ => hstage2 T).trans ?_
  let g : ℕ → ℝ≥0∞ := fun k =>
    (n.choose (m k) : ℝ≥0∞) * hitProb (8 * n) (8 * k) (8 * m k)
  have hregroup := sum_over_nonempty_finsets (n := n)
    (fun k => if active k then g k else 0)
  have hzero : ¬ active 0 := by
    intro h
    have := h.1
    simp only [Nat.cast_zero, zero_div] at this
    linarith
  have hleft :
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => active T.card), g T.card =
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => T.Nonempty),
        if active T.card then g T.card else 0 := by
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hact : active T.card
    · have hne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        subst T
        exact hzero hact
      simp [hact, hne]
    · simp [hact]
  rw [hleft, hregroup]
  simp only [g]
  rw [Finset.sum_filter]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro k hk
  simp only [active]
  by_cases hact : a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b
  · simp [hact]
  · simp [hact]

/-- The `1/n` in each fixed-size estimate cancels against at most `n` active source
sizes. The hypotheses isolate the integer-rounding facts needed by a concrete profile. -/
theorem portExpansion_failure_le_exponential (n : ℕ) (a b Δ ε : ℝ) (m : ℕ → ℕ)
    (hn : 0 < n) (ha : 0 < a) (hΔ : 0 < Δ) (hmn : ∀ k, m k ≤ n)
    (hprofile : ∀ k : ℕ, a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b →
      0 < k ∧ k < m k ∧ m k < n ∧
      a ≤ 1 - (m k : ℝ) / n ∧
      Δ ≤ (m k : ℝ) / n - (k : ℝ) / n ∧
      chungExponent 8 ((k : ℝ) / n) ((m k : ℝ) / n) ≤ -ε * Real.log 2) :
    probabilityOf (PortInterlayer.uniformLaw n)
      (fun P => ¬ P.ExpandsProfileOn a b m) ≤
    ENNReal.ofReal (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt Δ) *
      Real.exp (-(n : ℝ) * ε * Real.log 2)) := by
  let B : ℝ := Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt Δ) *
    Real.exp (-(n : ℝ) * ε * Real.log 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine (portExpansion_failure_le n a b m ha hmn).trans ?_
  have hterm : ∀ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b),
      (n.choose k : ℝ≥0∞) * ((n.choose (m k) : ℝ≥0∞) *
        hitProb (8 * n) (8 * k) (8 * m k)) ≤ ENNReal.ofReal (B / n) := by
    intro k hk
    have hactive := (Finset.mem_filter.1 hk).2
    obtain ⟨hk0, hkm, hmn', hya, hgap, hexp⟩ := hprofile k hactive
    rw [portTerm_eq_ofReal_pairMass hk0 hkm hmn']
    apply ENNReal.ofReal_le_ofReal
    simpa only [B] using portExpansionPairMass_le hk0 hkm hmn' ha hΔ hactive.1 hya hgap hexp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b)).card ≤ n := by
    calc
      _ ≤ (Finset.Ico 1 (n + 1)).card := Finset.card_filter_le _ _
      _ = n := by simp
  calc
    ↑((Finset.Ico 1 (n + 1)).filter
        (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b)).card *
        ENNReal.ofReal (B / n) ≤ (n : ℝ≥0∞) * ENNReal.ofReal (B / n) := by
      gcongr
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      field_simp

theorem portExpansion_whp_exponential (n : ℕ) (a b Δ ε : ℝ) (m : ℕ → ℕ)
    (hn : 0 < n) (ha : 0 < a) (hΔ : 0 < Δ) (hmn : ∀ k, m k ≤ n)
    (hprofile : ∀ k : ℕ, a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b →
      0 < k ∧ k < m k ∧ m k < n ∧
      a ≤ 1 - (m k : ℝ) / n ∧
      Δ ≤ (m k : ℝ) / n - (k : ℝ) / n ∧
      chungExponent 8 ((k : ℝ) / n) ((m k : ℝ) / n) ≤ -ε * Real.log 2) :
    HoldsWithFailureAtMost (PortInterlayer.uniformLaw n)
      (fun P => P.ExpandsProfileOn a b m)
      (ENNReal.ofReal (Real.exp (1 / 8) / (2 * Real.pi * a * Real.sqrt Δ) *
        Real.exp (-(n : ℝ) * ε * Real.log 2))) :=
  holdsWithFailureAtMost_of_compl_le _ _
    (portExpansion_failure_le_exponential n a b Δ ε m hn ha hΔ hmn hprofile)

end Concrete
end ProofOfSpace

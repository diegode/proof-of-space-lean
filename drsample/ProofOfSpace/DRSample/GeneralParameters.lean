import ProofOfSpace.DRSample.GeneralBlocks
import ProofOfSpace.DRSample.AsymptoticRobustness

namespace ProofOfSpace.DRSample
open Finset Filter

set_option maxHeartbeats 800000 in
-- The rounded parameters are bounded uniformly in both laws and exponents.
/-- The full parameter selection, including any prescribed product fraction. -/
theorem eventually_avoidance_product {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n : ℕ in atTop, 2 ^ 120 ≤ n ∧ ∃ e b : ℕ,
        c * (ε * n / robustnessScale n) ≤ e ∧
        (e : ℝ) ≤ C * (ε * n / robustnessScale n) ∧
        c * (robustnessScale n / ε) ≤ b ∧
        (b : ℝ) ≤ C * (robustnessScale n / ε) ∧
        β * n ≤ (e : ℝ) * b ∧
        ∀ p : ℕ → FiniteLaw (Finset (Fin n)),
          (∀ v < n, ∀ U : Finset (Fin n),
            (p v).probability (fun parents => Disjoint parents U) ≤
              Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ u ∈ U, harmonicAt n v u)) →
          (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
            BlockDepthRobust (incomingGraph sets) e (c * n / (Real.logb 2 n) ^ ε) b) ≥
            1 - Real.exp (-c * (ε * n / robustnessScale n)) := by
  let δ := 1 - β
  let α := (1 + β) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  let k := multiscaleConstant α hα hα1
  have hk : 0 < k := multiscaleConstant_pos α hα hα1
  let K := 1 + k
  let D := 20 * (K + 1)
  let A := 8 / δ
  let H := (A + 1) * D
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  let c := min (α / (4 * (H + D))) (min 1 (min (9 / (40 * k)) (1 / (4 * D))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcE : c ≤ α / (4 * (H + D)) := min_le_left _ _
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcDepth : c ≤ 9 / (40 * k) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcFail : c ≤ 1 / (4 * D) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, H + 1, hc, by positivity, ?_⟩
  intro ε hε hε1
  let Q := 1 + 4 * D + 4 * (H + D) / α + 8 * (H + 3 * D) / δ + 4 * D * (D + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQE : 0 ≤ 4 * (H + D) / α := by positivity
  have hQP : 0 ≤ 8 * (H + 3 * D) / δ := by positivity
  have hQF : 0 ≤ 4 * D * (D + 1) := by positivity
  filter_upwards [eventually_scale_small_const Q hQ hε] with n hn
  let q := robustnessScale n / ε
  let x := Real.logb 2 n
  have hx : 120 ≤ x := (log_parameters hn.1).1
  have hx0 : 0 < x := by linarith
  have hL := robustnessScale_bounds hn.1
  have hL0 : 0 < robustnessScale n := by linarith [hL.1]
  have hq : 1 ≤ q := (le_div_iff₀ hε).mpr (by linarith [hL.1])
  have hq0 : 0 < q := by linarith
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : ε * n / robustnessScale n = (n : ℝ) / q := by dsimp [q]; field_simp
  have hsmall : Q * q ^ 2 ≤ n := hn.2
  have hterm (z : ℝ) (hz : 0 ≤ z) (hzQ : z ≤ Q) : z * q ≤ (n : ℝ) :=
    (mul_le_mul_of_nonneg_left hq2 hz).trans
      ((mul_le_mul_of_nonneg_right hzQ (sq_nonneg q)).trans hsmall)
  have hDsmall : 4 * D * q ≤ (n : ℝ) := hterm _ (by positivity) (by dsimp [Q]; linarith only [hD, hQE, hQP, hQF])
  have hEsmall : (4 * (H + D) / α) * q ≤ (n : ℝ) :=
    hterm _ (by positivity) (by dsimp [Q]; linarith only [hD, hQE, hQP, hQF])
  have hProdSmall : (8 * (H + 3 * D) / δ) * q ≤ (n : ℝ) :=
    hterm _ (by positivity) (by dsimp [Q]; linarith only [hD, hQE, hQP, hQF])
  have hFailSmall : (4 * D * (D + 1)) * q ^ 2 ≤ (n : ℝ) :=
    (mul_le_mul_of_nonneg_right (show 4 * D * (D + 1) ≤ Q by dsimp [Q]; linarith only [hD, hQE, hQP, hQF])
      (sq_nonneg q)).trans hsmall
  let a := Nat.ceil (K * q)
  let B : ℝ := 20 * a
  let b := Nat.ceil (A * B)
  let e := Nat.floor (α * ((n : ℝ) - 2 * B) / (b + B))
  have haLo : K * q ≤ (a : ℝ) := Nat.le_ceil _
  have haHi : (a : ℝ) < K * q + 1 := Nat.ceil_lt_add_one (by positivity)
  have ha : 0 < a := by exact_mod_cast (show (0 : ℝ) < a by nlinarith only [haLo, hK, hq])
  have hBLo : 20 * K * q ≤ B := by dsimp [B]; nlinarith only [haLo]
  have hBHi : B ≤ D * q := by dsimp [B, D]; nlinarith only [haHi, hq]
  have hB1 : 1 ≤ B := by nlinarith only [hBLo, hK, hq]
  have hB0 : 0 < B := by linarith
  have hBsmall : 4 * B ≤ (n : ℝ) := by linarith
  have hnB : 2 * (20 * a) < n := by
    exact_mod_cast (show 2 * (20 * (a : ℝ)) < n by change 2 * B < n; linarith)
  have hbLo : A * B ≤ (b : ℝ) := Nat.le_ceil _
  have hbHi : (b : ℝ) < A * B + 1 := Nat.ceil_lt_add_one (by positivity)
  have hb : 0 < b := by exact_mod_cast (show (0 : ℝ) < b by positivity)
  have hbH : (b : ℝ) ≤ H * q := by
    have h := mul_le_mul_of_nonneg_left hBHi (show 0 ≤ A + 1 by positivity)
    dsimp [H]
    nlinarith only [h, hbHi, hB1]
  have hden : 0 < (b : ℝ) + B := by positivity
  have hcomplete : (n : ℝ) / 2 ≤ (n : ℝ) - 2 * B := by linarith
  have hremain : 0 ≤ (n : ℝ) - 2 * B := by linarith only [hcomplete, hn0]
  have heHi : (e : ℝ) ≤ α * ((n : ℝ) - 2 * B) / (b + B) :=
    Nat.floor_le (by positivity)
  have heLo : α * ((n : ℝ) - 2 * B) / (b + B) - 1 < (e : ℝ) :=
    Nat.sub_one_lt_floor _
  have hbudget : (e : ℝ) * (b + B) ≤ α * ((n : ℝ) - 2 * B) :=
    (le_div_iff₀ hden).mp heHi
  have heLower : α / (4 * (H + D)) * ((n : ℝ) / q) ≤ e := by
    have hbase : α * (n : ℝ) / (2 * ((H + D) * q)) ≤
        α * ((n : ℝ) - 2 * B) / (b + B) := by
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      have hdenHi : (b : ℝ) + B ≤ (H + D) * q := by nlinarith only [hbH, hBHi]
      have hmul := mul_le_mul_of_nonneg_left hdenHi (by positivity : 0 ≤ α * (n : ℝ))
      have hmul2 := mul_le_mul_of_nonneg_left hcomplete (by positivity : 0 ≤ 2 * α * ((H + D) * q))
      nlinarith only [hmul, hmul2]
    have htwo : 2 ≤ α * (n : ℝ) / (2 * ((H + D) * q)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hEsmall hα.le
      field_simp at hh
      nlinarith only [hh]
    have heq : α / (4 * (H + D)) * ((n : ℝ) / q) =
        (α * (n : ℝ) / (2 * ((H + D) * q))) / 2 := by field_simp <;> ring
    rw [heq]
    linarith
  have hbudgetN : (e : ℝ) * (b + B) ≤ (n : ℝ) := by
    apply hbudget.trans
    calc
      _ ≤ α * n := mul_le_mul_of_nonneg_left (by linarith only [hB0]) hα.le
      _ ≤ n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hα1.le hn0.le
  have heUpper : (e : ℝ) ≤ (n : ℝ) / q := by
    apply (le_div_iff₀ hq0).mpr
    have hpos : 0 ≤ (e : ℝ) := Nat.cast_nonneg e
    have hbpos : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    have hmul := mul_le_mul_of_nonneg_left (show q ≤ (b : ℝ) + B by nlinarith only [hBLo, hK, hq, hbpos]) hpos
    exact hmul.trans hbudgetN
  have hproduct : β * n ≤ (e : ℝ) * b := by
    have heMul : α * ((n : ℝ) - 2 * B) < ((e : ℝ) + 1) * (b + B) :=
      (div_lt_iff₀ hden).mp (by linarith : α * ((n : ℝ) - 2 * B) / (b + B) < e + 1)
    have heB : (e : ℝ) * B ≤ (n : ℝ) / A := by
      apply (le_div_iff₀ hA).mpr
      have hmul := mul_le_mul_of_nonneg_left hbLo (Nat.cast_nonneg e)
      have heBpos := mul_nonneg (Nat.cast_nonneg e : (0 : ℝ) ≤ e) hB0.le
      nlinarith only [hmul, hbudgetN, heBpos]
    have hcost : (b : ℝ) + 3 * B ≤ δ * n / 8 := by
      have hm := mul_le_mul_of_nonneg_left hProdSmall hδ.le
      field_simp at hm
      nlinarith only [hm, hbH, hBHi]
    have hnA : (n : ℝ) / A = δ * n / 8 := by dsimp [A]; field_simp
    rw [hnA] at heB
    have hgap : β + δ / 2 = α := by dsimp [α, δ]; ring
    nlinarith only [heMul, heB, hcost, hgap, hα1, hα, hB0, hδ, hn0]
  refine ⟨hn.1, e, b, ?_, ?_, ?_, ?_, hproduct, ?_⟩
  · rw [hratio]
    exact (mul_le_mul_of_nonneg_right hcE (by positivity)).trans heLower
  · rw [hratio]
    exact heUpper.trans (le_mul_of_one_le_left (by positivity) (by linarith))
  · change c * q ≤ b
    have hA1 : 1 ≤ A := by dsimp [A, δ]; apply (le_div_iff₀ hδ).mpr; linarith
    have hqB : q ≤ B := by nlinarith only [hBLo, hK, hq]
    calc
      c * q ≤ q := by simpa using mul_le_mul_of_nonneg_right hc1 hq0.le
      _ ≤ B := hqB
      _ ≤ A * B := le_mul_of_one_le_left hB0.le hA1
      _ ≤ b := hbLo
  · change (b : ℝ) ≤ (H + 1) * q
    nlinarith only [hbH, hq]
  intro p havoid
  have heta : 0 < 1 / (x + 1) := by positivity
  have hfinite := finite_avoidance_fraction hα hα1 ha hnB p heta havoid
  dsimp only at hfinite
  push_cast at hfinite
  have hdepth : c * n / x ^ ε ≤
      (9 / (20 * k)) * ((n : ℝ) - 2 * B) * Real.exp (-7 * k / ((1 / (x + 1)) * B)) := by
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqEq : q * (ε * Real.log x) = x * Real.log 2 := by
      change (x / (Real.log x / Real.log 2) / ε) * (ε * Real.log x) = x * Real.log 2
      field_simp
    have hcoef : 7 * k / ((1 / (x + 1)) * B) ≤ ε * Real.log x := by
      apply (div_le_iff₀ (by positivity)).mpr
      rw [one_div_mul_eq_div, ← mul_div_assoc, le_div_iff₀ (by linarith : 0 < x + 1)]
      have hm := mul_le_mul_of_nonneg_right hBLo (by positivity : 0 ≤ ε * Real.log x)
      have heq : 20 * K * q * (ε * Real.log x) = 20 * K * (x * Real.log 2) := by rw [mul_assoc, hqEq]
      rw [heq] at hm
      have hl2 := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
        (by positivity : 0 ≤ 20 * K * x)
      have hlast : 7 * k * (x + 1) ≤ 10 * K * x := by
        dsimp [K]
        nlinarith only [hx, hk]
      nlinarith only [hm, hl2, hlast]
    have hexp : (x ^ ε)⁻¹ ≤ Real.exp (-7 * k / ((1 / (x + 1)) * B)) := by
      rw [Real.rpow_def_of_pos hx0, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have hn := neg_le_neg hcoef
      simpa only [neg_div, neg_mul, mul_comm (Real.log x)] using hn
    rw [div_eq_mul_inv]
    apply mul_le_mul _ hexp (by positivity) (by positivity)
    have hcoef := mul_le_mul_of_nonneg_right hcDepth hn0.le
    have hlen := mul_le_mul_of_nonneg_left hcomplete (by positivity : 0 ≤ (9 : ℝ) / (20 * k))
    calc
      _ ≤ 9 / (40 * k) * n := hcoef
      _ = 9 / (20 * k) * ((n : ℝ) / 2) := by field_simp <;> ring
      _ ≤ _ := hlen
  have hfailure : B * Real.exp (-(2 - Real.log 3) * ((n : ℝ) / B - 2)) ≤
      Real.exp (-c * (ε * n / robustnessScale n)) := by
    have hkap : (1 / 2 : ℝ) ≤ 2 - Real.log 3 := by
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
      have hl4 := Real.log_pow (2 : ℝ) 2
      norm_num at hl4
      linarith [Real.log_two_lt_d9]
    have hlogB : Real.log B ≤ B := (Real.log_le_sub_one_of_pos hB0).trans (by linarith)
    have hnB4 : (4 : ℝ) ≤ (n : ℝ) / B := (le_div_iff₀ hB0).mpr hBsmall
    have hquot : (n : ℝ) / (D * q) ≤ (n : ℝ) / B :=
      div_le_div_of_nonneg_left hn0.le hB0 hBHi
    have hcost : B + 1 ≤ (n : ℝ) / (4 * D * q) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hBHi (by positivity : 0 ≤ 4 * D * q)
      have hql := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ 4 * D)
      nlinarith only [hm, hFailSmall, hql]
    have hm := mul_le_mul_of_nonneg_right hkap (by linarith : 0 ≤ (n : ℝ) / B - 2)
    have hcf := mul_le_mul_of_nonneg_right hcFail (by positivity : 0 ≤ (n : ℝ) / q)
    have hexponent : Real.log B - (2 - Real.log 3) * ((n : ℝ) / B - 2) ≤
        -c * (ε * n / robustnessScale n) := by
      rw [hratio]
      have heq : (n : ℝ) / (D * q) = 4 * ((n : ℝ) / (4 * D * q)) := by ring
      have heq2 : 1 / (4 * D) * ((n : ℝ) / q) = (n : ℝ) / (4 * D * q) := by ring
      rw [heq] at hquot
      rw [heq2] at hcf
      linarith only [hlogB, hm, hquot, hcost, hcf]
    calc
      _ = Real.exp (Real.log B - (2 - Real.log 3) * ((n : ℝ) / B - 2)) := by
        rw [Real.exp_sub, Real.exp_log hB0, neg_mul, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  have hbound := (show 1 - Real.exp (-c * (ε * n / robustnessScale n)) ≤
      1 - B * Real.exp (-(2 - Real.log 3) * ((n : ℝ) / B - 2)) by linarith only [hfailure]).trans hfinite
  apply hbound.trans
  apply FiniteLaw.probability_mono
  intro sets hs
  exact (hs e b hb hbudget).mono le_rfl hdepth

end ProofOfSpace.DRSample

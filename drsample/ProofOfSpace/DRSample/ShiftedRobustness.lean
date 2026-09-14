import ProofOfSpace.DRSample.TriangularGraph
import ProofOfSpace.DRSample.ShiftedBlocks
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The finite avoidance criterion, simultaneously over all endpoint budgets -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem multiscale_kappa_pos : 0 < (8 / 5 : ℝ) - Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [h]
  linarith [Real.log_two_lt_d9]

theorem shifted_full_blocks {n B : ℕ} (hB : 0 < B) (hn : 2 * B < n) (t : Fin B) :
    0 < (n - t.val) / B ∧ t.val + ((n - t.val) / B) * B ≤ n ∧
      (n : ℝ) / B - 2 ≤ ((n - t.val) / B : ℕ) := by
  have ht := t.isLt
  have htN : t.val ≤ n := by omega
  have hm := Nat.div_mul_le_self (n - t.val) B
  have hd := Nat.mod_add_div (n - t.val) B
  have hr := Nat.mod_lt (n - t.val) hB
  refine ⟨Nat.div_pos (by omega) hB, by omega, ?_⟩
  have hN : n ≤ (((n - t.val) / B) + 2) * B := by
    nlinarith [Nat.sub_add_cancel htN]
  have hNR : (n : ℝ) ≤ (((n - t.val) / B : ℕ) + 2) * B := by exact_mod_cast hN
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hdiv := (div_le_iff₀ hBR).mpr hNR
  linarith

/-- The paper's finite bound: deterministic lifting through the first intact
half-block avoids an additive rounding loss. -/
theorem finite_avoidance_robustness {n a : ℕ} (ha : 0 < a) (hn : 2 * (20 * a) < n)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      ∀ e b : ℕ, 0 < b →
        (e : ℝ) * (b + 20 * a) ≤ ((n : ℝ) - 2 * (20 * a)) / 3 →
        BlockDepthRobust (incomingGraph sets) e
          ((9 / 40 : ℝ) * ((n : ℝ) - 2 * (20 * a)) *
            Real.exp (-323 / (eta * (20 * a)))) b) ≥
      1 - (20 * a : ℕ) * Real.exp (-((8 / 5 : ℝ) - Real.log 4) *
        ((n : ℝ) / (20 * a) - 2)) := by
  let B := 20 * a
  have hB : 0 < B := by dsimp [B]; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  let M (t : Fin B) := (n - t.val) / B
  have hfull (t : Fin B) := shifted_full_blocks hB hn t
  let good (t : Fin B) (sets : Fin n → Finset (Fin n)) :=
    DepthRobust (triangleGraph (hfull t).2.1 sets) (M t / 3)
      ((M t / 2 : ℝ) * Real.exp (-323 / (eta * (20 * a))))
  let law := FiniteLaw.pi (fun v : Fin n => p v.val)
  have hbad (t : Fin B) : law.probability (fun sets => ¬ good t sets) ≤
      Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) := by
    have h := triangleGraph_robustness ha (hfull t).1 (hfull t).2.1 p heta havoid
    push_cast at h
    have hcomp := law.probability_compl (good t)
    have hmono : Real.exp (-((8 / 5 : ℝ) - Real.log 4) * (M t)) ≤
        Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hfull t).2.2 (by linarith [multiscale_kappa_pos])
    change 1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * (M t)) ≤
      law.probability (good t) at h
    linarith
  have hunion := law.probability_exists_le_sum (fun t sets => ¬ good t sets)
  have hfail : law.probability (fun sets => ∃ t, ¬ good t sets) ≤
      (B : ℝ) * Real.exp (-((8 / 5 : ℝ) - Real.log 4) * ((n : ℝ) / B - 2)) := by
    apply hunion.trans
    simpa using sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin B))) => hbad t)
  have hgood : 1 - (B : ℝ) * Real.exp (-((8 / 5 : ℝ) - Real.log 4) *
      ((n : ℝ) / B - 2)) ≤ law.probability (fun sets => ∀ t, good t sets) := by
    have hcomp := law.probability_compl (fun sets => ∃ t, ¬ good t sets)
    simp only [not_exists, not_not] at hcomp
    linarith
  dsimp [B] at hgood
  push_cast at hgood ⊢
  apply hgood.trans
  apply law.probability_mono
  intro sets hs e b hb he T hT
  obtain ⟨t, ht⟩ := exists_shiftedDiscarded_le_average hB hb M T
  have hcount : (shiftedDiscarded t.val B (M t) (blockDeleted b T)).card ≤ M t / 3 := by
    have hT' : (T.card : ℝ) ≤ e := by exact_mod_cast hT
    have hbcast : ((B + b - 1 : ℕ) : ℝ) ≤ (b : ℝ) + B := by
      exact_mod_cast (show B + b - 1 ≤ b + B by omega)
    have havg : (T.card : ℝ) * (B + b - 1 : ℕ) / B ≤
        (e : ℝ) * (b + B) / B := by
      apply div_le_div_of_nonneg_right _ hBR.le
      exact mul_le_mul hT' hbcast (by positivity) (by positivity)
    have he' : (e : ℝ) * (b + B) / B ≤ ((n : ℝ) / B - 2) / 3 := by
      calc
        _ ≤ (((n : ℝ) - 2 * B) / 3) / B := by
          apply div_le_div_of_nonneg_right _ hBR.le
          simpa only [B, Nat.cast_mul, Nat.cast_ofNat] using he
        _ = _ := by field_simp [hBR.ne']
    have hMbound := div_le_div_of_nonneg_right (hfull t).2.2 (by norm_num : (0 : ℝ) ≤ 3)
    have hthree : 3 * (shiftedDiscarded t.val B (M t) (blockDeleted b T)).card ≤ M t := by
      have h := ht.trans (havg.trans (he'.trans hMbound))
      exact_mod_cast (show (3 : ℝ) * (shiftedDiscarded t.val B (M t) (blockDeleted b T)).card ≤ M t by linarith)
    omega
  have hpath := (hs t) _ hcount
  have hlift := lift_triangle_path ha (hfull t).2.1 (incomingGraph sets)
    (triangleGraph (hfull t).2.1 sets) (incomingGraph_hasLine sets)
    (triangleGraph_edge_port ha (hfull t).2.1 sets) (blockDeleted b T)
    (by have := (hfull t).1; positivity) hpath
  apply hlift.mono_length
  have hMB : (n : ℝ) - 2 * B ≤ (M t : ℝ) * B := by
    have h := (hfull t).2.2
    have h := (div_le_iff₀ hBR).mp (show (n : ℝ) / B ≤ (M t : ℝ) + 2 by linarith)
    linarith
  have h := mul_le_mul_of_nonneg_right hMB
    (Real.exp_pos (-323 / (eta * (20 * a)))).le
  dsimp [B] at h
  push_cast at h ⊢
  nlinarith

/-- The earlier rounded-height bound, retained as a relaxation of
`finite_avoidance_robustness`. -/
theorem finite_avoidance_paper {n a : ℕ} (ha : 0 < a) (hn : 2 * (20 * a) < n)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      ∀ e b : ℕ, 0 < b →
        (e : ℝ) * (b + 20 * a) ≤ ((n : ℝ) - 2 * (20 * a)) / 3 →
        BlockDepthRobust (incomingGraph sets) e
          ((9 / 40 : ℝ) * (((n : ℝ) - 2 * (20 * a)) *
            Real.exp (-323 / (eta * (20 * a))) - 2 * (20 * a))) b) ≥
      1 - (20 * a : ℕ) * Real.exp (-((8 / 5 : ℝ) - Real.log 4) *
        ((n : ℝ) / (20 * a) - 2)) := by
  apply (finite_avoidance_robustness ha hn p heta havoid).trans
  apply FiniteLaw.probability_mono
  intro sets hs e b hb he
  apply (hs e b hb he).mono le_rfl
  nlinarith

end ProofOfSpace.DRSample

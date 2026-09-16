import ProofOfSpace.DRSample.GeneralMultiscale
import ProofOfSpace.DRSample.ShiftedRobustness

namespace ProofOfSpace.DRSample
open Finset

noncomputable def multiscaleConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
  (multiscale_fraction hα hα1).choose

theorem multiscaleConstant_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < multiscaleConstant α hα hα1 := (multiscale_fraction hα hα1).choose_spec.1

theorem triangleGraph_robustness_fraction {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {n t a M : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hn : t + M * (20 * a) ≤ n) (p : ℕ → FiniteLaw (Finset (Fin n)))
    {eta : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    let c := multiscaleConstant α hα hα1
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      DepthRobust (triangleGraph hn sets) (Nat.floor (α * M))
        ((M : ℝ) / c * Real.exp (-7 * c / (eta * (20 * a : ℕ))))) ≥
      1 - Real.exp (-(2 - Real.log 3) * M) := by
  dsimp only
  let c := multiscaleConstant α hα hα1
  have hc : 0 < c := multiscaleConstant_pos α hα hα1
  rw [triangleGraph_probability ha hn p
    (fun G => DepthRobust G (Nat.floor (α * M))
      ((M : ℝ) / c * Real.exp (-7 * c / (eta * (20 * a : ℕ)))))]
  have h := (multiscale_fraction hα hα1).choose_spec.2 M hM
    (fun j => (triangleRowLaw t a p j).map (triangleParents hn j))
    (eta * (119 / 800 : ℝ) * (20 * a : ℕ)) (by positivity) (by
      intro j hj A
      rw [FiniteLaw.probability_map]
      exact triangleParents_avoidance ha hn hj p heta.le havoid A)
  rw [independentSamples_map_probability] at h
  apply h.trans
  apply FiniteLaw.probability_mono
  intro s hs
  apply hs.mono le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (M : ℝ) / c)
  apply Real.exp_le_exp.mpr
  change -7 * c / (eta * (20 * a : ℕ)) ≤ -c / (eta * (119 / 800) * (20 * a : ℕ))
  have hB : (0 : ℝ) < (20 * a : ℕ) := by positivity
  field_simp
  nlinarith

theorem general_multiscale_kappa_pos : 0 < (2 : ℝ) - Real.log 3 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
  have hlog4 := Real.log_pow (2 : ℝ) 2
  norm_num at hlog4
  linarith [Real.log_two_lt_d9]

/-- The paper's finite bound: deterministic lifting through the first intact
half-block avoids an additive rounding loss. -/
theorem finite_avoidance_fraction {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {n a : ℕ} (ha : 0 < a) (hn : 2 * (20 * a) < n)
    (p : ℕ → FiniteLaw (Finset (Fin n))) {eta : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    let c := multiscaleConstant α hα hα1
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      ∀ e b : ℕ, 0 < b →
        (e : ℝ) * (b + 20 * a) ≤ α * ((n : ℝ) - 2 * (20 * a)) →
        BlockDepthRobust (incomingGraph sets) e
          ((9 / (20 * c) : ℝ) * ((n : ℝ) - 2 * (20 * a)) *
            Real.exp (-7 * c / (eta * (20 * a)))) b) ≥
      1 - (20 * a : ℕ) * Real.exp (-(2 - Real.log 3) *
        ((n : ℝ) / (20 * a) - 2)) := by
  dsimp only
  let c := multiscaleConstant α hα hα1
  have hc : 0 < c := multiscaleConstant_pos α hα hα1
  let B := 20 * a
  have hB : 0 < B := by dsimp [B]; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  let M (t : Fin B) := (n - t.val) / B
  have hfull (t : Fin B) := shifted_full_blocks hB hn t
  let good (t : Fin B) (sets : Fin n → Finset (Fin n)) :=
    DepthRobust (triangleGraph (hfull t).2.1 sets) (Nat.floor (α * M t))
      (((M t : ℝ) / c) * Real.exp (-7 * c / (eta * (20 * a))))
  let law := FiniteLaw.pi (fun v : Fin n => p v.val)
  have hbad (t : Fin B) : law.probability (fun sets => ¬ good t sets) ≤
      Real.exp (-(2 - Real.log 3) * ((n : ℝ) / B - 2)) := by
    have h := triangleGraph_robustness_fraction hα hα1 ha (hfull t).1 (hfull t).2.1 p heta havoid
    push_cast at h
    have hcomp := law.probability_compl (good t)
    have hmono : Real.exp (-(2 - Real.log 3) * (M t)) ≤
        Real.exp (-(2 - Real.log 3) * ((n : ℝ) / B - 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hfull t).2.2 (by linarith [general_multiscale_kappa_pos])
    change 1 - Real.exp (-(2 - Real.log 3) * (M t)) ≤
      law.probability (good t) at h
    linarith
  have hunion := law.probability_exists_le_sum (fun t sets => ¬ good t sets)
  have hfail : law.probability (fun sets => ∃ t, ¬ good t sets) ≤
      (B : ℝ) * Real.exp (-(2 - Real.log 3) * ((n : ℝ) / B - 2)) := by
    apply hunion.trans
    simpa using sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin B))) => hbad t)
  have hgood : 1 - (B : ℝ) * Real.exp (-(2 - Real.log 3) *
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
  have hcount : (shiftedDiscarded t.val B (M t) (blockDeleted b T)).card ≤ Nat.floor (α * M t) := by
    have hT' : (T.card : ℝ) ≤ e := by exact_mod_cast hT
    have hbcast : ((B + b - 1 : ℕ) : ℝ) ≤ (b : ℝ) + B := by
      exact_mod_cast (show B + b - 1 ≤ b + B by omega)
    have havg : (T.card : ℝ) * (B + b - 1 : ℕ) / B ≤
        (e : ℝ) * (b + B) / B := by
      apply div_le_div_of_nonneg_right _ hBR.le
      exact mul_le_mul hT' hbcast (by positivity) (by positivity)
    have he' : (e : ℝ) * (b + B) / B ≤ α * ((n : ℝ) / B - 2) := by
      calc
        _ ≤ (α * ((n : ℝ) - 2 * B)) / B := by
          apply div_le_div_of_nonneg_right _ hBR.le
          simpa only [B, Nat.cast_mul, Nat.cast_ofNat] using he
        _ = _ := by field_simp [hBR.ne']
    have hMbound := mul_le_mul_of_nonneg_left (hfull t).2.2 hα.le
    apply (Nat.le_floor_iff (by positivity : 0 ≤ α * M t)).mpr
    exact ht.trans (havg.trans (he'.trans hMbound))
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
    (Real.exp_pos (-7 * c / (eta * (20 * a)))).le
  dsimp [B] at h
  push_cast at h ⊢
  change 9 / (20 * c) * ((n : ℝ) - 2 * (20 * a)) *
    Real.exp (-7 * c / (eta * (20 * a))) ≤
    9 * (a : ℝ) * ((M t : ℝ) / c * Real.exp (-7 * c / (eta * (20 * a))))
  calc
    _ = 9 / (20 * c) * (((n : ℝ) - 2 * (20 * a)) *
        Real.exp (-7 * c / (eta * (20 * a)))) := by ring
    _ ≤ 9 / (20 * c) * ((M t : ℝ) * (20 * a) *
        Real.exp (-7 * c / (eta * (20 * a)))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hc.ne']

end ProofOfSpace.DRSample

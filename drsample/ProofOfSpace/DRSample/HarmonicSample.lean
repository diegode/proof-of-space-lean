import ProofOfSpace.DRSample.Samplers
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # HarmonicSample with an arbitrary positive number of independent draws -/
namespace ProofOfSpace.DRSample
open Finset Classical

/-- The normalization of edge lengths `2,…,v`, namely `H_v - 1`. -/
noncomputable def harmonicNormalizer (v : ℕ) : ℝ := ∑ s ∈ Icc 2 v, (1 : ℝ) / s

theorem harmonicNormalizer_eq {v : ℕ} (hv : 1 ≤ v) :
    harmonicNormalizer v = (harmonic v : ℝ) - 1 := by
  have h := sum_erase_add (Icc 1 v) (fun s : ℕ => (s : ℝ)⁻¹)
    (left_mem_Icc.mpr hv)
  have he : (Icc 1 v).erase 1 = Icc 2 v := by ext s; simp; omega
  rw [he] at h
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simpa [harmonicNormalizer, one_div] using (eq_sub_iff_add_eq.mpr h)

theorem harmonicNormalizer_pos {v : ℕ} (hv : 2 ≤ v) : 0 < harmonicNormalizer v := by
  apply sum_pos' (fun s _ => by positivity)
  exact ⟨2, mem_Icc.mpr ⟨le_rfl, hv⟩, by norm_num⟩

theorem harmonicNormalizer_le_log {v n : ℕ} (hv : 2 ≤ v) (hvn : v ≤ n) :
    harmonicNormalizer v ≤ Real.log n := by
  rw [harmonicNormalizer_eq (by omega)]
  have h := harmonic_le_one_add_log v
  have hlog : Real.log (v : ℝ) ≤ Real.log n := Real.log_le_log
    (by exact_mod_cast (show 0 < v by omega)) (by exact_mod_cast hvn)
  linarith

theorem harmonic_parent_sum {n v : ℕ} (hv : v < n) :
    (∑ u : Fin n, if u.val + 2 ≤ v then (1 : ℝ) / (v - u.val : ℕ) else 0) =
      harmonicNormalizer v := by
  rw [← sum_filter]
  apply sum_bij (fun u _ => v - u.val)
  · intro u hu
    have hu := (mem_filter.mp hu).2
    exact mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩
  · intro u hu w hw he
    have hu := (mem_filter.mp hu).2
    have hw := (mem_filter.mp hw).2
    apply Fin.ext
    omega
  · intro s hs
    obtain ⟨hs2, hsv⟩ := mem_Icc.mp hs
    refine ⟨⟨v - s, by omega⟩, mem_filter.mpr ⟨mem_univ _, by dsimp; omega⟩, ?_⟩
    dsimp
    omega
  · intros; rfl

/-- An exact harmonic parent draw; vertices zero and one use a dummy parent. -/
noncomputable def harmonicParentLaw {n : ℕ} (hn : 0 < n) (v : ℕ) : FiniteLaw (Fin n) :=
  if hv : v < n then
    if hv2 : 2 ≤ v then
      { weight := fun u => if u.val + 2 ≤ v then
          ((1 : ℝ) / (v - u.val : ℕ)) / harmonicNormalizer v else 0
        nonneg := fun u => by
          have hpos := harmonicNormalizer_pos hv2
          split_ifs <;> positivity
        total := by
          have h := harmonic_parent_sum hv
          have he : (∑ u : Fin n, if u.val + 2 ≤ v then
              ((1 : ℝ) / (v - u.val : ℕ)) / harmonicNormalizer v else 0) =
              (∑ u : Fin n, if u.val + 2 ≤ v then
                ((1 : ℝ) / (v - u.val : ℕ)) else 0) / harmonicNormalizer v := by
            rw [sum_div]
            apply sum_congr rfl
            intro u _
            split_ifs <;> simp
          rw [he, h, div_self (harmonicNormalizer_pos hv2).ne'] }
    else FiniteLaw.pure ⟨0, hn⟩
  else FiniteLaw.pure ⟨0, hn⟩

theorem harmonicParentLaw_weight_ge {n : ℕ} (hn : 0 < n) {v : ℕ} (hv : v < n)
    (u : Fin n) (hu : u.val + 2 ≤ v) :
    (1 / Real.log n) / (v - u.val : ℕ) ≤ (harmonicParentLaw hn v).weight u := by
  have hv2 : 2 ≤ v := by omega
  rw [harmonicParentLaw, dif_pos hv, dif_pos hv2]
  dsimp only
  rw [if_pos hu]
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hr : (0 : ℝ) < (v - u.val : ℕ) := by exact_mod_cast (show 0 < v - u.val by omega)
  calc (1 / Real.log n) / (v - u.val : ℕ) =
      (1 / (v - u.val : ℕ)) / Real.log n := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (harmonicNormalizer_pos hv2)
      (harmonicNormalizer_le_log hv2 hv.le)

noncomputable def harmonicIncomingLaw {n : ℕ} (hn : 0 < n) (r v : ℕ) :
    FiniteLaw (Finset (Fin n)) := parentSetLaw r v (harmonicParentLaw hn v)

/-- The paper's harmonic avoidance coefficient is `r / ln n`. -/
theorem harmonicIncomingLaw_avoidance {n : ℕ} (hn : 2 ≤ n) (r : ℕ)
    {v : ℕ} (hv : v < n) (A : Finset (Fin n)) :
    (harmonicIncomingLaw (by omega) r v).probability (fun parents => Disjoint parents A) ≤
      Real.exp (-((r : ℝ) / Real.log n) * ∑ i ∈ A, harmonicAt n v i) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  simpa [harmonicIncomingLaw, div_eq_mul_inv] using
    parentSetLaw_avoidance_harmonic (d := r) (harmonicParentLaw (by omega) v)
      (by positivity) (harmonicParentLaw_weight_ge (by omega) hv) A

end ProofOfSpace.DRSample

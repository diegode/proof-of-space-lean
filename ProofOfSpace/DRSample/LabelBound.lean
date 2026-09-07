import ProofOfSpace.DRSample.HarmonicSubsequence

/-! # From inconsistent comparison mass to a depth lower bound -/
namespace ProofOfSpace.DRSample
open Finset

/-- Finite Jensen inequality for the exponential, proved from its tangent line. -/
theorem card_mul_exp_neg_average_le {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (c : α → ℝ) :
    (s.card : ℝ) * Real.exp (-(∑ j ∈ s, c j) / s.card) ≤ ∑ j ∈ s, Real.exp (-c j) := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  let avg : ℝ := (∑ j ∈ s, c j) / s.card
  have hsum (j : α) : Real.exp (-avg) * (1 + avg - c j) ≤ Real.exp (-c j) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (avg - c j))
      (Real.exp_pos (-avg)).le
    rw [← Real.exp_add, show -avg + (avg - c j) = -c j by ring] at h
    nlinarith
  have hall := sum_le_sum (s := s) (fun j _ => hsum j)
  have havg : (s.card : ℝ) * avg = ∑ j ∈ s, c j := by
    dsimp [avg]
    field_simp
  rw [← mul_sum, sum_sub_distrib] at hall
  simp only [sum_const, nsmul_eq_mul] at hall
  have hexp : Real.exp (-avg) = Real.exp (-(∑ j ∈ s, c j) / s.card) := by
    dsimp [avg]
    congr 1
    ring
  rw [← hexp]
  have hcancel : (s.card : ℝ) * (1 + avg) - (∑ j ∈ s, c j) = s.card := by nlinarith
  rw [hcancel] at hall
  simpa only [mul_comm] using hall

/-- A set of retained indices with bounded total inconsistent mass certifies a
large range of integer depth labels. This is the deterministic step after holes
have been removed and rank distances have been compared. -/
theorem depth_bound_of_inconsistent_mass (h : ℕ → ℕ) (lo hi : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Ico lo hi) (d : ℕ) (hh : ∀ i ∈ T, 1 ≤ h i ∧ h i ≤ d)
    (g W : ℝ) (hg : 0 < g) (hW : 0 ≤ W) (hcard : g ≤ T.card)
    (hmass : ∑ j ∈ T, inconsistentCost (fun i => (h i : ℝ)) lo hi j ≤ 4 * W) :
    g * Real.exp (-4 * W / g) ≤ d := by
  have hTpos : (0 : ℝ) < T.card := hg.trans_le hcard
  have hTne : T.Nonempty := card_pos.mp (by exact_mod_cast hTpos)
  have hjensen := card_mul_exp_neg_average_le T hTne
    (fun j => inconsistentCost (fun i => (h i : ℝ)) lo hi j)
  have hsubseq := sum_exp_inconsistentCost_le_capacity (fun i => (h i : ℝ)) lo hi T hT
  have hcap : (increasingCapacity (fun i => (h i : ℝ)) T : ℝ) ≤ d := by
    exact_mod_cast increasingCapacity_nat_le h T d hh
  have hexp1 : Real.exp (-4 * W / g) ≤ Real.exp (-4 * W / T.card) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ hg hTpos).mpr
    nlinarith
  have hexp2 : Real.exp (-4 * W / T.card) ≤
      Real.exp (-(∑ j ∈ T, inconsistentCost (fun i => (h i : ℝ)) lo hi j) / T.card) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hTpos.le
    linarith
  calc g * Real.exp (-4 * W / g)
      ≤ (T.card : ℝ) * Real.exp (-4 * W / T.card) :=
        mul_le_mul hcard hexp1 (Real.exp_pos _).le hTpos.le
    _ ≤ (T.card : ℝ) * Real.exp (-(∑ j ∈ T, inconsistentCost (fun i => (h i : ℝ)) lo hi j) / T.card) :=
      mul_le_mul_of_nonneg_left hexp2 hTpos.le
    _ ≤ ∑ j ∈ T, Real.exp (-inconsistentCost (fun i => (h i : ℝ)) lo hi j) := hjensen
    _ ≤ (increasingCapacity (fun i => (h i : ℝ)) T : ℝ) := hsubseq
    _ ≤ d := hcap

/-- Exact constants in the finite multiscale theorem. -/
theorem multiscale_scalar {M d : ℕ} {lambda g W : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hW : 0 ≤ W)
    (hg : 3 * M / 4 ≤ g) (hmass : W ≤ 4 * M / lambda)
    (hdepth : g * Real.exp (-4 * W / g) ≤ d) :
    (3 * M / 4 : ℝ) * Real.exp (-64 / (3 * lambda)) ≤ d := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hg0 : 0 < g := by linarith
  have hratio : -64 / (3 * lambda) ≤ -4 * W / g := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * lambda) hg0).mpr
    have hm := (le_div_iff₀ hlambda).mp hmass
    nlinarith
  have he := Real.exp_le_exp.mpr hratio
  exact (mul_le_mul hg he (Real.exp_pos _).le hg0.le).trans hdepth

end ProofOfSpace.DRSample

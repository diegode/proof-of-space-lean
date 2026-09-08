import ProofOfSpace.DRSample.SequentialMass

/-! # The finite multiscale theorem

The only sampler hypothesis is harmonic avoidance at each destination. The
sample space is an explicit product, so distinct destinations are independent.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

def natDeleted {M : ℕ} (S : Finset (Fin M)) : Finset ℕ := S.image Fin.val

@[simp] theorem natDeleted_card {M : ℕ} (S : Finset (Fin M)) :
    (natDeleted S).card = S.card := card_image_of_injective _ Fin.val_injective

theorem natDeleted_subset {M : ℕ} (S : Finset (Fin M)) : natDeleted S ⊆ range M := by
  intro j hj
  obtain ⟨i, _, rfl⟩ := mem_image.mp hj
  exact mem_range.mpr i.isLt

@[simp] theorem mem_natDeleted {M : ℕ} (S : Finset (Fin M)) (v : Fin M) :
    v.val ∈ natDeleted S ↔ v ∈ S := by
  simp [natDeleted, Fin.val_injective.eq_iff]

noncomputable def actualMass {M : ℕ} (S : Finset (Fin M))
    (s : SampleSpace (Finset (Fin M)) M) : ℝ :=
  forbiddenMass (range M \ natDeleted S) (exposedLabels (natDeleted S) M s)

theorem actualMass_moment {M : ℕ} (p : ℕ → FiniteLaw (Finset (Fin M)))
    {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) (S : Finset (Fin M)) :
    (independentSamples p M).expectation (fun s => Real.exp (lambda / 2 * actualMass S s)) ≤
      2 ^ (M - S.card) := by
  have hmoment := accumulated_moment p (exposedIncrement (natDeleted S)) (lambda / 2)
    (fun j => if j ∈ natDeleted S ∨ M ≤ j then 1 else 2)
    (fun j => by split_ifs <;> norm_num)
    (exposedIncrement_moment p (natDeleted S) hlambda havoid) M
  simp_rw [accumulated_eq_forbiddenMass (natDeleted S) _ le_rfl] at hmoment
  have hprod : (∏ j ∈ range M, if j ∈ natDeleted S ∨ M ≤ j then (1 : ℝ) else 2) =
      2 ^ (M - S.card) := by
    calc
      _ = ∏ j ∈ range M, if j ∉ natDeleted S then (2 : ℝ) else 1 := by
        apply prod_congr rfl
        intro j hj
        have hjM := mem_range.mp hj
        by_cases hjs : j ∈ natDeleted S <;> simp [hjs, Nat.not_le.mpr hjM]
      _ = ∏ j ∈ (range M).filter (fun j => j ∉ natDeleted S), (2 : ℝ) := by rw [prod_filter]
      _ = 2 ^ (M - S.card) := by
        have heq : (range M).filter (fun j => j ∉ natDeleted S) = range M \ natDeleted S := by ext j; simp
        rw [heq, prod_const, card_sdiff, inter_eq_left.mpr (natDeleted_subset S), card_range, natDeleted_card]
  rw [hprod] at hmoment
  exact hmoment

noncomputable def labelDepth {M : ℕ} (S : Finset (Fin M))
    (s : SampleSpace (Finset (Fin M)) M) : ℕ :=
  univ.sup (fun v : Fin M => exposedLabels (natDeleted S) M s v.val)

theorem path_of_le_labelDepth {M : ℕ} (S : Finset (Fin M))
    (s : SampleSpace (Finset (Fin M)) M) {d : ℝ} (hd : 0 < d)
    (hle : d ≤ labelDepth S s) : HasPath (exposedGraph M s) S d := by
  have hpos : 0 < labelDepth S s := by exact_mod_cast hd.trans_le hle
  obtain ⟨v, _, hv⟩ := (Finset.le_sup_iff hpos).mp (le_refl (labelDepth S s))
  obtain ⟨P, hne, hchain, havoid, _, hlen⟩ :=
    exposedLabels_path (natDeleted S) s le_rfl v (hpos.trans_le hv)
  refine ⟨P, hne, hchain, ?_, ?_⟩
  · intro u hu
    simpa using havoid u hu
  · rw [hlen]
    exact hle.trans (by exact_mod_cast hv)

theorem depth_of_mass_bound {M : ℕ} (hM : 0 < M) {lambda : ℝ} (hlambda : 0 < lambda)
    (S : Finset (Fin M)) (hS : S.card ≤ M / 48)
    (s : SampleSpace (Finset (Fin M)) M) (hmass : actualMass S s ≤ 4 * M / lambda) :
    HasPath (exposedGraph M s) S ((3 * M / 4 : ℝ) * Real.exp (-64 / (3 * lambda))) := by
  have h48 : 48 * S.card ≤ M := by omega
  have hsmall : 12 * (natDeleted S).card < M := by rw [natDeleted_card]; omega
  have hlabels : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := shallow_labels (natDeleted_subset S) hsmall
    (exposedLabels (natDeleted S) M s) hlabels
  have hg : (3 * M / 4 : ℝ) ≤ ((M - 12 * (natDeleted S).card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsmall.le, natDeleted_card, Nat.cast_mul, Nat.cast_ofNat]
    have h48R : (48 : ℝ) * S.card ≤ M := by exact_mod_cast h48
    linarith
  have hbound := multiscale_scalar hM hlambda (forbiddenMass_nonneg _ _) hg hmass hshallow
  exact path_of_le_labelDepth S s (by positivity) hbound

/-- With exponentially high probability the sampled graph is depth robust
simultaneously against every deletion of at most one forty-eighth of its vertices. -/
theorem multiscale {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 48)
        ((3 * M / 4 : ℝ) * Real.exp (-64 / (3 * lambda)))) ≥
      1 - Real.exp (-(2 - Real.log 3) * M) := by
  have hmass := (independentSamples p M).uniform_mass_bound M lambda hlambda actualMass
    (actualMass_moment p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  exact depth_of_mass_bound hM hlambda S hS s (hs S)

theorem depth_of_mass_bound_wide {M : ℕ} (hM : 0 < M) {lambda : ℝ}
    (hlambda : 0 < lambda) (S : Finset (Fin M)) (hS : S.card ≤ M / 24)
    (s : SampleSpace (Finset (Fin M)) M)
    (hmass : actualMass S s ≤ 8 * M / (3 * lambda)) :
    HasPath (exposedGraph M s) S ((M / 2 : ℝ) * Real.exp (-64 / (3 * lambda))) := by
  have h24 : 24 * S.card ≤ M := by omega
  have hsmall : 12 * (natDeleted S).card < M := by rw [natDeleted_card]; omega
  have hlabels : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := shallow_labels (natDeleted_subset S) hsmall
    (exposedLabels (natDeleted S) M s) hlabels
  have hg : (M / 2 : ℝ) ≤ ((M - 12 * (natDeleted S).card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsmall.le, natDeleted_card, Nat.cast_mul, Nat.cast_ofNat]
    have h24R : (24 : ℝ) * S.card ≤ M := by exact_mod_cast h24
    linarith
  have hbound := multiscale_scalar_wide hM hlambda (forbiddenMass_nonneg _ _) hg hmass hshallow
  exact path_of_le_labelDepth S s (by positivity) hbound

/-- A deletion-heavy form of `multiscale`.  It tolerates twice the deletion
fraction at the cost of a `2/3` prefactor and a smaller, still exponential,
success exponent. -/
theorem multiscale_wide {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 24)
        ((M / 2 : ℝ) * Real.exp (-64 / (3 * lambda)))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have hmass := (independentSamples p M).uniform_mass_bound_wide M lambda hlambda actualMass
    (actualMass_moment p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  exact depth_of_mass_bound_wide hM hlambda S hS s (hs S)

theorem depth_of_mass_bound_third {M : ℕ} (hM : 0 < M) {lambda : ℝ}
    (hlambda : 0 < lambda) (S : Finset (Fin M)) (hS : S.card ≤ M / 3)
    (s : SampleSpace (Finset (Fin M)) M)
    (hmass : actualMass S s ≤ 8 * M / (3 * lambda)) :
    HasPath (exposedGraph M s) S ((M / 6 : ℝ) * Real.exp (-160 / lambda)) := by
  have hlabels : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := shallow_labels_third (natDeleted_subset S) hM (by simpa using hS)
    (exposedLabels (natDeleted S) M s) hlabels
  apply path_of_le_labelDepth S s (by positivity)
  apply le_trans _ hshallow
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hm : actualMass S s * (3 * lambda) ≤ 8 * M :=
    (le_div_iff₀ (by positivity)).mp hmass
  change -160 / lambda ≤ -60 * actualMass S s / M
  apply (div_le_div_iff₀ hlambda hMR).mpr
  nlinarith

/-- Multiscale robustness against deletion of one third of the vertices. -/
theorem multiscale_third {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 3)
        ((M / 6 : ℝ) * Real.exp (-160 / lambda))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have hmass := (independentSamples p M).uniform_mass_bound_wide M lambda hlambda actualMass
    (actualMass_moment p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  exact depth_of_mass_bound_third hM hlambda S hS s (hs S)


end ProofOfSpace.DRSample

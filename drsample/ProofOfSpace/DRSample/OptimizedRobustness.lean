import ProofOfSpace.DRSample.Registry

/-! # Sharper finite bounds by accounting for the overlap of exceptional sets

Every deleted vertex belongs to both one-sided dense sets. Subtracting that
intersection improves the good-vertex count from `n - 5|S|/2` to `n - 3|S|/2`.
The public deletion, depth, interval-width, and failure constants are unchanged.
-/
namespace ProofOfSpace.DRSample
open Finset

theorem card_goodVerticesFourFifths_overlap {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) :
    2 * n ≤ 2 * (goodVerticesFourFifths S n).card + 3 * S.card := by
  have hleft := card_leftDenseFourFifths_le S n
  have hright := card_rightDenseFourFifths_le hS
  have hdeleted : S ⊆ leftDenseFourFifths S n ∩ rightDenseFourFifths S n := by
    intro j hj
    have hjn := mem_range.mp (hS hj)
    have hpos : 0 < (S ∩ Ico j (j + 1)).card := card_pos.mpr
      ⟨j, mem_inter.mpr ⟨hj, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
    apply mem_inter.mpr
    constructor
    · exact mem_filter.mpr ⟨hS hj, j, le_rfl, by omega⟩
    · exact mem_rightDenseFourFifths_of_interval (hi := j + 1) hS
        (by omega) (by omega) (by omega)
  have hi := card_le_card hdeleted
  have hu := card_union_add_card_inter (leftDenseFourFifths S n) (rightDenseFourFifths S n)
  have hs := card_sdiff_add_card_inter (range n)
    (leftDenseFourFifths S n ∪ rightDenseFourFifths S n)
  have hinter := card_le_card (inter_subset_right :
    range n ∩ (leftDenseFourFifths S n ∪ rightDenseFourFifths S n) ⊆
      leftDenseFourFifths S n ∪ rightDenseFourFifths S n)
  simp only [card_range] at hs
  change 2 * n ≤
    2 * (range n \ (leftDenseFourFifths S n ∪ rightDenseFourFifths S n)).card + 3 * S.card
  omega


/-- Sharper shallow-label bound at the same one-third deletion budget. -/
theorem shallow_labels_third_overlap {n d : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hn : 0 < n) (hsmall : S.card ≤ n / 3) (h : ℕ → ℕ)
    (hh : ∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) :
    (n : ℝ) / 2 * Real.exp (-20 * forbiddenMass (range n \ S) h / n) ≤ d := by
  have hsub : goodVerticesFourFifths S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨goodVerticesFourFifths_subset_range S n hj, goodVerticesFourFifths_survive hj⟩
  have hbound := depth_bound_of_inconsistent_mass
    (compressedHeight (range n \ S) h) 0 (range n \ S).card
    ((goodVerticesFourFifths S n).image (survivorRank (range n \ S)))
    (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      exact mem_Ico.mpr ⟨Nat.zero_le _, survivorRank_lt_card (hsub hj)⟩)
    d (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      rw [compressedHeight_rank (hsub hj)]
      exact hh j (hsub hj))
    ((n : ℝ) / 2) ((5 / 2 : ℝ) * forbiddenMass (range n \ S) h)
    (by positivity) (mul_nonneg (by norm_num) (forbiddenMass_nonneg _ _))
    (by
      rw [card_image_of_injOn ((survivorRank_injOn (range n \ S)).mono hsub)]
      have hc := card_goodVerticesFourFifths_overlap hS
      have hs : 3 * S.card ≤ n := by omega
      have hncard : n ≤ 2 * (goodVerticesFourFifths S n).card := by omega
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      simpa [mul_comm] using
        (show (n : ℝ) ≤ 2 * (goodVerticesFourFifths S n).card by exact_mod_cast hncard))
    (by nlinarith [goodFourFifths_compressed_mass_le hS h])
  convert hbound using 2
  congr 1
  ring

theorem depth_of_mass_bound_third_overlap {M : ℕ} (hM : 0 < M) {lambda : ℝ}
    (hlambda : 0 < lambda) (S : Finset (Fin M)) (hS : S.card ≤ M / 3)
    (s : SampleSpace (Finset (Fin M)) M)
    (hmass : actualMass S s ≤ 8 * M / (3 * lambda)) :
    HasPath (exposedGraph M s) S ((M / 2 : ℝ) * Real.exp (-160 / (3 * lambda))) := by
  have hlabels : ∀ i ∈ range M \ natDeleted S,
      1 ≤ exposedLabels (natDeleted S) M s i ∧
        exposedLabels (natDeleted S) M s i ≤ labelDepth S s := by
    intro i hi
    have hiM := mem_range.mp (mem_sdiff.mp hi).1
    refine ⟨exposedLabels_positive (natDeleted S) s hiM (mem_sdiff.mp hi).2, ?_⟩
    exact Finset.le_sup (f := fun v : Fin M => exposedLabels (natDeleted S) M s v.val)
      (mem_univ (⟨i, hiM⟩ : Fin M))
  have hshallow := shallow_labels_third_overlap (natDeleted_subset S) hM (by simpa using hS)
    (exposedLabels (natDeleted S) M s) hlabels
  apply path_of_le_labelDepth S s (by positivity)
  apply le_trans _ hshallow
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hm : actualMass S s * (3 * lambda) ≤ 8 * M :=
    (le_div_iff₀ (by positivity)).mp hmass
  change -160 / (3 * lambda) ≤ -20 * actualMass S s / M
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * lambda) hMR).mpr
  nlinarith

/-- Multiscale robustness against deletion of one third of the vertices. -/
theorem multiscale_third_overlap {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw (Finset (Fin M))) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M s) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-160 / (3 * lambda)))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have hmass := (independentSamples p M).uniform_mass_bound_wide M lambda hlambda actualMass
    (actualMass_moment p hlambda havoid)
  apply hmass.trans
  apply FiniteLaw.probability_mono
  intro s hs S hS
  exact depth_of_mass_bound_third_overlap hM hlambda S hS s (hs S)


theorem multiscale_mapped_third_overlap {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (p : ℕ → FiniteLaw α) (f : ℕ → α → Finset (Fin M)) {lambda : ℝ} (hlambda : 0 < lambda)
    (havoid : ∀ j < M, ∀ A : Finset (Fin M),
      (p j).probability (fun row => Disjoint (f j row) A) ≤
        Real.exp (-lambda * ∑ i ∈ A, harmonicAt M j i)) :
    (independentSamples p M).probability (fun s =>
      DepthRobust (exposedGraph M (mapSamples f M s)) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-160 / (3 * lambda)))) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * M) := by
  have h := multiscale_third_overlap hM (fun j => (p j).map (f j)) hlambda (by
    intro j hj A
    rw [FiniteLaw.probability_map]
    exact havoid j hj A)
  rwa [independentSamples_map_probability] at h


theorem finite_block_robustness_overlap {n m e b : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n)
    (hb : b ≤ m) (he : 2 * e ≤ (n / m) / 3)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ A : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-(1 / (Real.logb 2 n + 1)) * ∑ i ∈ A, harmonicAt n v i)) :
    (graphLaw m p).probability (fun s =>
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) e
        (((m : ℝ) * (n / m : ℕ) / 6) *
          Real.exp (-(160 * m * (Real.logb 2 n + 1) / (3 * (m / 3 : ℕ) ^ 2)))) b) ≥
      1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * (n / m : ℕ)) := by
  have hm0 : 0 < m := by omega
  have hM : 0 < n / m := Nat.div_pos hmn hm0
  have hn : (n / m) * m ≤ n := Nat.div_mul_le_self _ _
  have hlog : 0 < Real.logb 2 n := lt_of_lt_of_le (by norm_num)
    (logb_two_ge_one (show 2 ≤ n by omega))
  have ht : 0 < m / 3 := by omega
  have hlambda : 0 < ((m / 3 : ℕ) : ℝ) ^ 2 / (m * (Real.logb 2 n + 1)) := by positivity
  have hmeta := multiscale_mapped_third_overlap hM (rowLaw m p) (metaParents (by omega) hn) hlambda
    (fun j hj A => by
      have h := metaParents_avoidance_sharp (by omega) hn hj p
        (by positivity) havoid A
      convert h using 2
      congr 1
      field_simp)
  have hfinite : (graphLaw m p).probability (fun s =>
      DepthRobust (exposedGraph (n / m) (mapSamples (metaParents (by omega) hn) (n / m) s.1))
        ((n / m) / 3) (((n / m : ℕ) / 2 : ℝ) *
          Real.exp (-160 / (3 * (((m / 3 : ℕ) : ℝ) ^ 2 / (m * (Real.logb 2 n + 1))))))) ≥
        1 - Real.exp (-((4 / 3 : ℝ) - Real.log 3) * (n / m : ℕ)) := by
    exact hmeta.trans_eq (FiniteLaw.probability_product_fst
      (independentSamples (rowLaw m p) (n / m)) (rowLaw m p (n / m)) _).symm
  apply hfinite.trans
  apply FiniteLaw.probability_mono
  intro s hs
  have htransfer := blockDepthRobust_of_meta_third (rowGraph hm0 (n / m) s.1)
    (exposedGraph (n / m) (mapSamples (metaParents (by omega) hn) (n / m) s.1))
    (rowGraph_hasLine hm0 s.1) (by omega) hn hb (by positivity)
    (mapped_meta_edge_port (by omega) hn s.1) he hs
  have hdepth : (m : ℝ) / 3 * (((n / m : ℕ) / 2 : ℝ) *
      Real.exp (-160 / (3 * (((m / 3 : ℕ) : ℝ) ^ 2 / (m * (Real.logb 2 n + 1)))))) =
      ((m : ℝ) * (n / m : ℕ) / 6) *
        Real.exp (-(160 * m * (Real.logb 2 n + 1) / (3 * (m / 3 : ℕ) ^ 2))) := by
    have hexp : -160 / (3 * (((m / 3 : ℕ) : ℝ) ^ 2 / (m * (Real.logb 2 n + 1)))) =
        -(160 * m * (Real.logb 2 n + 1) / (3 * (m / 3 : ℕ) ^ 2)) := by field_simp
    rw [hexp]
    ring
  rw [hdepth] at htransfer
  exact htransfer.mono_graph (fun _ _ h => rowGraph_mono hm0 s.1 s.2 h)


end ProofOfSpace.DRSample

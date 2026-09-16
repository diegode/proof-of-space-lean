import ProofOfSpace.DRSample.Mass
import ProofOfSpace.DRSample.PaperDefinitions

/-! # Label bounds for every fixed deletion fraction below one -/
namespace ProofOfSpace.DRSample
open Finset
open Classical

/-- Endpoints of left intervals whose deletion density exceeds `(q-1)/q`. -/
noncomputable def denseLeft (q : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (range n).filter fun j => ∃ i ≤ j, (q - 1) * (j + 1 - i) < q * (S ∩ Ico i (j + 1)).card

/-- The rational-threshold version of the one-sided maximal estimate. -/
theorem card_denseLeft_le (q : ℕ) (S : Finset ℕ) (n : ℕ) :
    (q - 1) * (denseLeft q S n).card ≤ q * S.card := by
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    rcases (denseLeft q S n).eq_empty_or_nonempty with he | hne
    · simp [he]
    obtain ⟨j, hj, hmax⟩ := (denseLeft q S n).exists_max_image id hne
    have hjn : j < n := mem_range.mp (mem_filter.mp hj).1
    obtain ⟨i, hij, hdense⟩ := (mem_filter.mp hj).2
    have hiN : i < n := hij.trans_lt hjn
    let pastDeleted := S ∩ range i
    have hcover : denseLeft q S n ⊆ denseLeft q pastDeleted i ∪ Ico i (j + 1) := by
      intro k hk
      have hkj : k ≤ j := hmax k hk
      by_cases hki : k < i
      · apply mem_union_left
        obtain ⟨l, hlk, hldense⟩ := (mem_filter.mp hk).2
        have hinter : pastDeleted ∩ Ico l (k + 1) = S ∩ Ico l (k + 1) := by
          ext x
          simp only [pastDeleted, mem_inter, mem_range, mem_Ico]
          constructor
          · rintro ⟨⟨hxS, _⟩, hxlo, hxhi⟩
            exact ⟨hxS, hxlo, hxhi⟩
          · rintro ⟨hxS, hxlo, hxhi⟩
            exact ⟨⟨hxS, by omega⟩, hxlo, hxhi⟩
        apply mem_filter.mpr
        refine ⟨mem_range.mpr hki, l, hlk, ?_⟩
        rwa [hinter]
      · apply mem_union_right
        exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hdisj : Disjoint pastDeleted (S ∩ Ico i (j + 1)) := by
      apply disjoint_left.mpr
      intro x hx hy
      have hxi : x < i := mem_range.mp (mem_inter.mp hx).2
      have hix : i ≤ x := (mem_Ico.mp (mem_inter.mp hy).2).1
      omega
    have hsub : pastDeleted ∪ (S ∩ Ico i (j + 1)) ⊆ S := by
      apply union_subset
      · exact inter_subset_left
      · exact inter_subset_left
    have hcards : pastDeleted.card + (S ∩ Ico i (j + 1)).card ≤ S.card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card hsub
    have hrec := ih i hiN pastDeleted
    have hc := (card_le_card hcover).trans (card_union_le _ _)
    simp only [Nat.card_Ico] at hc
    nlinarith [Nat.mul_le_mul_left (q - 1) hc]

/-- The right-directed maximal set, obtained by reflecting the left-directed one. -/
noncomputable def denseRight (q : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  reflected n (denseLeft q (reflected n S) n)

theorem card_denseRight_le (q : ℕ) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    (q - 1) * (denseRight q S n).card ≤ q * S.card := by
  have hsub : denseLeft q (reflected n S) n ⊆ range n := filter_subset _ _
  rw [denseRight, reflected_card hsub]
  simpa [reflected_card hS] using card_denseLeft_le q (reflected n S) n

theorem mem_denseRight_of_interval (q : ℕ) {n j hi : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) (hj : j < hi) (hhi : hi ≤ n)
    (hdense : (q - 1) * (hi - j) < q * (S ∩ Ico j hi).card) : j ∈ denseRight q S n := by
  have hjn : j < n := hj.trans_le hhi
  have hcard : (reflected n S ∩ Ico (n - hi) (n - j)).card = (S ∩ Ico j hi).card := by
    rw [← reflected_inter_Ico hS hj.le hhi]
    exact reflected_card (inter_subset_left.trans hS)
  apply mem_image.mpr
  refine ⟨n - 1 - j, ?_, by omega⟩
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (by omega), n - hi, by omega, ?_⟩
  have heq : n - 1 - j + 1 = n - j := by omega
  rw [heq, hcard]
  have hlen : n - j - (n - hi) = hi - j := by omega
  rwa [hlen]

/-- Vertices outside both one-sided exceptional sets. -/
noncomputable def densityGood (q : ℕ) (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  range n \ (denseLeft q S n ∪ denseRight q S n)

theorem densityGood_subset_range (q : ℕ) (S : Finset ℕ) (n : ℕ) :
    densityGood q S n ⊆ range n := sdiff_subset

theorem densityGood_survive (q : ℕ) (hq : 2 ≤ q) {n j : ℕ} {S : Finset ℕ} (hj : j ∈ densityGood q S n) : j ∉ S := by
  intro hjS
  have hjn : j < n := mem_range.mp (mem_sdiff.mp hj).1
  have hnot : j ∉ denseLeft q S n := fun h => (mem_sdiff.mp hj).2 (mem_union_left _ h)
  apply hnot
  apply mem_filter.mpr
  refine ⟨mem_range.mpr hjn, j, le_rfl, ?_⟩
  have hpos : 0 < (S ∩ Ico j (j + 1)).card := card_pos.mpr
    ⟨j, mem_inter.mpr ⟨hjS, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
  have hpred : q - 1 + 1 = q := by omega
  rw [show j + 1 - j = 1 by omega, mul_one]
  nlinarith


theorem densityGood_left (q : ℕ) {n lo j : ℕ} {S : Finset ℕ}
    (hj : j ∈ densityGood q S n) (hlo : lo ≤ j) :
    q * (S ∩ Ico lo (j + 1)).card ≤ (q - 1) * (j + 1 - lo) := by
  by_contra! h
  exact (mem_sdiff.mp hj).2 (mem_union_left _
    (mem_filter.mpr ⟨(mem_sdiff.mp hj).1, lo, hlo, h⟩))

theorem densityGood_right (q : ℕ) {n j hi : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) (hj : j ∈ densityGood q S n)
    (hjhi : j < hi) (hhi : hi ≤ n) :
    q * (S ∩ Ico j hi).card ≤ (q - 1) * (hi - j) := by
  by_contra! h
  exact (mem_sdiff.mp hj).2 (mem_union_right _
    (mem_denseRight_of_interval q hS hjhi hhi h))

/-- At a four-fifths-good endpoint, rank distance is at least one fifth of distance. -/
theorem densityGood_survivor_distance (q : ℕ) (hq : 2 ≤ q) {n i j : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hi : i ∈ range n \ S) (hj : j ∈ range n \ S) (hij : i < j)
    (hgood : i ∈ densityGood q S n ∨ j ∈ densityGood q S n) :
    j - i ≤ q * (survivorRank (range n \ S) j - survivorRank (range n \ S) i) := by
  have hjn := mem_range.mp (mem_sdiff.mp hj).1
  have hdense : q * (S ∩ Ico i j).card ≤ (q - 1) * (j - i) := by
    rcases hgood with hg | hg
    · exact densityGood_right q hS hg hij hjn.le
    · have heq : S ∩ Ico (i + 1) (j + 1) = S ∩ Ico i j := by
        ext x
        simp only [mem_inter, mem_Ico]
        have hiS := (mem_sdiff.mp hi).2
        have hjS := (mem_sdiff.mp hj).2
        constructor
        · rintro ⟨hx, hlo, hhi⟩
          have hxj : x ≠ j := fun he => hjS (he ▸ hx)
          exact ⟨hx, by omega, by omega⟩
        · rintro ⟨hx, hlo, hhi⟩
          have hxi : x ≠ i := fun he => hiS (he ▸ hx)
          exact ⟨hx, by omega, by omega⟩
      have hh := densityGood_left q hg (show i + 1 ≤ j by omega)
      rw [heq] at hh
      have he : j + 1 - (i + 1) = j - i := by omega
      rwa [he] at hh
  have hp := survivor_interval_partition (S := S) hij.le hjn.le
  rw [survivorRank_sub hij.le]
  have hpred : q - 1 + 1 = q := by omega
  nlinarith

theorem densityGood_survivor_reciprocal (q : ℕ) (hq : 2 ≤ q) {n i j : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (hi : i ∈ range n \ S) (hj : j ∈ range n \ S) (hij : i < j)
    (hgood : i ∈ densityGood q S n ∨ j ∈ densityGood q S n) :
    (1 : ℝ) / (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ)
      ≤ (q : ℝ) / (j - i : ℕ) := by
  have hdist := densityGood_survivor_distance q hq hS hi hj hij hgood
  have hrank := survivorRank_strictMono hi hij
  have hp : (0 : ℝ) < (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hrank
  have hq : (0 : ℝ) < (j - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hij
  apply (div_le_div_iff₀ hp hq).mpr
  simpa using (show ((j - i : ℕ) : ℝ) ≤ q * (survivorRank (range n \ S) j - survivorRank (range n \ S) i : ℕ) by exact_mod_cast hdist)

theorem densityGood_compressed_cost_le (q : ℕ) (hq : 2 ≤ q) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (h : ℕ → ℕ) {j : ℕ} (hj : j ∈ densityGood q S n) :
    inconsistentCost (fun r => (compressedHeight (range n \ S) h r : ℝ)) 0
        (range n \ S).card (survivorRank (range n \ S) j) ≤
      (q : ℝ) * ((∑ i ∈ range n \ S, pairMass h i j) +
        ∑ i ∈ range n \ S, pairMass h j i) := by
  have hjU : j ∈ range n \ S := mem_sdiff.mpr
    ⟨densityGood_subset_range q S n hj, densityGood_survive q hq hj⟩
  rw [compressed_cost h hjU, mul_add, mul_sum, mul_sum]
  apply add_le_add
  · apply sum_le_sum
    intro i hi
    unfold pairMass
    split_ifs with hcond
    · simpa only [← mul_div_assoc, mul_one] using
        densityGood_survivor_reciprocal q hq hS hi hjU hcond.1 (Or.inr hj)
    · simp
  · apply sum_le_sum
    intro i hi
    unfold pairMass
    split_ifs with hcond
    · simpa only [← mul_div_assoc, mul_one] using
        densityGood_survivor_reciprocal q hq hS hjU hi hcond.1 (Or.inl hj)
    · simp

/-- Each forbidden pair can contribute at most once at either good endpoint. -/
theorem densityGood_compressed_mass_le (q : ℕ) (hq : 2 ≤ q) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n)
    (h : ℕ → ℕ) :
    ∑ r ∈ (densityGood q S n).image (survivorRank (range n \ S)),
      inconsistentCost (fun r => (compressedHeight (range n \ S) h r : ℝ)) 0
        (range n \ S).card r ≤ 2 * q * forbiddenMass (range n \ S) h := by
  have hsub : densityGood q S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨densityGood_subset_range q S n hj, densityGood_survive q hq hj⟩
  rw [sum_image ((survivorRank_injOn (range n \ S)).mono hsub)]
  calc _ ≤ ∑ j ∈ densityGood q S n,
        (q : ℝ) * ((∑ i ∈ range n \ S, pairMass h i j) + ∑ i ∈ range n \ S, pairMass h j i) :=
      sum_le_sum fun j hj => densityGood_compressed_cost_le q hq hS h hj
    _ ≤ ∑ j ∈ range n \ S,
        (q : ℝ) * ((∑ i ∈ range n \ S, pairMass h i j) + ∑ i ∈ range n \ S, pairMass h j i) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      exact mul_nonneg (Nat.cast_nonneg q) (add_nonneg
        (sum_nonneg fun i _ => pairMass_nonneg h i j)
        (sum_nonneg fun i _ => pairMass_nonneg h j i))
    _ = 2 * q * forbiddenMass (range n \ S) h := by
      rw [← mul_sum, sum_add_distrib]
      conv_lhs => arg 2; arg 2; rw [sum_comm]
      unfold forbiddenMass
      ring



/-- Deleted vertices occur in both exceptional sets, so their overlap must be
subtracted when estimating the number of good vertices. -/
theorem card_densityGood_overlap (q : ℕ) (hq : 2 ≤ q) {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) :
    (q - 1) * n ≤ (q - 1) * (densityGood q S n).card + (q + 1) * S.card := by
  have hleft := card_denseLeft_le q S n
  have hright := card_denseRight_le q hS
  have hpred : q - 1 + 1 = q := by omega
  have hdeleted : S ⊆ denseLeft q S n ∩ denseRight q S n := by
    intro j hj
    have hjn := mem_range.mp (hS hj)
    have hpos : 0 < (S ∩ Ico j (j + 1)).card := card_pos.mpr
      ⟨j, mem_inter.mpr ⟨hj, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
    have hd : (q - 1) * (j + 1 - j) < q * (S ∩ Ico j (j + 1)).card := by
      rw [show j + 1 - j = 1 by omega, mul_one]
      nlinarith
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨hS hj, j, le_rfl, hd⟩,
      mem_denseRight_of_interval q hS (by omega) (by omega) hd⟩
  have hi := card_le_card hdeleted
  have hu := card_union_add_card_inter (denseLeft q S n) (denseRight q S n)
  have hs := card_sdiff_add_card_inter (range n) (denseLeft q S n ∪ denseRight q S n)
  have hinter := card_le_card (inter_subset_right :
    range n ∩ (denseLeft q S n ∪ denseRight q S n) ⊆ denseLeft q S n ∪ denseRight q S n)
  simp only [card_range] at hs
  change (q - 1) * n ≤
    (q - 1) * (range n \ (denseLeft q S n ∪ denseRight q S n)).card + (q + 1) * S.card
  nlinarith [Nat.mul_le_mul_left (q - 1) hi, Nat.mul_le_mul_left (q - 1) hinter]

set_option maxHeartbeats 800000 in
-- The parameter-dependent cardinality and exponential estimates share many casts.
/-- The shallow-label estimate for an arbitrary fixed deleted fraction. -/
theorem shallow_labels_fraction {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d : ℕ, 0 < n → ∀ S : Finset ℕ,
      S ⊆ range n → (S.card : ℝ) ≤ α * n → ∀ h : ℕ → ℕ,
      (∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) →
      (n : ℝ) / c * Real.exp (-c * forbiddenMass (range n \ S) h / n) ≤ d := by
  let δ := 1 - α
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let q := Nat.ceil (4 / δ)
  have hqLower : 4 / δ ≤ (q : ℝ) := Nat.le_ceil _
  have hqδ : 4 ≤ (q : ℝ) * δ := (div_le_iff₀ hδ).mp hqLower
  have hqReal : 2 ≤ (q : ℝ) := by
    dsimp [δ] at *
    nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
  have hq : 2 ≤ q := by exact_mod_cast hqReal
  let c : ℝ := 8 * q / δ
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n d hn S hS hsmall h hh
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let g : ℝ := δ * n / 2
  let W := forbiddenMass (range n \ S) h
  have hg : 0 < g := by dsimp [g]; positivity
  have hW : 0 ≤ W := forbiddenMass_nonneg _ _
  have hsub : densityGood q S n ⊆ range n \ S := fun j hj => mem_sdiff.mpr
    ⟨densityGood_subset_range q S n hj, densityGood_survive q hq hj⟩
  have hcard : g ≤ ((densityGood q S n).card : ℝ) := by
    have hcount := card_densityGood_overlap q hq hS
    have hcountR : ((q : ℝ) - 1) * n ≤
        ((q : ℝ) - 1) * (densityGood q S n).card + ((q : ℝ) + 1) * S.card := by
      have hcR := (Nat.cast_le (α := ℝ)).mpr hcount
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)] at hcR
      exact hcR
    have hprod := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (q : ℝ) + 1)
    have hcoef : ((q : ℝ) - 1) * δ / 2 ≤ (q - 1 : ℝ) - (q + 1) * α := by
      dsimp [δ] at *
      nlinarith
    have hcoefn := mul_le_mul_of_nonneg_right hcoef hn0.le
    by_contra! hbad
    have hp := mul_pos (show 0 < (q : ℝ) - 1 by linarith) (sub_pos.mpr hbad)
    dsimp [g] at *
    nlinarith
  have hbound := depth_bound_of_inconsistent_mass
    (compressedHeight (range n \ S) h) 0 (range n \ S).card
    ((densityGood q S n).image (survivorRank (range n \ S)))
    (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      exact mem_Ico.mpr ⟨Nat.zero_le _, survivorRank_lt_card (hsub hj)⟩)
    d (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      rw [compressedHeight_rank (hsub hj)]
      exact hh j (hsub hj))
    g ((q : ℝ) / 2 * W) hg (by positivity)
    (by
      rw [card_image_of_injOn ((survivorRank_injOn (range n \ S)).mono hsub)]
      exact hcard)
    (by nlinarith [densityGood_compressed_mass_le q hq hS h])
  have hpre : (n : ℝ) / c ≤ g := by
    apply (div_le_iff₀ hc).mpr
    dsimp [g, c]
    field_simp
    nlinarith
  have hexp : -c * W / n ≤ -4 * ((q : ℝ) / 2 * W) / g := by
    dsimp [c, g]
    field_simp
    nlinarith
  exact (mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le hg.le).trans hbound

end ProofOfSpace.DRSample

namespace ProofOfSpaceStatement
open Finset ProofOfSpace.DRSample

/-- Lemma `lem:dr-labels`, with a constant depending only on the deletion fraction. -/
theorem dr_labels {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d : ℕ, 1 ≤ n → ∀ S : Finset ℕ,
      S ⊆ range n → (S.card : ℝ) ≤ α * n → ∀ h : ℕ → ℕ,
      (∀ i ∈ range n \ S, 1 ≤ h i ∧ h i ≤ d) →
      (n : ℝ) / c * Real.exp (-c * labelMass (range n \ S) h / n) ≤ d := by
  simpa only [labelMass, forbiddenMass, pairMass, Nat.succ_le_iff] using
    shallow_labels_fraction hα hα1

end ProofOfSpaceStatement

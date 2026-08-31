import ProofOfSpace.Constructions

/-!
# The union bound for permutation-interlayer expansion

`Constructions.lean` defines `PermutationExpansionWhpClaim` and records that the
development does not prove it.  This file proves it, by the union bound.

The chain is entirely elementary once the probability space is recognised for what it
is: `uniformLaw n d` is the uniform measure on the finite type of `d`-tuples of
permutations, so every probability here is a ratio of cardinalities.

* `probabilityOf_le_sum` is the union bound for such a measure.
* `card_perm_maps_le` counts the permutations carrying a `k`-set into an `m`-set:
  at most `(m)_k (n-k)!` of them.
* `hitProb_le` turns that into the probability `(m)_k / (n)_k` for one permutation, and
  the product structure of a tuple raises it to the `d`-th power.
* `permutationExpansion_whp` assembles the three into the claim.
-/

namespace ProofOfSpace
namespace Concrete

open Finset
open scoped ENNReal

/-! ### Probabilities of a finite uniform law -/

variable {A : Type*}

theorem probabilityOf_congr (p : PMF A) {Q R : A → Prop} (h : ∀ a, Q a ↔ R a) :
    probabilityOf p Q = probabilityOf p R := by
  classical
  unfold probabilityOf
  exact tsum_congr fun a => by simp only [h a]

theorem probabilityOf_mono (p : PMF A) {Q R : A → Prop} (h : ∀ a, Q a → R a) :
    probabilityOf p Q ≤ probabilityOf p R := by
  classical
  unfold probabilityOf
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hq : Q a
  · rw [if_pos hq, if_pos (h a hq)]
  · rw [if_neg hq]
    exact bot_le

/-- Total probability: an event and its complement exhaust the law. -/
theorem probabilityOf_add_compl (p : PMF A) (Q : A → Prop) :
    probabilityOf p Q + probabilityOf p (fun a => ¬ Q a) = 1 := by
  classical
  unfold probabilityOf
  rw [← ENNReal.tsum_add]
  rw [← p.tsum_coe]
  refine tsum_congr fun a => ?_
  by_cases hq : Q a <;> simp [hq]

/-- To certify an event with failure at most `δ` it is enough to bound the failure
event by `δ`. -/
theorem holdsWithFailureAtMost_of_compl_le (p : PMF A) (Q : A → Prop) {δ : ℝ≥0∞}
    (h : probabilityOf p (fun a => ¬ Q a) ≤ δ) : HoldsWithFailureAtMost p Q δ := by
  have hsum := probabilityOf_add_compl p Q
  have hne : probabilityOf p (fun a => ¬ Q a) ≠ ⊤ := by
    intro hcon
    rw [hcon] at hsum
    simp at hsum
  have heq : probabilityOf p Q = 1 - probabilityOf p (fun a => ¬ Q a) :=
    ENNReal.eq_sub_of_add_eq hne hsum
  rw [HoldsWithFailureAtMost, heq]
  exact tsub_le_tsub_left h 1

theorem sum_tsum_ennreal {ι : Type*} (s : Finset ι) (f : ι → A → ℝ≥0∞) :
    ∑' a, ∑ i ∈ s, f i a = ∑ i ∈ s, ∑' a, f i a := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i t hi ih
  rw [Finset.sum_insert hi, ← ih, ← ENNReal.tsum_add]
  exact tsum_congr fun a => by rw [Finset.sum_insert hi]

/-- **The union bound.**  If every outcome of `Q` is an outcome of `R i` for some `i` in
a finite index set, the probability of `Q` is at most the sum. -/
theorem probabilityOf_le_sum {ι : Type*} (p : PMF A) (Q : A → Prop) (s : Finset ι)
    (R : ι → A → Prop) (h : ∀ a, Q a → ∃ i ∈ s, R i a) :
    probabilityOf p Q ≤ ∑ i ∈ s, probabilityOf p (R i) := by
  classical
  unfold probabilityOf
  rw [← sum_tsum_ennreal]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hq : Q a
  · obtain ⟨i, hi, hR⟩ := h a hq
    rw [if_pos hq]
    calc p a = (if R i a then p a else 0) := by rw [if_pos hR]
      _ ≤ ∑ j ∈ s, (if R j a then p a else 0) :=
          Finset.single_le_sum (f := fun j => if R j a then p a else 0)
            (fun j _ => bot_le) hi
  · rw [if_neg hq]
    exact bot_le

/-- For a uniform law, every probability is a ratio of cardinalities. -/
theorem probabilityOf_uniformOfFintype [Fintype A] [Nonempty A] (Q : A → Prop)
    [DecidablePred Q] :
    probabilityOf (PMF.uniformOfFintype A) Q
      = (Finset.univ.filter Q).card / (Fintype.card A : ℝ≥0∞) := by
  classical
  unfold probabilityOf
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_eq_sum (s := Finset.univ) (by simp), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-! ### Counting permutations that carry one set into another -/

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Permutations that agree with a fixed map on `T` number at most `(n - |T|)!`:
outside `T` such a permutation is an injection from the complement of `T` into the
complement of the image. -/
theorem card_agree_le (T : Finset α) (g : ↑T → α) :
    (univ.filter fun π : Equiv.Perm α => ∀ v : ↑T, π v = g v).card
      ≤ Nat.factorial (Fintype.card α - T.card) := by
  classical
  set B := univ.filter fun π : Equiv.Perm α => ∀ v : ↑T, π v = g v with hBdef
  rcases B.eq_empty_or_nonempty with he | ⟨π₀, hπ₀⟩
  · simp [he]
  have hmem : ∀ π ∈ B, ∀ v : ↑T, π v = g v := fun π hπ => (Finset.mem_filter.1 hπ).2
  set U : Finset α := Finset.univ.image (fun v : ↑T => g v) with hUdef
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hmem π₀ hπ₀ a
    have h2 := hmem π₀ hπ₀ b
    have : (π₀ : Equiv.Perm α) a = (π₀ : Equiv.Perm α) b := by rw [h1, h2, hab]
    exact Subtype.ext (π₀.injective this)
  have hUcard : U.card = T.card := by
    rw [hUdef, Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_coe]
  have key : ∀ π ∈ B, ∀ x : α, x ∉ T → π x ∉ U := by
    intro π hπ x hx hcon
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hcon
    have heq : π x = π (v : α) := ((hmem π hπ v).trans hv).symm
    have hxv : x = (v : α) := π.injective heq
    exact hx (by rw [hxv]; exact v.2)
  have hcardT : Fintype.card {x : α // x ∈ T} = T.card := by
    simp [Fintype.card_subtype]
  have hcompl : ∀ (V : Finset α), V.card = T.card →
      Fintype.card {x : α // x ∉ V} = Fintype.card α - T.card := by
    intro V hV
    rw [Fintype.card_subtype_compl]
    congr 1
    simp [Fintype.card_subtype, hV]
  have hinj : B.card ≤ Fintype.card ({x : α // x ∉ T} ↪ {x : α // x ∉ U}) := by
    rw [← Fintype.card_coe B]
    refine Fintype.card_le_of_injective
      (fun π => ⟨fun x => ⟨(π.1 : Equiv.Perm α) x, key π.1 π.2 x x.2⟩, ?_⟩) ?_
    · intro a b hab
      exact Subtype.ext (π.1.injective (Subtype.ext_iff.1 hab))
    · intro π₁ π₂ hπ
      refine Subtype.ext (Equiv.ext fun x => ?_)
      by_cases hx : x ∈ T
      · rw [hmem π₁.1 π₁.2 ⟨x, hx⟩, hmem π₂.1 π₂.2 ⟨x, hx⟩]
      · exact Subtype.ext_iff.1 (Function.Embedding.ext_iff.1 hπ ⟨x, hx⟩)
  calc B.card ≤ Fintype.card ({x : α // x ∉ T} ↪ {x : α // x ∉ U}) := hinj
    _ = (Fintype.card α - T.card).descFactorial (Fintype.card α - T.card) := by
        rw [Fintype.card_embedding_eq, hcompl U hUcard, hcompl T rfl]
    _ = Nat.factorial (Fintype.card α - T.card) := Nat.descFactorial_self _

/-- **The permutation count.**  At most `(m)_k (n-k)!` permutations carry a `k`-set into
an `m`-set. -/
theorem card_maps_le (T S : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ v ∈ T, π v ∈ S).card
      ≤ S.card.descFactorial T.card * Nat.factorial (Fintype.card α - T.card) := by
  classical
  set B := univ.filter fun π : Equiv.Perm α => ∀ v ∈ T, π v ∈ S with hBdef
  set φ : Equiv.Perm α → (↑T → α) := fun π v => π v with hφ
  set Im := B.image φ with hIm
  have hfib : B.card = ∑ g ∈ Im, (B.filter fun π => φ π = g).card :=
    Finset.card_eq_sum_card_fiberwise fun π hπ => Finset.mem_image_of_mem _ hπ
  have hsub : ∀ g ∈ Im, (B.filter fun π => φ π = g).card
      ≤ Nat.factorial (Fintype.card α - T.card) := by
    intro g _
    refine le_trans (Finset.card_le_card ?_) (card_agree_le T g)
    intro π hπ
    obtain ⟨hπB, hπg⟩ := Finset.mem_filter.1 hπ
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun v => ?_⟩
    exact congrFun hπg v
  have hImcard : Im.card ≤ S.card.descFactorial T.card := by
    have hmapsto : ∀ g ∈ Im, (∀ v : ↑T, g v ∈ S) ∧ Function.Injective g := by
      intro g hg
      obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.1 hg
      have hπS := (Finset.mem_filter.1 hπ).2
      refine ⟨fun v => hπS v v.2, fun a b hab => Subtype.ext (π.injective hab)⟩
    have : Fintype.card ↑Im ≤ Fintype.card (↑T ↪ ↑S) := by
      refine Fintype.card_le_of_injective
        (fun g => ⟨fun v => ⟨g.1 v, (hmapsto g.1 g.2).1 v⟩, ?_⟩) ?_
      · intro a b hab
        exact (hmapsto g.1 g.2).2 (Subtype.ext_iff.1 hab)
      · intro g₁ g₂ hg
        refine Subtype.ext (funext fun v => ?_)
        exact Subtype.ext_iff.1 (Function.Embedding.ext_iff.1 hg v)
    rw [Fintype.card_coe] at this
    refine this.trans (le_of_eq ?_)
    rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe]
  calc B.card = ∑ g ∈ Im, (B.filter fun π => φ π = g).card := hfib
    _ ≤ ∑ _g ∈ Im, Nat.factorial (Fintype.card α - T.card) := Finset.sum_le_sum hsub
    _ = Im.card * Nat.factorial (Fintype.card α - T.card) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ S.card.descFactorial T.card * Nat.factorial (Fintype.card α - T.card) :=
        Nat.mul_le_mul_right _ hImcard

omit [DecidableEq α] in
/-- Instance-free form: any collection of permutations carrying `T` into `S` is small. -/
theorem card_maps_le' (T S : Finset α) (C : Finset (Equiv.Perm α))
    (hC : ∀ π ∈ C, ∀ v ∈ T, π v ∈ S) :
    C.card ≤ S.card.descFactorial T.card
      * Nat.factorial (Fintype.card α - T.card) := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_maps_le T S)
  intro π hπ
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hC π hπ⟩

end Counting

/-! ### From one permutation to a `d`-tuple -/

/-- A `d`-tuple interlayer is exactly a `d`-tuple of permutations. -/
def interlayerEquiv (n d : ℕ) :
    PermutationInterlayer n d ≃ (Fin d → Equiv.Perm (Fin n)) where
  toFun := PermutationInterlayer.perm
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_permutationInterlayer (n d : ℕ) :
    Fintype.card (PermutationInterlayer n d) = (Nat.factorial n) ^ d := by
  rw [Fintype.card_congr (interlayerEquiv n d), Fintype.card_fun, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_fin]

/-- A tuple event that is a product of one-permutation events. -/
theorem card_interlayer_le {n d : ℕ} (B : Finset (Equiv.Perm (Fin n))) :
    (univ.filter fun P : PermutationInterlayer n d => ∀ j, P.perm j ∈ B).card
      ≤ B.card ^ d := by
  classical
  rw [← Fintype.card_coe]
  have hle : Fintype.card
      ↑(univ.filter fun P : PermutationInterlayer n d => ∀ j, P.perm j ∈ B)
      ≤ Fintype.card (Fin d → ↑B) := by
    refine Fintype.card_le_of_injective
      (fun P j => ⟨P.1.perm j, (Finset.mem_filter.1 P.2).2 j⟩) ?_
    intro P₁ P₂ h
    refine Subtype.ext ?_
    have hperm : P₁.1.perm = P₂.1.perm := by
      funext j
      exact congrArg Subtype.val (congrFun h j)
    cases P₁ with | mk P₁ hP₁ => cases P₂ with | mk P₂ hP₂ =>
      cases P₁; cases P₂; simp_all
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe B] at hle
  exact hle

/-! ### The probability that one source set lands in one target set -/

/-- The chance that a uniform permutation carries a `k`-set into an `m`-set. -/
noncomputable def hitProb (n k m : ℕ) : ℝ≥0∞ :=
  (m.descFactorial k : ℝ≥0∞) / (n.descFactorial k : ℝ≥0∞)

/-- `N_P(T) ⊆ U` says exactly that each of the `d` permutations maps `T` into `U`. -/
theorem neighborhood_subset_iff {n d : ℕ} (P : PermutationInterlayer n d)
    (T U : Finset (Fin n)) :
    P.neighborhood T ⊆ U ↔ ∀ j, ∀ v ∈ T, P.perm j v ∈ U := by
  classical
  simp only [PermutationInterlayer.neighborhood, Finset.subset_iff, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h j v hv
    exact h ⟨v, hv, j, rfl⟩
  · rintro h x ⟨v, hv, j, rfl⟩
    exact h j v hv

/-- `(a/b)^d = a^d/b^d` in `ℝ≥0∞`. -/
theorem ennreal_div_pow (a b : ℝ≥0∞) (d : ℕ) : (a / b) ^ d = a ^ d / b ^ d := by
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-- Instance-free tuple form. -/
theorem card_interlayer_le' {n d : ℕ} (B : Finset (Equiv.Perm (Fin n)))
    (C : Finset (PermutationInterlayer n d)) (hC : ∀ P ∈ C, ∀ j, P.perm j ∈ B) :
    C.card ≤ B.card ^ d := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_interlayer_le B)
  intro P hP
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hC P hP⟩

/-- Interlayers crushing a `k`-set into an `m`-set number at most
`((m)_k (n-k)!)^d`. -/
theorem card_neighborhood_le {n d : ℕ} (T U : Finset (Fin n))
    (C : Finset (PermutationInterlayer n d)) (hC : ∀ P ∈ C, P.neighborhood T ⊆ U) :
    C.card ≤ (U.card.descFactorial T.card * Nat.factorial (n - T.card)) ^ d := by
  classical
  set B := univ.filter fun π : Equiv.Perm (Fin n) => ∀ v ∈ T, π v ∈ U with hB
  have hBcard : B.card ≤ U.card.descFactorial T.card * Nat.factorial (n - T.card) := by
    have h := card_maps_le' T U B (fun π hπ => (Finset.mem_filter.1 hπ).2)
    rwa [Fintype.card_fin] at h
  refine le_trans (card_interlayer_le' B C ?_) (Nat.pow_le_pow_left hBcard d)
  intro P hP j
  exact Finset.mem_filter.2
    ⟨Finset.mem_univ _, fun w hw => (neighborhood_subset_iff P T U).1 (hC P hP) j w hw⟩

/-- **The one-pair bound.**  For `k ≤ n`, the probability that a sampled interlayer
crushes a `k`-set into an `m`-set is at most `((m)_k / (n)_k)^d`. -/
theorem prob_neighborhood_subset_le {n d : ℕ} (T U : Finset (Fin n))
    (hT : T.card ≤ n) :
    probabilityOf (PermutationInterlayer.uniformLaw n d)
        (fun P => P.neighborhood T ⊆ U) ≤ hitProb n T.card U.card ^ d := by
  classical
  have hfac : n.descFactorial T.card * Nat.factorial (n - T.card) = Nat.factorial n := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.mul_comm (Nat.factorial T.card) (n.choose T.card)]
    exact Nat.choose_mul_factorial_mul_factorial hT
  have hne : ((Nat.factorial (n - T.card) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp [Nat.factorial_ne_zero]
  have hnt : ((Nat.factorial (n - T.card) : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  have hratio :
      ((U.card.descFactorial T.card * Nat.factorial (n - T.card) : ℕ) : ℝ≥0∞)
        / ((Nat.factorial n : ℕ) : ℝ≥0∞) = hitProb n T.card U.card := by
    rw [hitProb, ← hfac]
    push_cast
    exact ENNReal.mul_div_mul_right _ _ hne hnt
  rw [PermutationInterlayer.uniformLaw, probabilityOf_uniformOfFintype,
    card_permutationInterlayer]
  refine le_trans (ENNReal.div_le_div_right
    (b := (((U.card.descFactorial T.card * Nat.factorial (n - T.card)) ^ d : ℕ) : ℝ≥0∞))
    ?_ _) (le_of_eq ?_)
  · exact_mod_cast card_neighborhood_le (n := n) (d := d) T U _
      (fun P hP => (Finset.mem_filter.1 hP).2)
  · rw [← hratio]
    push_cast
    rw [ennreal_div_pow]

/-! ### Failure profiles

A *failure profile* is any `m : ℕ → ℕ` with `β(k/n) n ≤ m k + 1`, so that a `k`-set whose
neighbourhood misses the expansion requirement has that neighbourhood inside a set of
size `m k`.  The sharpest choice is `⌈β(k/n) n⌉ - 1`; larger admissible values are also
allowed and are easier to certify. -/

/-- The canonical failure profile: one less than the least integer meeting the expansion
requirement.  Values above `n` are irrelevant to the union bound and are set to zero. -/
noncomputable def canonicalFailureProfile (S : Setting) (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (S.β ((k : ℝ) / n) * n) - 1 else 0

/-- The canonical profile meets the real-valued expansion threshold. -/
theorem canonicalFailureProfile_spec (S : Setting) (n k : ℕ) (hk : k ≤ n) :
    S.β ((k : ℝ) / n) * n ≤ (canonicalFailureProfile S n k : ℝ) + 1 := by
  rw [canonicalFailureProfile, if_pos hk]
  by_cases hz : Nat.ceil (S.β ((k : ℝ) / n) * n) = 0
  · have hceil := Nat.le_ceil (S.β ((k : ℝ) / n) * n)
    rw [hz] at hceil
    simp only [Nat.cast_zero] at hceil
    simp only [hz, Nat.zero_sub, Nat.cast_zero, zero_add]
    exact hceil.trans (by norm_num)
  · have hceil := Nat.le_ceil (S.β ((k : ℝ) / n) * n)
    have hpos : 0 < Nat.ceil (S.β ((k : ℝ) / n) * n) := Nat.pos_of_ne_zero hz
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil (S.β ((k : ℝ) / n) * n))]
    norm_num
    exact hceil

/-- The canonical failure size never exceeds the layer width. -/
theorem canonicalFailureProfile_le (S : Setting) (n k : ℕ) :
    canonicalFailureProfile S n k ≤ n := by
  rw [canonicalFailureProfile]
  split_ifs with hk
  · by_cases hn : n = 0
    · subst n
      simp
    · have hnreal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / n := div_nonneg (Nat.cast_nonneg k) hnreal.le
      have hk1 : (k : ℝ) / n ≤ 1 := by
        rw [div_le_one hnreal]
        exact_mod_cast hk
      have hβ := (S.β_maps ⟨hk0, hk1⟩).2
      have hmul : S.β ((k : ℝ) / n) * n ≤ n := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg n)
      have hceil : Nat.ceil (S.β ((k : ℝ) / n) * n) ≤ n :=
        Nat.ceil_le.mpr hmul
      omega
  · exact Nat.zero_le _

/-- A failing interlayer crushes some *nonempty* source set into a set of the failure
size.  The empty set is excluded because `β 0 = 0` makes its requirement vacuous, and it
would otherwise contribute the useless term `1` to every union bound. -/
theorem exists_cover_of_not_expands {n d : ℕ} {S : Setting} {m : ℕ → ℕ}
    (hm : ∀ k ≤ n, S.β (k / n) * n ≤ (m k : ℝ) + 1) (hmn : ∀ k, m k ≤ n)
    (P : PermutationInterlayer n d) (hP : ¬ P.Expands S) :
    ∃ T : Finset (Fin n), T.Nonempty ∧
      ∃ U ∈ Finset.univ.powersetCard (m T.card), P.neighborhood T ⊆ U := by
  classical
  rw [PermutationInterlayer.Expands] at hP
  push Not at hP
  obtain ⟨T, hT⟩ := hP
  have hTn : T.card ≤ n := by
    have h := Finset.card_le_univ T
    simpa using h
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with rfl | h
    · exfalso
      rw [Finset.card_empty] at hT
      simp only [Nat.cast_zero, zero_div, S.β_zero, zero_mul,
        PermutationInterlayer.neighborhood, Finset.biUnion_empty, Finset.card_empty,
        Nat.cast_zero] at hT
      exact lt_irrefl 0 hT
    · exact h
  have hlt : ((P.neighborhood T).card : ℝ) < (m T.card : ℝ) + 1 :=
    lt_of_lt_of_le hT (hm T.card hTn)
  have hle : (P.neighborhood T).card ≤ m T.card := by
    have : ((P.neighborhood T).card : ℝ) < ((m T.card + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  obtain ⟨U, hU1, hU2, hU3⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (P.neighborhood T)) hle (by simpa using hmn T.card)
  exact ⟨T, hTne, U, Finset.mem_powersetCard.2 ⟨hU2, hU3⟩, hU1⟩

/-- Regrouping a sum over the nonempty source sets by cardinality. -/
theorem sum_over_nonempty_finsets {n : ℕ} (g : ℕ → ℝ≥0∞) :
    ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => T.Nonempty), g T.card
      = ∑ k ∈ Finset.Ico 1 (n + 1), (n.choose k : ℝ≥0∞) * g k := by
  classical
  have hmaps : ∀ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => T.Nonempty),
      T.card ∈ Finset.Ico 1 (n + 1) := by
    intro T hT
    have hne := (Finset.mem_filter.1 hT).2
    refine Finset.mem_Ico.2 ⟨Finset.card_pos.2 hne, ?_⟩
    have h := Finset.card_le_univ T
    simpa using h
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun T : Finset (Fin n) => g T.card)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
  have hfil : ((Finset.univ.filter fun T : Finset (Fin n) => T.Nonempty).filter
      fun T => T.card = k) = (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      exact ⟨Finset.card_pos.1 (by omega), h⟩
  have hconst : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, g T.card = g k :=
    fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2]
  rw [hfil, Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The union bound, assembled -/

/-- **The union bound for interlayer expansion.**  The probability that a uniformly
sampled `d`-tuple of permutations fails the expansion requirement of `S` is at most an
explicit sum of binomial terms. -/
theorem permutationExpansion_failure_le (S : Setting) (n d : ℕ) (m : ℕ → ℕ)
    (hm : ∀ k ≤ n, S.β (k / n) * n ≤ (m k : ℝ) + 1) (hmn : ∀ k, m k ≤ n) :
    probabilityOf (PermutationInterlayer.uniformLaw n d) (fun P => ¬ P.Expands S)
      ≤ ∑ k ∈ Finset.Ico 1 (n + 1),
          (n.choose k : ℝ≥0∞) * ((n.choose (m k) : ℝ≥0∞) * hitProb n k (m k) ^ d) := by
  classical
  set p := PermutationInterlayer.uniformLaw n d with hp
  set R : Finset (Fin n) → PermutationInterlayer n d → Prop := fun T P =>
    ∃ U ∈ Finset.univ.powersetCard (m T.card), P.neighborhood T ⊆ U with hR
  have hstage1 : probabilityOf p (fun P => ¬ P.Expands S)
      ≤ ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) => T.Nonempty),
          probabilityOf p (R T) :=
    probabilityOf_le_sum p _ _ R fun P hP => by
      obtain ⟨T, hTne, U, hU, hsub⟩ := exists_cover_of_not_expands hm hmn P hP
      exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hTne⟩, U, hU, hsub⟩
  have hstage2 : ∀ T : Finset (Fin n), probabilityOf p (R T)
      ≤ (n.choose (m T.card) : ℝ≥0∞) * hitProb n T.card (m T.card) ^ d := by
    intro T
    have hTn : T.card ≤ n := by
      have h := Finset.card_le_univ T
      simpa using h
    have hsplit : probabilityOf p (R T)
        ≤ ∑ U ∈ Finset.univ.powersetCard (m T.card),
            probabilityOf p (fun P => P.neighborhood T ⊆ U) :=
      probabilityOf_le_sum p _ _ _ fun P hP => hP
    refine hsplit.trans ?_
    have hterm : ∀ U ∈ Finset.univ.powersetCard (m T.card),
        probabilityOf p (fun P => P.neighborhood T ⊆ U)
          ≤ hitProb n T.card (m T.card) ^ d := by
      intro U hU
      have hUcard : U.card = m T.card := (Finset.mem_powersetCard.1 hU).2
      have h := prob_neighborhood_subset_le (n := n) (d := d) T U hTn
      rwa [hUcard] at h
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  refine hstage1.trans ?_
  refine (Finset.sum_le_sum fun T _ => hstage2 T).trans (le_of_eq ?_)
  exact sum_over_nonempty_finsets (n := n)
    (fun k => (n.choose (m k) : ℝ≥0∞) * hitProb n k (m k) ^ d)

/-! ### The bound as a single ratio of naturals -/

/-- One term of the bound, over the common denominator `(n!)^d`. -/
theorem term_eq_div {n k mm d : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ≥0∞) * ((n.choose mm : ℝ≥0∞) * hitProb n k mm ^ d)
      = ((n.choose k * (n.choose mm
            * (mm.descFactorial k * Nat.factorial (n - k)) ^ d) : ℕ) : ℝ≥0∞)
        / ((Nat.factorial n ^ d : ℕ) : ℝ≥0∞) := by
  have hfac : n.descFactorial k * Nat.factorial (n - k) = Nat.factorial n := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.mul_comm (Nat.factorial k) (n.choose k)]
    exact Nat.choose_mul_factorial_mul_factorial hk
  have hne : ((Nat.factorial (n - k) : ℕ) : ℝ≥0∞) ≠ 0 := by simp [Nat.factorial_ne_zero]
  have hnt : ((Nat.factorial (n - k) : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  have hratio : hitProb n k mm
      = ((mm.descFactorial k * Nat.factorial (n - k) : ℕ) : ℝ≥0∞)
        / ((Nat.factorial n : ℕ) : ℝ≥0∞) := by
    rw [hitProb, ← hfac]
    push_cast
    exact (ENNReal.mul_div_mul_right _ _ hne hnt).symm
  rw [hratio, ennreal_div_pow]
  push_cast
  simp only [mul_div_assoc]

/-- **The union bound as one fraction.**  Everything is now a natural number
comparison. -/
theorem permutationExpansion_failure_le_ratio (S : Setting) (n d : ℕ) (m : ℕ → ℕ)
    (hm : ∀ k ≤ n, S.β (k / n) * n ≤ (m k : ℝ) + 1) (hmn : ∀ k, m k ≤ n) :
    probabilityOf (PermutationInterlayer.uniformLaw n d) (fun P => ¬ P.Expands S)
      ≤ ((∑ k ∈ Finset.Ico 1 (n + 1), n.choose k * (n.choose (m k)
            * ((m k).descFactorial k * Nat.factorial (n - k)) ^ d) : ℕ) : ℝ≥0∞)
        / ((Nat.factorial n ^ d : ℕ) : ℝ≥0∞) := by
  refine (permutationExpansion_failure_le S n d m hm hmn).trans (le_of_eq ?_)
  rw [Nat.cast_sum]
  have hsumdiv : (∑ k ∈ Finset.Ico 1 (n + 1),
      ((n.choose k * (n.choose (m k)
        * ((m k).descFactorial k * Nat.factorial (n - k)) ^ d) : ℕ) : ℝ≥0∞))
      / ((Nat.factorial n ^ d : ℕ) : ℝ≥0∞)
      = ∑ k ∈ Finset.Ico 1 (n + 1),
        ((n.choose k * (n.choose (m k)
          * ((m k).descFactorial k * Nat.factorial (n - k)) ^ d) : ℕ) : ℝ≥0∞)
          / ((Nat.factorial n ^ d : ℕ) : ℝ≥0∞) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [hsumdiv]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by
    have := (Finset.mem_Ico.1 hk).2
    omega
  exact term_eq_div hkn

/-- The exact finite union-bound certificate obtained from the canonical failure profile. -/
noncomputable def permutationExpansionFailureBound (S : Setting) (n d : ℕ) : ℝ≥0∞ :=
  ((∑ k ∈ Finset.Ico 1 (n + 1), n.choose k *
        (n.choose (canonicalFailureProfile S n k) *
          ((canonicalFailureProfile S n k).descFactorial k * Nat.factorial (n - k)) ^ d) : ℕ) :
      ℝ≥0∞) /
    ((Nat.factorial n ^ d : ℕ) : ℝ≥0∞)

/-- A random permutation interlayer fails expansion with probability at most the exact
canonical union-bound expression.  This theorem is uniform in both width and degree. -/
theorem permutationExpansion_failure_le_canonical (S : Setting) (n d : ℕ) :
    probabilityOf (PermutationInterlayer.uniformLaw n d) (fun P => ¬ P.Expands S) ≤
      permutationExpansionFailureBound S n d := by
  exact permutationExpansion_failure_le_ratio S n d (canonicalFailureProfile S n)
    (canonicalFailureProfile_spec S n) (canonicalFailureProfile_le S n)

/-- Consequently, a random permutation interlayer realizes the setting with failure at
most the canonical finite union bound. -/
theorem permutationExpansion_canonical_whp (S : Setting) (n d : ℕ) :
    PermutationExpansionWhpClaim S n d (permutationExpansionFailureBound S n d) := by
  exact holdsWithFailureAtMost_of_compl_le _ _
    (permutationExpansion_failure_le_canonical S n d)

end Concrete
end ProofOfSpace

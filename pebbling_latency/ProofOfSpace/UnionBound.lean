import ProofOfSpace.PortModel

/-! # Finite uniform probabilities and permutation counting

The Chung port-model union bound uses these finite counting lemmas.
-/

namespace ProofOfSpace
namespace Concrete

open Finset
open scoped ENNReal

/-! ### Probabilities of a finite uniform law -/

variable {A : Type*}
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

/-- The chance that a uniform permutation carries a `k`-set into an `m`-set. -/
noncomputable def hitProb (n k m : ℕ) : ℝ≥0∞ :=
  (m.descFactorial k : ℝ≥0∞) / (n.descFactorial k : ℝ≥0∞)

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


end Concrete
end ProofOfSpace

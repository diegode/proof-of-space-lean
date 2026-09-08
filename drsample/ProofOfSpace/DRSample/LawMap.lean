import ProofOfSpace.DRSample.ProductLaw

/-! # Finite mixtures, pushforwards, and independent families -/
namespace ProofOfSpace.DRSample.FiniteLaw
open Finset Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def pure (a : α) : FiniteLaw α where
  weight b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  total := by simp

noncomputable def bind (p : FiniteLaw α) (q : α → FiniteLaw β) : FiniteLaw β where
  weight b := ∑ a, p.weight a * (q a).weight b
  nonneg b := sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b)
  total := by
    rw [sum_comm]
    simp_rw [← mul_sum, total, mul_one]
    exact p.total

noncomputable def map (p : FiniteLaw α) (f : α → β) : FiniteLaw β := p.bind fun a => pure (f a)

theorem expectation_bind (p : FiniteLaw α) (q : α → FiniteLaw β) (f : β → ℝ) :
    (p.bind q).expectation f = p.expectation (fun a => (q a).expectation f) := by
  unfold expectation bind
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

@[simp] theorem expectation_pure (a : α) (f : α → ℝ) :
    (pure a).expectation f = f a := by
  simp [expectation, pure, ite_mul]

theorem expectation_map (p : FiniteLaw α) (g : α → β) (f : β → ℝ) :
    (p.map g).expectation f = p.expectation (fun a => f (g a)) := by
  simp [map, expectation_bind]

theorem probability_eq_expectation (p : FiniteLaw α) (Q : α → Prop) :
    p.probability Q = p.expectation (fun a => if Q a then 1 else 0) := by
  unfold probability expectation
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem probability_map (p : FiniteLaw α) (f : α → β) (Q : β → Prop) :
    (p.map f).probability Q = p.probability (fun a => Q (f a)) := by
  rw [probability_eq_expectation, expectation_map, probability_eq_expectation]

theorem probability_bind (p : FiniteLaw α) (q : α → FiniteLaw β) (Q : β → Prop) :
    (p.bind q).probability Q = p.expectation (fun a => (q a).probability Q) := by
  simp_rw [probability_eq_expectation, expectation_bind]

@[simp] theorem probability_true (p : FiniteLaw α) : p.probability (fun _ => True) = 1 := by
  simp [probability, p.total]

@[simp] theorem probability_false (p : FiniteLaw α) : p.probability (fun _ => False) = 0 := by
  simp [probability]

noncomputable def uniformOn (s : Finset α) (hs : s.Nonempty) : FiniteLaw α where
  weight a := if a ∈ s then 1 / s.card else 0
  nonneg a := by split_ifs <;> positivity
  total := by
    rw [← sum_filter]
    have heq : univ.filter (fun a => a ∈ s) = s := by ext a; simp
    rw [heq, sum_const, nsmul_eq_mul]
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hs).ne'
    field_simp

@[simp] theorem probability_singleton (p : FiniteLaw α) (a : α) :
    p.probability (fun b => b = a) = p.weight a := by simp [probability]

theorem bind_weight_ge (p : FiniteLaw α) (q : α → FiniteLaw β) (a : α) (b : β) :
    p.weight a * (q a).weight b ≤ (p.bind q).weight b :=
  single_le_sum (fun c _ => mul_nonneg (p.nonneg c) ((q c).nonneg b)) (mem_univ a)

noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight s := ∏ i, (p i).weight (s i)
  nonneg s := prod_nonneg fun i _ => (p i).nonneg _
  total := by
    rw [← Fintype.prod_sum]
    simp [total]

theorem expectation_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteLaw α)
    (f : ι → α → ℝ) :
    (pi p).expectation (fun s => ∏ i, f i (s i)) = ∏ i, (p i).expectation (f i) := by
  unfold expectation pi
  simp_rw [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a * f i a)).symm

theorem probability_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteLaw α)
    (Q : ι → α → Prop) :
    (pi p).probability (fun s => ∀ i, Q i (s i)) = ∏ i, (p i).probability (Q i) := by
  classical
  simp_rw [probability_eq_expectation]
  have heq : (fun s : ι → α => if ∀ i, Q i (s i) then (1 : ℝ) else 0) =
      (fun s => ∏ i, if Q i (s i) then (1 : ℝ) else 0) := by
    funext s
    by_cases h : ∀ i, Q i (s i)
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (fun hall => hi (hall i))]
      symm
      exact prod_eq_zero (mem_univ i) (if_neg hi)
  have hh := congrArg (pi p).expectation heq
  convert hh.trans (expectation_pi_product p (fun i a => if Q i a then 1 else 0)) using 1
  congr 1
  funext s
  split_ifs <;> rfl

end ProofOfSpace.DRSample.FiniteLaw

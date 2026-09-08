import ProofOfSpace.DRSample.FiniteLaw

/-! # Finite products and sequential exponential moments -/
namespace ProofOfSpace.DRSample
open Finset

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def product (p : FiniteLaw α) (q : FiniteLaw β) : FiniteLaw (α × β) where
  weight x := p.weight x.1 * q.weight x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, q.total, mul_one]
    exact p.total

theorem expectation_product (p : FiniteLaw α) (q : FiniteLaw β) (f : α × β → ℝ) :
    (p.product q).expectation f = p.expectation (fun a => q.expectation (fun b => f (a, b))) := by
  unfold expectation product
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem expectation_const_mul (p : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    p.expectation (fun a => c * f a) = c * p.expectation f := by
  unfold expectation
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

@[simp] theorem expectation_const (p : FiniteLaw α) (c : ℝ) :
    p.expectation (fun _ => c) = c := by
  unfold expectation
  rw [← sum_mul, p.total, one_mul]

end FiniteLaw

universe u
/-- A finite sequence of independent choices, built from left to right. -/
@[reducible] def SampleSpace (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => SampleSpace α n × α

@[reducible] instance sampleSpaceFintype {α : Type*} [Fintype α] :
    (n : ℕ) → Fintype (SampleSpace α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (SampleSpace α n) α (sampleSpaceFintype n) inferInstance

noncomputable def independentSamples {α : Type*} [Fintype α]
    (p : ℕ → FiniteLaw α) : (n : ℕ) → FiniteLaw (SampleSpace α n)
  | 0 => ⟨fun _ => 1, by intro; norm_num, by simp [SampleSpace]⟩
  | n + 1 => (independentSamples p n).product (p n)

noncomputable def accumulated {α : Type*}
    (increment : (n : ℕ) → SampleSpace α (n + 1) → ℝ) :
    (n : ℕ) → SampleSpace α n → ℝ
  | 0, _ => 0
  | n + 1, s => accumulated increment n s.1 + increment n s

/-- Iterated conditioning, proved by finite sums. Increments may depend on the
entire previously exposed history, not just the latest independent choice. -/
theorem accumulated_moment {α : Type*} [Fintype α] (p : ℕ → FiniteLaw α)
    (increment : (n : ℕ) → SampleSpace α (n + 1) → ℝ) (theta : ℝ)
    (factor : ℕ → ℝ) (hfactor : ∀ n, 0 ≤ factor n)
    (hstep : ∀ n (past : SampleSpace α n),
      (p n).expectation (fun a => Real.exp (theta * increment n (past, a))) ≤ factor n)
    (n : ℕ) :
    (independentSamples p n).expectation (fun s => Real.exp (theta * accumulated increment n s)) ≤
      ∏ i ∈ range n, factor i := by
  induction n with
  | zero => simp [independentSamples, accumulated, FiniteLaw.expectation, SampleSpace]
  | succ n ih =>
    rw [independentSamples, FiniteLaw.expectation_product, prod_range_succ]
    have hinside (past : SampleSpace α n) :
        (p n).expectation (fun a => Real.exp (theta * accumulated increment (n + 1) (past, a))) ≤
          factor n * Real.exp (theta * accumulated increment n past) := by
      simp only [accumulated, mul_add, Real.exp_add]
      rw [FiniteLaw.expectation_const_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hstep n past) (Real.exp_pos _).le
    calc (independentSamples p n).expectation
          (fun past => (p n).expectation (fun a => Real.exp (theta * accumulated increment (n + 1) (past, a))))
        ≤ (independentSamples p n).expectation
          (fun past => factor n * Real.exp (theta * accumulated increment n past)) :=
            FiniteLaw.expectation_mono _ hinside
      _ = factor n * (independentSamples p n).expectation
          (fun s => Real.exp (theta * accumulated increment n s)) :=
            FiniteLaw.expectation_const_mul _ _ _
      _ ≤ (∏ i ∈ range n, factor i) * factor n := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left ih (hfactor n)

end ProofOfSpace.DRSample

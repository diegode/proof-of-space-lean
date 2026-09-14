import ProofOfSpace.DRSample.RowGraph
import ProofOfSpace.DRSample.Samplers

/-! # The grouped sampling law and its incomplete final row -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem FiniteLaw.probability_product_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q : FiniteLaw β) (Q : α → Prop) :
    (p.product q).probability (fun s => Q s.1) = p.probability Q := by
  unfold probability product
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  by_cases ha : Q a
  · simp [ha, ← mul_sum, q.total]
  · simp [ha]

/-- The last sampled row supplies the incomplete suffix. Extra choices past
vertex `n-1` are ignored. Every genuine vertex has its prescribed incoming law. -/
noncomputable def graphLaw {n : ℕ} (m : ℕ) (p : ℕ → FiniteLaw (Finset (Fin n))) :
    FiniteLaw (SampleSpace (Fin m → Finset (Fin n)) (n / m + 1)) :=
  independentSamples (rowLaw m p) (n / m + 1)

end ProofOfSpace.DRSample

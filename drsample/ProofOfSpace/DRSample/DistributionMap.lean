import ProofOfSpace.DRSample.Conjectures
import Mathlib.Algebra.BigOperators.Fin

/-! # The row-based proof law agrees with independent choices at every vertex -/
namespace ProofOfSpace.DRSample
open Finset Classical

namespace FiniteLaw
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

@[ext] theorem ext_weights {p q : FiniteLaw α} (h : ∀ a, p.weight a = q.weight a) : p = q := by
  cases p; cases q
  congr
  exact funext h

theorem map_comp (p : FiniteLaw α) (f : α → β) {γ : Type*} [Fintype γ] (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  apply ext_weights
  intro c
  simp only [← probability_singleton, probability_map, Function.comp_def]

theorem probability_product (p : FiniteLaw α) (q : FiniteLaw β)
    (P : α → Prop) (Q : β → Prop) :
    (p.product q).probability (fun s => P s.1 ∧ Q s.2) = p.probability P * q.probability Q := by
  unfold probability product
  rw [Fintype.sum_prod_type, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases hP : P a <;> by_cases hQ : Q b <;> simp [hP, hQ]

theorem pi_map [DecidableEq ι] (p : ι → FiniteLaw α) (f : ι → α → β) :
    (pi p).map (fun s i => f i (s i)) = pi (fun i => (p i).map (f i)) := by
  apply ext_weights
  intro t
  rw [← probability_singleton, probability_map]
  simp only [funext_iff]
  rw [probability_pi p (fun i a => f i a = t i)]
  change _ = ∏ i, ((p i).map (f i)).weight (t i)
  apply prod_congr rfl
  intro i _
  rw [← probability_singleton, probability_map]

theorem pi_map_injective [DecidableEq ι] [DecidableEq κ]
    (p : ι → FiniteLaw α) (f : κ → ι) (hf : Function.Injective f) :
    (pi p).map (fun s j => s (f j)) = pi (fun j => p (f j)) := by
  apply ext_weights
  intro t
  rw [← probability_singleton, probability_map]
  have he : (fun s : ι → α => (fun j => s (f j)) = t) =
      (fun s => ∀ i, ∀ j, f j = i → s i = t j) := by
    funext s
    apply propext
    simp only [funext_iff]
    constructor
    · intro h i j he; subst i; exact h j
    · intro h j; exact h (f j) j rfl
  rw [he, probability_pi p (fun i a => ∀ j, f j = i → a = t j)]
  change (∏ i, (p i).probability (fun a => ∀ j, f j = i → a = t j)) =
    ∏ j, (p (f j)).weight (t j)
  have hsub : (univ.image f) ⊆ (univ : Finset ι) := subset_univ _
  rw [← prod_subset hsub (by
    intro i _ hi
    have hn : ∀ j, f j ≠ i := by simpa using hi
    simp [hn])]
  rw [prod_image (fun _ _ _ _ h => hf h)]
  apply prod_congr rfl
  intro j _
  simp only [hf.eq_iff]
  simp

theorem pi_uncurry [DecidableEq ι] [DecidableEq κ]
    (p : ι → κ → FiniteLaw α) :
    (pi (fun i => pi (p i))).map (fun s (ik : ι × κ) => s ik.1 ik.2) =
      pi (fun ik : ι × κ => p ik.1 ik.2) := by
  apply ext_weights
  intro t
  rw [← probability_singleton, probability_map]
  have he : (fun s : ι → κ → α => (fun ik : ι × κ => s ik.1 ik.2) = t) =
      (fun s => ∀ i, ∀ k, s i k = t (i, k)) := by
    funext s
    apply propext
    simp [funext_iff, Prod.forall]
  rw [he, probability_pi (fun i => pi (p i)) (fun i a => ∀ k, a k = t (i, k))]
  have hpoint (i : ι) : (pi (p i)).probability (fun s => ∀ k, s k = t (i, k)) =
      ∏ k, (p i k).weight (t (i, k)) := by
    rw [probability_pi (p i) (fun k a => a = t (i, k))]
    simp only [probability_singleton]
  simp_rw [hpoint]
  exact (Fintype.prod_prod_type (fun ik : ι × κ => (p ik.1 ik.2).weight (t ik))).symm

end FiniteLaw

/-- Replacing the nested tuple of samples by a function does not change its law. -/
theorem independentSamples_as_pi {α : Type*} [Fintype α] (fallback : α)
    (p : ℕ → FiniteLaw α) (R : ℕ) :
    (independentSamples p R).map (fun s (j : Fin R) => getSample fallback R s j.val) =
      FiniteLaw.pi (fun j : Fin R => p j.val) := by
  induction R with
  | zero =>
    apply FiniteLaw.ext_weights
    intro t
    have ht : ∀ s : SampleSpace α 0, (fun j : Fin 0 => getSample fallback 0 s j.val) = t :=
      fun _ => funext fun j => Fin.elim0 j
    simp [FiniteLaw.map, FiniteLaw.bind, FiniteLaw.pure, independentSamples, FiniteLaw.pi, ht]
  | succ R ih =>
    apply FiniteLaw.ext_weights
    intro t
    rw [← FiniteLaw.probability_singleton, FiniteLaw.probability_map]
    have he : (fun s : SampleSpace α (R + 1) =>
        (fun j : Fin (R + 1) => getSample fallback (R + 1) s j.val) = t) =
        (fun s => (fun j : Fin R => getSample fallback R s.1 j.val) =
          (fun j => t j.castSucc) ∧ s.2 = t (Fin.last R)) := by
      funext s
      apply propext
      simp only [funext_iff]
      constructor
      · intro h
        constructor
        · intro j
          simpa [getSample, Nat.ne_of_lt j.isLt] using h j.castSucc
        · simpa [getSample] using h (Fin.last R)
      · rintro ⟨h, hl⟩ j
        by_cases hj : j.val = R
        · have heq : j = Fin.last R := Fin.ext hj
          subst j
          simpa [getSample] using hl
        · have hjR : j.val < R := by omega
          simpa [getSample, hj] using h ⟨j.val, hjR⟩
    rw [he, independentSamples, FiniteLaw.probability_product _ _
      (fun s => (fun j : Fin R => getSample fallback R s j.val) = fun j => t j.castSucc)
      (fun a => a = t (Fin.last R))]
    rw [← FiniteLaw.probability_map (independentSamples p R)
      (fun s (j : Fin R) => getSample fallback R s j.val)
      (fun f => f = fun j => t j.castSucc), ih, FiniteLaw.probability_singleton,
      FiniteLaw.probability_singleton]
    exact (Fin.prod_univ_castSucc (fun j : Fin (R + 1) => (p j.val).weight (t j))).symm

/-- Every genuine destination retrieves one coordinate of the row sample. -/
def vertexCoordinate {n m : ℕ} (hm : 0 < m) (v : Fin n) : Fin (n / m + 1) × Fin m :=
  (⟨v.val / m, by have : v.val / m ≤ n / m := Nat.div_le_div_right v.isLt.le; omega⟩,
    ⟨v.val % m, Nat.mod_lt _ hm⟩)

theorem vertexCoordinate_injective {n m : ℕ} (hm : 0 < m) :
    Function.Injective (vertexCoordinate (n := n) hm) := by
  intro u v h
  have hq := congrArg (fun p => p.1.val) h
  have hr := congrArg (fun p => p.2.val) h
  apply Fin.ext
  have hu := Nat.div_add_mod u.val m
  have hv := Nat.div_add_mod v.val m
  dsimp [vertexCoordinate] at hq hr
  rw [hq, hr] at hu
  exact hu.symm.trans hv

/-- The original graph's incoming sets have precisely the independent vertex law. -/
theorem graphLaw_as_pi {n m : ℕ} (hm : 0 < m)
    (p : ℕ → FiniteLaw (Finset (Fin n))) :
    (graphLaw m p).map (fun s (v : Fin n) =>
      getSample (fun _ => ∅) (n / m + 1) s (v.val / m) ⟨v.val % m, Nat.mod_lt _ hm⟩) =
      FiniteLaw.pi (fun v : Fin n => p v.val) := by
  have hrows := independentSamples_as_pi (fun _ : Fin m => (∅ : Finset (Fin n)))
    (rowLaw m p) (n / m + 1)
  have hflat := congrArg (fun law => law.map
    (fun rows (jk : Fin (n / m + 1) × Fin m) => rows jk.1 jk.2)) hrows
  rw [FiniteLaw.map_comp] at hflat
  change _ = (FiniteLaw.pi (fun j : Fin (n / m + 1) =>
    FiniteLaw.pi (fun k : Fin m => p (j.val * m + k.val)))).map _ at hflat
  rw [FiniteLaw.pi_uncurry] at hflat
  have hrestrict := congrArg (fun law => law.map
    (fun choices v => choices (vertexCoordinate hm v))) hflat
  rw [FiniteLaw.map_comp, FiniteLaw.pi_map_injective _ _ (vertexCoordinate_injective hm)] at hrestrict
  have hindex (v : Fin n) : v.val / m * m + v.val % m = v.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod v.val m
  simpa only [Function.comp_def, vertexCoordinate, hindex, graphLaw] using hrestrict

end ProofOfSpace.DRSample

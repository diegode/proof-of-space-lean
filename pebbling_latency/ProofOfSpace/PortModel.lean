/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import Mathlib.Probability.Distributions.Uniform

/-! # Chung port permutations and their probability law -/
namespace ProofOfSpace.Concrete
open Finset Set
open scoped ENNReal
variable {n : ℕ}

/-! ### Chung's one-permutation port model -/

/-- A degree-eight Chung interlayer is one permutation of all `8n` ports.  This is the
sampling model in Appendix A of Reyzin's paper; it is not a tuple of eight vertex
permutations. -/
structure PortInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)
deriving Fintype

instance : Nonempty (PortInterlayer n) := ⟨⟨Equiv.refl _⟩⟩

namespace PortInterlayer

/-- All eight ports belonging to the vertices in `T`. -/
def ports (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

@[simp] theorem card_ports (T : Finset (Fin n)) : (ports T).card = 8 * T.card := by
  simp [ports]

/-- Distinct predecessor vertices hit by the permuted ports of `T`. -/
def neighborhood (P : PortInterlayer n) (T : Finset (Fin n)) : Finset (Fin n) :=
  (ports T).image fun q => (P.perm q).2

end PortInterlayer

/-- Probability assigned to a property by a finite sampler.  This is the interface used
to state finite-size and high-probability claims without replacing them by existential
seed claims. -/
noncomputable def probabilityOf {A : Type*} (p : PMF A) (P : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if P a then p a else 0

/-- A conventional finite failure-probability formulation of "with high probability". -/
def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (P : A → Prop) (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p P

noncomputable def PortInterlayer.uniformLaw (n : ℕ) : PMF (PortInterlayer n) :=
  PMF.uniformOfFintype (PortInterlayer n)

end ProofOfSpace.Concrete

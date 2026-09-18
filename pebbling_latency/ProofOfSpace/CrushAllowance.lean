/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Transition
import Mathlib.Data.Finset.Max
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # The September 18 crush allowance

The allowance optimizes the certificate over integer kill lengths, with strict
budget feasibility for every nonempty plan. The empty plan is always available,
including at zero remaining budget. This file proves the finite optimization
and its accounting interface; it does not postulate graph transitions.
-/

namespace ProofOfSpace.Crush
open Set

def cost (K g : ℝ) (m : ℕ) : ℝ := K + ((m : ℝ) + 1) * g

noncomputable def worth (τ : ℝ → ℝ) (p K g : ℝ) (m : ℕ) : ℝ :=
  τ (p - K - (m : ℝ) * g) - K / g

def spending (K g : ℝ) (ms : List ℕ) : ℝ := (ms.map (cost K g)).sum

noncomputable def credit (τ : ℝ → ℝ) (p K g : ℝ) (ms : List ℕ) : ℝ :=
  (ms.map (worth τ p K g)).sum

/-- The no-crush case must not require `0 < B`. -/
def Admissible (K g B : ℝ) (ms : List ℕ) : Prop :=
  (∀ m ∈ ms, 1 ≤ m) ∧ (ms = [] ∨ spending K g ms < B)

@[simp] theorem admissible_nil (K g B : ℝ) : Admissible K g B [] := by
  simp [Admissible]

theorem spending_nonneg {K g : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (ms : List ℕ) :
    0 ≤ spending K g ms := by
  induction ms with
  | nil => simp [spending]
  | cons m ms ih =>
    simp only [spending, List.map_cons, List.sum_cons] at *
    have : 0 ≤ cost K g m := by unfold cost; positivity
    linarith

theorem length_cost_le {K g : ℝ} (_hK : 0 ≤ K) (hg : 0 ≤ g)
    {ms : List ℕ} (hm : ∀ m ∈ ms, 1 ≤ m) :
    (ms.length : ℝ) * (K + 2 * g) ≤ spending K g ms := by
  induction ms with
  | nil => simp [spending]
  | cons m ms ih =>
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm m (by simp)
    have ht := ih (fun n hn => hm n (by simp [hn]))
    simp only [spending, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] at *
    dsimp [cost] at *
    nlinarith

theorem member_cost_le {K g : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g)
    {ms : List ℕ} {m : ℕ} (hm : m ∈ ms) : cost K g m ≤ spending K g ms := by
  induction ms with
  | nil => simp at hm
  | cons n ns ih =>
    simp only [List.mem_cons] at hm
    simp only [spending, List.map_cons, List.sum_cons]
    rcases hm with rfl | hm
    · have ht := spending_nonneg hK hg ns
      dsimp [spending] at ht
      linarith
    · have := ih hm
      have : 0 ≤ cost K g n := by unfold cost; positivity
      dsimp [spending] at *
      linarith

/-- Finite container: all lists of length at most `N`, with entries at most `M`. -/
def plans : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | N + 1, M => insert [] ((Finset.range (M + 1)).biUnion
      (fun m => (plans N M).image (List.cons m)))

theorem mem_plans {N M : ℕ} {ms : List ℕ} :
    ms ∈ plans N M ↔ ms.length ≤ N ∧ ∀ m ∈ ms, m ≤ M := by
  induction N generalizing ms with
  | zero => cases ms <;> simp [plans]
  | succ N ih =>
    cases ms with
    | nil => simp [plans]
    | cons m ms =>
      simp [plans, ih, and_assoc, and_left_comm]

theorem admissible_spending_le {K g B : ℝ} (hB : 0 ≤ B)
    {ms : List ℕ} (h : Admissible K g B ms) : spending K g ms ≤ B := by
  rcases h.2 with rfl | h
  · simpa [spending] using hB
  · exact h.le

theorem admissible_bounded {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g)
    (hB : 0 ≤ B) {ms : List ℕ} (h : Admissible K g B ms) :
    ms ∈ plans ⌈B / g⌉₊ ⌈B / g⌉₊ := by
  have hcap : B ≤ (⌈B / g⌉₊ : ℝ) * g :=
    (div_le_iff₀ hg).mp (Nat.le_ceil (B / g))
  have hsp := admissible_spending_le hB h
  apply mem_plans.mpr
  constructor
  · have hl := length_cost_le hK hg.le h.1
    have : (ms.length : ℝ) ≤ (⌈B / g⌉₊ : ℝ) := by nlinarith
    exact_mod_cast this
  · intro m hm
    have hc := member_cost_le hK hg.le hm
    dsimp [cost] at hc
    have : (m : ℝ) ≤ (⌈B / g⌉₊ : ℝ) := by nlinarith
    exact_mod_cast this

def values (τ : ℝ → ℝ) (p K g B : ℝ) : Set ℝ :=
  {c | ∃ ms, Admissible K g B ms ∧ credit τ p K g ms = c}

theorem values_finite {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g) (hB : 0 ≤ B)
    (τ : ℝ → ℝ) (p : ℝ) : (values τ p K g B).Finite := by
  apply ((plans ⌈B / g⌉₊ ⌈B / g⌉₊).finite_toSet.image (credit τ p K g)).subset
  rintro c ⟨ms, h, rfl⟩
  exact ⟨ms, admissible_bounded hK hg hB h, rfl⟩

theorem zero_mem_values (τ : ℝ → ℝ) (p K g B : ℝ) : 0 ∈ values τ p K g B :=
  ⟨[], admissible_nil K g B, by simp [credit]⟩

noncomputable def allowance (τ : ℝ → ℝ) (p K g B : ℝ) : ℝ :=
  sSup (values τ p K g B)

theorem allowance_isGreatest {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g) (hB : 0 ≤ B)
    (τ : ℝ → ℝ) (p : ℝ) : IsGreatest (values τ p K g B) (allowance τ p K g B) := by
  have hf := values_finite hK hg hB τ p
  have hn : (values τ p K g B).Nonempty := ⟨0, zero_mem_values τ p K g B⟩
  exact ⟨hn.csSup_mem hf, fun _ hx => le_csSup hf.bddAbove hx⟩

theorem credit_le_allowance {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g) (hB : 0 ≤ B)
    (τ : ℝ → ℝ) (p : ℝ) {ms : List ℕ} (h : Admissible K g B ms) :
    credit τ p K g ms ≤ allowance τ p K g B :=
  (allowance_isGreatest hK hg hB τ p).2 ⟨ms, h, rfl⟩

theorem allowance_nonneg {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g) (hB : 0 ≤ B)
    (τ : ℝ → ℝ) (p : ℝ) : 0 ≤ allowance τ p K g B :=
  (allowance_isGreatest hK hg hB τ p).2 (zero_mem_values τ p K g B)

theorem allowance_mono {K g B C : ℝ} (hK : 0 ≤ K) (hg : 0 < g)
    (hB : 0 ≤ B) (hBC : B ≤ C) (τ : ℝ → ℝ) (p : ℝ) :
    allowance τ p K g B ≤ allowance τ p K g C := by
  obtain ⟨ms, hm, he⟩ := (allowance_isGreatest hK hg hB τ p).1
  rw [← he]
  apply credit_le_allowance hK hg (hB.trans hBC)
  exact ⟨hm.1, hm.2.imp id (fun h => h.trans_le hBC)⟩

/-- All positive initial depths have the same base certificate. Hence the
cost-model maximum needs only depth one among those depths. -/
theorem positive_base_le_one {K g ρ c : ℝ} (hK : 0 ≤ K) (hg : 0 < g)
    (τ : ℝ → ℝ) (p : ℝ) {b : ℕ} (hb : 1 ≤ b)
    (hB : 0 ≤ ρ - ((b : ℝ) - c) * g) :
    c + allowance τ p K g (ρ - ((b : ℝ) - c) * g) ≤
      c + allowance τ p K g (ρ - (1 - c) * g) := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbudget : ρ - ((b : ℝ) - c) * g ≤ ρ - (1 - c) * g := by nlinarith
  have := allowance_mono hK hg hB hbudget τ p
  linarith

/-- Restrict the paper's maximum to admissible lengths so `τ` is in its domain. -/
theorem worth_argument_mem {a p K g B : ℝ} {m : ℕ}
    (hK : 0 ≤ K) (hg : 0 < g) (_hm : 1 ≤ m)
    (hfloor : a ≤ p + g - B) (hcost : cost K g m < B) :
    p - K - (m : ℝ) * g ∈ Icc a p := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp [cost] at hcost
  constructor <;> nlinarith

/-- Filecoin's regime permits at most one crush. -/
theorem at_most_one {K g B : ℝ} (hK : 0 ≤ K) (hg : 0 < g)
    (hcap : B ≤ 2 * (K + 2 * g)) {ms : List ℕ} (h : Admissible K g B ms) :
    ms = [] ∨ ∃ m, ms = [m] ∧ 1 ≤ m ∧ cost K g m < B := by
  rcases h.2 with he | hb
  · exact Or.inl he
  · have hl := length_cost_le hK hg.le h.1
    have hlen : ms.length < 2 := by
      have : (ms.length : ℝ) < 2 := by nlinarith
      exact_mod_cast this
    cases ms with
    | nil => exact Or.inl rfl
    | cons m ms =>
      cases ms with
      | nil => exact Or.inr ⟨m, rfl, h.1 m (by simp), by simpa [spending] using hb⟩
      | cons n ns => simp at hlen

theorem allowance_zero {K g : ℝ} (hK : 0 ≤ K) (hg : 0 < g)
    (τ : ℝ → ℝ) (p : ℝ) : allowance τ p K g 0 = 0 := by
  have hmax := allowance_isGreatest hK hg (by rfl : (0 : ℝ) ≤ 0) τ p
  obtain ⟨ms, hm, he⟩ := hmax.1
  rcases hm.2 with rfl | hneg
  · simpa [credit] using he.symm
  · exact (not_lt_of_ge (spending_nonneg hK hg.le ms) hneg).elim

end ProofOfSpace.Crush

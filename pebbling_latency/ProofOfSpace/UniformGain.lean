/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring

/-! # Uniform-gain scalar amplification

The affine accounting is internal. The graph theorem supplies only interval
expansion, depth robustness, and the black/red budgets.
-/

namespace ProofOfSpace.UniformGain

open Finset Set
universe u

structure Parameters where
  p : ℝ
  σ : ℝ
  g : ℝ
  h : ℝ
  w : ℝ
  ρ : ℝ
  g_pos : 0 < g
  rho_nonneg : 0 ≤ ρ
  a_pos : 0 < min w (p + g) - ρ
  a_le_source : min w (p + g) - ρ ≤ σ
  source_le_p : σ ≤ p
  h_le : h ≤ p + g
  source_guard : min w (p + g) - ρ + 2 * g ≤ h

namespace Parameters

variable (S : Parameters)

def a : ℝ := min S.w (S.p + S.g) - S.ρ
def U : ℝ := S.p + S.g
def K : ℝ := S.h - S.a - 2 * S.g
def C : ℝ := S.p + 2 * S.g - S.h

theorem K_nonneg : 0 ≤ S.K := by
  have := S.source_guard
  dsimp [K, a]; linarith

theorem C_pos : 0 < S.C := by
  have := S.h_le; have := S.g_pos
  dsimp [C]; linarith

theorem a_le_p : S.a ≤ S.p := S.a_le_source.trans S.source_le_p
theorem a_le_U : S.a ≤ S.U := by
  have := S.a_le_p; have := S.g_pos; dsimp [U]; linarith
theorem U_pos : 0 < S.U := S.a_pos.trans_le S.a_le_U
theorem a_le_U_sub_rho : S.a ≤ S.U - S.ρ :=
  sub_le_sub_right (min_le_right _ _) _

theorem accounting_identity :
    max 0 (S.U - S.w) + S.ρ + max 0 (S.ρ - S.K) =
      S.ρ + S.g + max (S.p - S.w) S.C := by
  have hg := S.g_pos.le
  have hh := S.h_le
  dsimp [U, K, a, C]
  rcases le_total S.w (S.p + S.g) with hw | hw
  · rw [min_eq_left hw, max_eq_right (by linarith)]
    by_cases hx : 0 ≤ S.w - S.h + 2 * S.g
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right hw, max_eq_left (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith)]; ring

end Parameters

/-- Cumulative black spending. `B t` counts depths strictly below `t`. -/
structure Budget (S : Parameters) where
  B : ℕ → ℝ
  zero : B 0 = 0
  mono : Monotone B
  bound : ∀ t, B t ≤ S.ρ

namespace Budget

variable {S : Parameters} (B : Budget S)

def r (t : ℕ) : ℝ := B.B (t + 1) - B.B t

theorem nonneg (t : ℕ) : 0 ≤ B.B t := by
  have := B.mono (Nat.zero_le t); rwa [B.zero] at this

theorem r_nonneg (t : ℕ) : 0 ≤ B.r t := sub_nonneg.mpr (B.mono (by omega))

theorem diff_nonneg {t u : ℕ} (htu : t ≤ u) : 0 ≤ B.B u - B.B t :=
  sub_nonneg.mpr (B.mono htu)

theorem diff_le_rho (t u : ℕ) : B.B u - B.B t ≤ S.ρ := by
  have := B.nonneg t; have := B.bound u; linarith

def Expandable (t : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → B.B (t + k + 1) - B.B (t + 1) ≤
    ((k : ℝ) + 1) * S.g + S.K

end Budget

/-- The capped free expansion map. -/
structure Growth (S : Parameters) where
  F : ℝ → ℝ
  cap : ∀ x ∈ Icc S.a S.U, F x ≤ S.U
  grow : ∀ x ∈ Icc S.a S.U, min S.U (x + S.g) ≤ F x
  source : S.h ≤ F S.σ

namespace Growth

variable {S : Parameters} (F : Growth S) (B : Budget S)

theorem nondecreasing_step {x : ℝ} (hx : x ∈ Icc S.a S.U) : x ≤ F.F x := by
  exact (le_min hx.2 (by linarith [S.g_pos])).trans (F.grow x hx)

theorem fertile {x : ℝ} (hx : x ∈ Icc S.a S.U) (hp : S.p ≤ x) : F.F x = S.U := by
  apply le_antisymm (F.cap x hx)
  have hu : S.U ≤ x + S.g := by dsimp [Parameters.U]; linarith
  simpa only [min_eq_left hu] using F.grow x hx

noncomputable def orbit (t : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => max 0 (F.F (orbit t x k) - B.r (t + k + 1))

theorem orbit_step (t : ℕ) (x : ℝ) (k : ℕ) :
    F.F (F.orbit B t x k) - B.r (t + k + 1) ≤ F.orbit B t x (k + 1) :=
  le_max_right _ _

theorem orbit_cap {t k : ℕ} {x : ℝ}
    (hx : F.orbit B t x k ∈ Icc S.a S.U) : F.orbit B t x (k + 1) ≤ S.U := by
  apply max_le S.U_pos.le
  have := F.cap _ hx; have := B.r_nonneg (t + k + 1); linarith

/-- Initial challenge growth pays every black pebble once. -/
theorem challenge_orbit (k : ℕ) :
    let x := min S.U (S.w - B.B 1)
    F.orbit B 0 x k ∈ Icc S.a S.U ∧
      min S.U S.w - B.B (k + 1) ≤ F.orbit B 0 x k := by
  dsimp only
  induction k with
  | zero =>
    dsimp [orbit]
    have hB := B.nonneg 1
    have hR := B.bound 1
    have ha := S.a_le_U
    have hw : S.a ≤ S.w - S.ρ := sub_le_sub_right (min_le_left _ _) _
    refine ⟨⟨le_min ha (by linarith), min_le_left _ _⟩, ?_⟩
    apply le_min
    · have := min_le_left S.U S.w; linarith
    · have := min_le_right S.U S.w; linarith
  | succ k ih =>
    have hstep := F.orbit_step B 0 (min S.U (S.w - B.B 1)) k
    have hgrow := F.nondecreasing_step ih.1
    have hlo : min S.U S.w - B.B (k + 1 + 1) ≤
        F.orbit B 0 (min S.U (S.w - B.B 1)) (k + 1) := by
      dsimp [Budget.r] at hstep
      simp only [Nat.zero_add] at hstep
      linarith [ih.2]
    refine ⟨⟨?_, F.orbit_cap B ih.1⟩, hlo⟩
    have hR := B.bound (k + 1 + 1)
    have heq : min S.U S.w - S.ρ = S.a := by
      dsimp [Parameters.a, Parameters.U]; rw [min_comm]
    rw [← heq]; linarith

/-- A source at an expandable depth stays above the same floor. -/
theorem source_orbit (t : ℕ) (hexp : B.Expandable t) (k : ℕ) :
    F.orbit B t S.σ k ∈ Icc S.a S.U ∧
      (0 < k → min S.U (S.h + ((k : ℝ) - 1) * S.g) -
        (B.B (t + k + 1) - B.B (t + 1)) ≤ F.orbit B t S.σ k) := by
  induction k with
  | zero =>
    refine ⟨⟨S.a_le_source, S.source_le_p.trans ?_⟩, by omega⟩
    dsimp [Parameters.U]; linarith [S.g_pos]
  | succ k ih =>
    have hstep := F.orbit_step B t S.σ k
    have hcap := F.orbit_cap B ih.1
    have hR := B.diff_le_rho (t + 1) (t + (k + 1) + 1)
    have hE := hexp (k + 1) (by omega)
    have hg : 0 ≤ S.g := S.g_pos.le
    have hlo : min S.U (S.h + ((k + 1 : ℕ) - 1 : ℝ) * S.g) -
        (B.B (t + (k + 1) + 1) - B.B (t + 1)) ≤
        F.orbit B t S.σ (k + 1) := by
      cases k with
      | zero =>
        simp only [Nat.zero_add, Nat.cast_one, sub_self, zero_mul, add_zero]
        rw [min_eq_right (show S.h ≤ S.U from S.h_le)]
        exact (sub_le_sub_right F.source _).trans (le_max_right _ _)
      | succ k =>
        have hl := ih.2 (by omega)
        have hb := B.diff_nonneg (t := t + 1) (u := t + (k + 1) + 1) (by omega)
        have hfree := F.grow _ ih.1
        dsimp [Budget.r] at hstep
        simp only [Nat.add_assoc] at hstep hb hl ⊢
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hl ⊢
        rw [show (k : ℝ) + (1 + 1) - 1 = (k : ℝ) + 1 by ring]
        have hmin1 := min_le_left S.U (S.h + ((k : ℝ) + 1) * S.g)
        have hmin2 := min_le_right S.U (S.h + ((k : ℝ) + 1) * S.g)
        rcases le_total S.U (S.h + (k : ℝ) * S.g) with ht | ht
        · rw [min_eq_left (by nlinarith)] at hl
          rcases le_total S.U (F.orbit B t S.σ (k + 1) + S.g) with hu | hu
          · rw [min_eq_left hu] at hfree; linarith
          · rw [min_eq_right hu] at hfree; nlinarith
        · rw [min_eq_right (by nlinarith)] at hl
          rcases le_total S.U (F.orbit B t S.σ (k + 1) + S.g) with hu | hu
          · rw [min_eq_left hu] at hfree; linarith
          · rw [min_eq_right hu] at hfree; nlinarith
    refine ⟨⟨?_, hcap⟩, fun _ => hlo⟩
    rw [← min_sub_sub_right] at hlo
    apply le_trans (le_min ?_ ?_) hlo
    · have := S.a_le_U_sub_rho; linarith
    · dsimp [Parameters.K] at hE
      push_cast at hE ⊢
      nlinarith

end Growth

/-- A context remembers the last source and the paths it already carries.
The scalar engine needs only the following physical consequences. -/
structure System {S : Parameters} (F : Growth S) (B : Budget S) (ℓ : ℕ)
    (Result : ℕ → Prop) where
  Context : Type u
  start : Context → ℕ
  count : Context → ℕ
  f : Context → ℕ → ℝ
  mem : ∀ X d, start X ≤ d → f X d ∈ Icc S.a S.U
  step : ∀ X d, start X ≤ d → F.F (f X d) - B.r (d + 1) ≤ f X (d + 1)
  result : ∀ X, 0 < count X → Result (count X)
  next : ∀ X b, start X ≤ b → b < ℓ → S.p ≤ f X b → B.Expandable b →
    ∃ Y, start Y = b + 1 ∧ count Y = count X + 1 ∧
      S.h - B.r (b + 1) ≤ f Y (b + 1)
  initial : Context
  initial_start : start initial = 0
  initial_count : count initial = 0
  initial_bound : S.U - f initial 0 ≤ max 0 (S.U - S.w) + B.B 1

namespace System

variable {S : Parameters} {F : Growth S} {B : Budget S} {ℓ : ℕ}
    {Result : ℕ → Prop} (CS : System F B ℓ Result)

theorem fertile_drop (X : CS.Context) {b : ℕ} (hb : CS.start X ≤ b)
    (hp : S.p ≤ CS.f X b) (k : ℕ) :
    S.U - (B.B (b + k + 2) - B.B (b + 1)) ≤ CS.f X (b + k + 1) := by
  induction k with
  | zero =>
    have hs := CS.step X b hb
    rw [F.fertile (CS.mem X b hb) hp] at hs
    simpa only [Budget.r, Nat.add_zero, Nat.add_assoc] using hs
  | succ k ih =>
    have hs := CS.step X (b + k + 1) (by omega)
    have hg := F.nondecreasing_step (CS.mem X (b + k + 1) (by omega))
    dsimp [Budget.r] at hs
    convert (by linarith : S.U - (B.B (b + k + 1 + 1 + 1) - B.B (b + 1)) ≤
      CS.f X (b + k + 1 + 1)) using 1 <;> congr 1

include CS in
/-- The end-to-end scalar counting theorem, with one global black budget. -/
theorem count_links {z : ℕ} (hz : 1 ≤ z)
    (hmono : ∀ i j, i ≤ j → Result j → Result i)
    (hlevels : S.ρ + S.g + max (S.p - S.w) S.C + ((z : ℝ) - 1) * S.C <
      S.g * ℓ) : Result z := by
  classical
  by_contra hn
  have hcount (X : CS.Context) : CS.count X < z := by
    by_contra h
    have hle : z ≤ CS.count X := by omega
    exact hn (hmono z (CS.count X) hle (CS.result X (by omega)))
  let extra (flag : Bool) (b : ℕ) : ℝ := if flag then B.B (b + 1) - S.K else 0
  have hwalk : ∀ rem b : ℕ, ℓ - b = rem → ∀ (X : CS.Context) (flag : Bool),
      CS.start X ≤ b →
      (b : ℝ) * S.g + (S.U - CS.f X b) ≤
        max 0 (S.U - S.w) + (CS.count X : ℝ) * S.C + B.B (b + 1) + extra flag b →
      False := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | h rem ih =>
      intro b hrem X flag hb hledger
      have hmem := CS.mem X b hb
      have hc : (CS.count X : ℝ) ≤ (z : ℝ) - 1 := by
        have ht : CS.count X + 1 ≤ z := hcount X
        have ht' : (CS.count X : ℝ) + 1 ≤ z := by exact_mod_cast ht
        linarith
      by_cases hend : ℓ ≤ b
      · have he : extra flag b ≤ max 0 (S.ρ - S.K) := by
          cases flag
          · exact le_max_left _ _
          · exact (sub_le_sub_right (B.bound _) _).trans (le_max_right _ _)
        have hR := B.bound (b + 1)
        have hCc := mul_le_mul_of_nonneg_right hc S.C_pos.le
        have hlb : (ℓ : ℝ) ≤ b := by exact_mod_cast hend
        have hgb := mul_le_mul_of_nonneg_left hlb S.g_pos.le
        have hiden := S.accounting_identity
        nlinarith [hmem.2]
      · have hbell : b < ℓ := by omega
        by_cases hp : S.p ≤ CS.f X b
        · by_cases hexp : B.Expandable b
          · obtain ⟨Y, hyb, hyc, hyf⟩ := CS.next X b hb hbell hp hexp
            have he : extra flag b ≤ extra flag (b + 1) := by
              cases flag
              · exact le_rfl
              · exact sub_le_sub_right (B.mono (by omega)) _
            have hnew : ((b + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f Y (b + 1)) ≤
                max 0 (S.U - S.w) + (CS.count Y : ℝ) * S.C +
                  B.B (b + 1 + 1) + extra flag (b + 1) := by
              rw [hyc]
              dsimp [Budget.r] at hyf
              push_cast
              have heq : S.C = S.g + S.U - S.h := by
                dsimp [Parameters.C, Parameters.U]; ring
              nlinarith [hmem.2]
            exact ih (ℓ - (b + 1)) (by omega) (b + 1) rfl Y flag hyb.le hnew
          · have hex : ∃ k : ℕ, 1 ≤ k ∧
                ((k : ℝ) + 1) * S.g + S.K < B.B (b + k + 1) - B.B (b + 1) := by
              simpa only [Budget.Expandable, not_forall, not_le, exists_prop] using hexp
            obtain ⟨k, hk, hblock⟩ := hex
            have hdrop := CS.fertile_drop X hb hp k
            have hRmono := B.mono (show b + k + 1 ≤ b + k + 2 by omega)
            have hB0 := B.nonneg (b + 1)
            have hK0 := S.K_nonneg
            have hnew : ((b + k + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f X (b + k + 1)) ≤
                max 0 (S.U - S.w) + (CS.count X : ℝ) * S.C +
                  B.B (b + k + 1 + 1) + extra true (b + k + 1) := by
              cases flag <;> dsimp [extra] at hledger ⊢ <;> push_cast <;>
                have hidx : b + k + 1 + 1 = b + k + 2 := by omega
              all_goals rw [hidx]; nlinarith [hmem.2]
            exact ih (ℓ - (b + k + 1)) (by omega) (b + k + 1) rfl X true (by omega) hnew
        · have hs := CS.step X b hb
          have hg := F.grow _ hmem
          rw [min_eq_right (by dsimp [Parameters.U]; linarith)] at hg
          have he : extra flag b ≤ extra flag (b + 1) := by
            cases flag
            · exact le_rfl
            · exact sub_le_sub_right (B.mono (by omega)) _
          have hnew : ((b + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f X (b + 1)) ≤
              max 0 (S.U - S.w) + (CS.count X : ℝ) * S.C +
                B.B (b + 1 + 1) + extra flag (b + 1) := by
            dsimp [Budget.r] at hs
            push_cast
            nlinarith
          exact ih (ℓ - (b + 1)) (by omega) (b + 1) rfl X flag (by omega) hnew
  apply hwalk ℓ 0 (by omega) CS.initial false CS.initial_start.le
  simpa only [Nat.cast_zero, zero_mul, zero_add, CS.initial_count, extra, Bool.false_eq_true,
    if_false, add_zero] using CS.initial_bound

end System

end ProofOfSpace.UniformGain

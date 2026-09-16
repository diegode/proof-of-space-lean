/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Delay
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring

/-! # Scalar floors and budget accounting for reference-trajectory latency

A protected level permits the initial surplus `K = beta_delta(sigma)-a-2g`.
Standard expandable levels are protected. This surplus is the deep-crush
premium, and the global ledger charges every budget interval explicitly.
-/

namespace ProofOfSpace.Reference

open Finset Set
universe u

structure Parameters where
  a : ℝ
  p : ℝ
  σ : ℝ
  g : ℝ
  h : ℝ
  w : ℝ
  ρ : ℝ
  g_pos : 0 < g
  rho_nonneg : 0 ≤ ρ
  a_pos : 0 < a
  entry : a ≤ min w (p + g) - ρ
  a_le_source : a ≤ σ
  source_le_p : σ ≤ p
  h_le : h ≤ p + g
  source_guard : a + 2 * g ≤ h

namespace Parameters

variable (S : Parameters)

def U : ℝ := S.p + S.g
def K : ℝ := S.h - S.a - 2 * S.g

theorem K_nonneg : 0 ≤ S.K := by
  have := S.source_guard
  dsimp [K]; linarith

theorem a_le_p : S.a ≤ S.p := S.a_le_source.trans S.source_le_p
theorem a_le_U : S.a ≤ S.U := by
  have := S.a_le_p; have := S.g_pos; dsimp [U]; linarith
theorem U_pos : 0 < S.U := S.a_pos.trans_le S.a_le_U
theorem a_le_U_sub_rho : S.a ≤ S.U - S.ρ :=
  S.entry.trans (sub_le_sub_right (min_le_right _ _) _)

theorem a_le_w_sub_rho : S.a ≤ S.w - S.ρ :=
  S.entry.trans (sub_le_sub_right (min_le_left _ _) _)

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

def Protected (t : ℕ) : Prop :=
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
    have hw := S.a_le_w_sub_rho
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
    have hentry : S.a ≤ min S.U S.w - S.ρ := by
      simpa only [min_comm, Parameters.U] using S.entry
    linarith

/-- A source at a protected depth stays above the band floor. -/
theorem source_orbit (t : ℕ) (hexp : B.Protected t) (k : ℕ) :
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

/-- The advisor's expandable-level definition, without a surplus allowance. -/
def Budget.Expandable {S : Parameters} (B : Budget S) (t : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → B.B (t + k + 1) - B.B (t + 1) ≤ ((k : ℝ) + 1) * S.g

theorem Budget.Expandable.protected {S : Parameters} {B : Budget S} {t : ℕ}
    (h : B.Expandable t) : B.Protected t := by
  intro k hk
  have := h k hk
  have := S.K_nonneg
  linarith

/-- Above a maximal high-spending stride the expenditure is strictly below
one base rate per level, exactly as in the manuscript. -/
theorem Budget.above_stride {S : Parameters} (B : Budget S) {b k : ℕ}
    (hstride : ((k : ℝ) + 1) * S.g < B.B (b + k + 1) - B.B (b + 1))
    (hmax : ∀ j, k < j → B.B (b + j + 1) - B.B (b + 1) ≤ ((j : ℝ) + 1) * S.g)
    {j : ℕ} (hj : 1 ≤ j) :
    B.B (b + k + j + 1) - B.B (b + k + 1) < (j : ℝ) * S.g := by
  have h := hmax (k + j) (by omega)
  rw [show b + (k + j) + 1 = b + k + j + 1 by omega] at h
  push_cast at h
  nlinarith

/-- Both levels identified by the maximal-stride lemma are expandable. -/
theorem Budget.stride_top_expandable {S : Parameters} (B : Budget S) {b k : ℕ}
    (hstride : ((k : ℝ) + 1) * S.g < B.B (b + k + 1) - B.B (b + 1))
    (hmax : ∀ j, k < j → B.B (b + j + 1) - B.B (b + 1) ≤ ((j : ℝ) + 1) * S.g) :
    B.Expandable (b + k) ∧ B.Expandable (b + k + 1) := by
  constructor
  · intro j hj
    have h := B.above_stride hstride hmax hj
    nlinarith [S.g_pos]
  · intro j hj
    have h := B.above_stride hstride hmax (show 1 ≤ j + 1 by omega)
    have hm := B.mono (show b + k + 1 ≤ b + k + 1 + 1 by omega)
    rw [show b + k + (j + 1) + 1 = b + k + 1 + j + 1 by omega] at h
    push_cast at h
    linarith

/-- Standard expandability preserves the starting weight until fertility.
The general protected-level invariant only promises the band floor. -/
theorem Growth.expandable_source_floor {S : Parameters} (F : Growth S) (B : Budget S)
    (b j : ℕ) (hexp : B.Expandable b) (hsource : S.σ + 2 * S.g ≤ F.F S.σ)
    (hbelow : ∀ k < j, F.orbit B b S.σ k ≤ S.p) :
    ∀ k ≤ j, S.σ ≤ F.orbit B b S.σ k := by
  have hmem (k : ℕ) := (F.source_orbit B b hexp.protected k).1
  have hledger : ∀ k ≤ j, 0 < k →
      S.σ + ((k : ℝ) + 1) * S.g - (B.B (b + k + 1) - B.B (b + 1)) ≤
        F.orbit B b S.σ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      intro _
      cases k with
      | zero =>
        have hs := F.orbit_step B b S.σ 0
        simp only [Growth.orbit, Nat.add_zero, Nat.zero_add, Nat.cast_one, Budget.r] at hs ⊢
        linarith
      | succ k =>
        have hp := hbelow (k + 1) (by omega)
        have hg := F.grow _ (hmem (k + 1))
        rw [min_eq_right (by dsimp [Parameters.U]; linarith)] at hg
        have hs := F.orbit_step B b S.σ (k + 1)
        have hi := ih (by omega) (by omega)
        dsimp [Budget.r] at hs
        simp only [Nat.add_assoc] at hs hi ⊢
        push_cast at hi ⊢
        nlinarith
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact le_rfl
  · have h := hledger k hk hpos
    have he := hexp k hpos
    linarith

/-- A clock turns nonlinear free expansion into uniform progress. -/
structure Clock {S : Parameters} (F : Growth S) where
  score : ℝ → ℝ
  mem : ∀ x ∈ Icc S.a S.U, score x ∈ Icc S.a S.U
  top : ∀ x ∈ Icc S.p S.U, score x = x
  below : ∀ x ∈ Icc S.a S.p, score x ≤ S.p
  step : ∀ x ∈ Icc S.a S.U, min S.U (score x + S.g) ≤ score (F.F x)
  subtract : ∀ x ∈ Icc S.a S.U, ∀ y ∈ Icc S.a S.U, ∀ r, 0 ≤ r →
    x - r ≤ y → score x - r ≤ score y

structure System {S : Parameters} (B : Budget S) (ℓ : ℕ) (Result : ℕ → Prop) where
  Context : Type u
  start : Context → ℕ
  count : Context → ℕ
  f : Context → ℕ → ℝ
  fertile : Context → ℕ → Prop
  mem : ∀ X d, start X ≤ d → f X d ≤ S.U
  fertile_ge : ∀ X d, start X ≤ d → fertile X d → S.p ≤ f X d
  infertile_le : ∀ X d, start X ≤ d → ¬ fertile X d → f X d ≤ S.p
  step : ∀ X d, start X ≤ d → min S.U (f X d + S.g) - B.r (d + 1) ≤ f X (d + 1)
  result : ∀ X, 0 < count X → Result (count X)
  sourceScore : ℝ
  sourceScore_le : sourceScore ≤ S.U
  initialCost : ℝ
  next : ∀ X b, start X ≤ b → b < ℓ → fertile X b → B.Protected b →
    ∃ Y, start Y = b + 1 ∧ count Y = count X + 1 ∧
      sourceScore - B.r (b + 1) ≤ f Y (b + 1)
  initial : Context
  initial_start : start initial = 0
  initial_count : count initial = 0
  initial_bound : S.U - f initial 0 ≤ initialCost + B.B 1

namespace System
variable {S : Parameters} {B : Budget S} {ℓ : ℕ} {Result : ℕ → Prop}
    (CS : System B ℓ Result)

def C : ℝ := S.g + S.U - CS.sourceScore

lemma C_pos : 0 < CS.C := by
  have := S.g_pos
  have := CS.sourceScore_le
  dsimp [C]
  linarith

theorem fertile_drop (X : CS.Context) {b : ℕ} (hb : CS.start X ≤ b)
    (hp : CS.fertile X b) (k : ℕ) :
    S.U - (B.B (b + k + 2) - B.B (b + 1)) ≤ CS.f X (b + k + 1) := by
  induction k with
  | zero =>
    have hs := CS.step X b hb
    have hp' := CS.fertile_ge X b hb hp
    rw [min_eq_left (by dsimp [Parameters.U]; linarith)] at hs
    simpa only [Budget.r, Nat.add_zero, Nat.add_assoc] using hs
  | succ k ih =>
    have hs := CS.step X (b + k + 1) (by omega)
    have hmem := CS.mem X (b + k + 1) (by omega)
    have hgrow : CS.f X (b + k + 1) ≤ min S.U (CS.f X (b + k + 1) + S.g) :=
      le_min hmem (by linarith [S.g_pos])
    dsimp [Budget.r] at hs
    convert (by linarith : S.U - (B.B (b + k + 1 + 1 + 1) - B.B (b + 1)) ≤
      CS.f X (b + k + 1 + 1)) using 1 <;> congr 1

include CS in
/-- The end-to-end scalar counting theorem, with one global black budget. -/
theorem count_links {z : ℕ} (hz : 1 ≤ z)
    (hmono : ∀ i j, i ≤ j → Result j → Result i)
    (hlevels : CS.initialCost + S.ρ + max 0 (S.ρ - S.K) +
      ((z : ℝ) - 1) * CS.C < S.g * ℓ) : Result z := by
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
        CS.initialCost + (CS.count X : ℝ) * CS.C + B.B (b + 1) + extra flag b →
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
        have hCc := mul_le_mul_of_nonneg_right hc CS.C_pos.le
        have hlb : (ℓ : ℝ) ≤ b := by exact_mod_cast hend
        have hgb := mul_le_mul_of_nonneg_left hlb S.g_pos.le
        nlinarith [hmem]
      · have hbell : b < ℓ := by omega
        by_cases hp : CS.fertile X b
        · by_cases hexp : B.Protected b
          · obtain ⟨Y, hyb, hyc, hyf⟩ := CS.next X b hb hbell hp hexp
            have he : extra flag b ≤ extra flag (b + 1) := by
              cases flag
              · exact le_rfl
              · exact sub_le_sub_right (B.mono (by omega)) _
            have hnew : ((b + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f Y (b + 1)) ≤
                CS.initialCost + (CS.count Y : ℝ) * CS.C +
                  B.B (b + 1 + 1) + extra flag (b + 1) := by
              rw [hyc]
              dsimp [Budget.r] at hyf
              push_cast
              have heq : CS.C = S.g + S.U - CS.sourceScore := rfl
              nlinarith [hmem]
            exact ih (ℓ - (b + 1)) (by omega) (b + 1) rfl Y flag hyb.le hnew
          · have hex : ∃ k : ℕ, 1 ≤ k ∧
                ((k : ℝ) + 1) * S.g + S.K < B.B (b + k + 1) - B.B (b + 1) := by
              simpa only [Budget.Protected, not_forall, not_le, exists_prop] using hexp
            obtain ⟨k, hk, hblock⟩ := hex
            have hdrop := CS.fertile_drop X hb hp k
            have hRmono := B.mono (show b + k + 1 ≤ b + k + 2 by omega)
            have hB0 := B.nonneg (b + 1)
            have hK0 := S.K_nonneg
            have hnew : ((b + k + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f X (b + k + 1)) ≤
                CS.initialCost + (CS.count X : ℝ) * CS.C +
                  B.B (b + k + 1 + 1) + extra true (b + k + 1) := by
              cases flag <;> dsimp [extra] at hledger ⊢ <;> push_cast <;>
                have hidx : b + k + 1 + 1 = b + k + 2 := by omega
              all_goals rw [hidx]; nlinarith [hmem]
            exact ih (ℓ - (b + k + 1)) (by omega) (b + k + 1) rfl X true (by omega) hnew
        · have hs := CS.step X b hb
          have hinf := CS.infertile_le X b hb hp
          rw [min_eq_right (by dsimp [Parameters.U]; linarith)] at hs
          have he : extra flag b ≤ extra flag (b + 1) := by
            cases flag
            · exact le_rfl
            · exact sub_le_sub_right (B.mono (by omega)) _
          have hnew : ((b + 1 : ℕ) : ℝ) * S.g + (S.U - CS.f X (b + 1)) ≤
              CS.initialCost + (CS.count X : ℝ) * CS.C +
                B.B (b + 1 + 1) + extra flag (b + 1) := by
            dsimp [Budget.r] at hs
            push_cast
            nlinarith
          exact ih (ℓ - (b + 1)) (by omega) (b + 1) rfl X flag (by omega) hnew
  apply hwalk ℓ 0 (by omega) CS.initial false CS.initial_start.le
  simpa only [Nat.cast_zero, zero_mul, zero_add, CS.initial_count, extra, Bool.false_eq_true,
    if_false, add_zero] using CS.initial_bound

end System
end ProofOfSpace.Reference

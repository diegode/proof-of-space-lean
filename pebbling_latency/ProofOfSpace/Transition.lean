/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Reference

/-! # Accounting lemmas for the revised manuscript transition

These lemmas make the September 16 transition's first-fertile certificate,
deep-crush premium, and floor-based remaining delay explicit. They use the
existing capped lower recurrence and do not assert the draft's full transition
or terminal theorem. The end-to-end latency theorem retains its global repair
allowance and its finite-depth proof.
-/

namespace ProofOfSpace.Delay.Trajectory

open Set
variable {F : ℝ → ℝ} {p g : ℝ} (T : ProofOfSpace.Delay.Trajectory F p g)

/-- The revised draft's `τ_x`: remaining time on the single floor-based scale.
This is distinct from the integer fertility time of a trajectory seeded at `x`.
Only arguments in `[T.y 0,p]` are used. -/
noncomputable def remainingDelay (x : ℝ) : ℝ :=
  ProofOfSpace.Delay.scale T.y T.t p - ProofOfSpace.Delay.scale T.y T.t x

theorem remainingDelay_nonneg {x : ℝ} (hx : x ∈ Icc (T.y 0) p) :
    0 ≤ T.remainingDelay x :=
  (ProofOfSpace.Delay.scale_calculus T.positive T.spaced hx.1 hx.2 T.reaches).1

theorem remainingDelay_antitone : AntitoneOn T.remainingDelay (Icc (T.y 0) p) := by
  intro x hx y hy hxy
  have h := (ProofOfSpace.Delay.scale_calculus T.positive T.spaced
    hx.1 hxy (hy.2.trans T.reaches)).1
  dsimp [remainingDelay]
  linarith

/-- The missing `eq:tau-linear` in the revised draft. -/
theorem remainingDelay_le {x : ℝ} (hx : x ∈ Icc (T.y 0) p) :
    T.remainingDelay x ≤ (p - x) / g :=
  (ProofOfSpace.Delay.scale_calculus T.positive T.spaced hx.1 hx.2 T.reaches).2

/-- A crush spending `W` prepays the regrowth allowance at the base rate. -/
theorem regrowth_allowance {W : ℝ} (hfloor : T.y 0 ≤ p + g - W) (hW : g ≤ W) :
    T.remainingDelay (p + g - W) + 1 ≤ W / g := by
  have h := T.remainingDelay_le ⟨hfloor, by linarith⟩
  have hg := T.positive
  have hmul := (le_div_iff₀ hg).mp h
  apply (le_div_iff₀ hg).mpr
  nlinarith

/-- The new certificate increment is bounded, but need not be nonpositive. -/
theorem crush_certificate_le {W κ : ℝ}
    (hfloor : T.y 0 ≤ p + g - W) (hW : g ≤ W) :
    T.remainingDelay (p + g - W) + 2 - κ / g ≤ (W - κ) / g + 1 := by
  have h := T.regrowth_allowance hfloor hW
  rw [sub_div]
  linarith

end ProofOfSpace.Delay.Trajectory

namespace ProofOfSpace.Reference.Growth

open Set
variable {S : Parameters} (F : Growth S) (B : Budget S)

/-- Spending through an infertile challenge prefix, retaining the original
challenge surplus even when the recurrence is capped above fertility. -/
theorem challenge_infertile_spending (k : ℕ)
    (hbelow : ∀ i ≤ k, F.orbit B 0 (min S.U (S.w - B.B 1)) i < S.p) :
    S.w + (k : ℝ) * S.g - S.p < B.B (k + 1) := by
  let x := min S.U (S.w - B.B 1)
  have hledger : ∀ j ≤ k, S.w + (j : ℝ) * S.g ≤
      F.orbit B 0 x j + B.B (j + 1) := by
    intro j hj
    induction j with
    | zero =>
      have hzero := hbelow 0 (Nat.zero_le k)
      have hcap : S.w - B.B 1 ≤ S.U := by
        by_contra h
        rw [orbit, min_eq_left (le_of_not_ge h)] at hzero
        have := S.g_pos
        dsimp [Parameters.U] at hzero
        linarith
      simp [orbit, x, min_eq_right hcap]
    | succ j ih =>
      have hi := ih (by omega)
      have hmem := (F.challenge_orbit B j).1
      have hg := F.grow _ hmem
      have hp := hbelow j (by omega)
      rw [min_eq_right (show F.orbit B 0 x j + S.g ≤ S.U by
        dsimp [Parameters.U]; linarith)] at hg
      have hs := F.orbit_step B 0 x j
      dsimp [Budget.r] at hs
      simp only [Nat.zero_add] at hs
      push_cast
      linarith
  have h := hledger k le_rfl
  have hp := hbelow k le_rfl
  change F.orbit B 0 x k < S.p at hp
  linarith

/-- The revised first-fertile certificate, conditional only on the preceding
levels being infertile. Spending at the fertile endpoint is nonnegative. -/
theorem first_fertile_certificate {b : ℕ} (hb : 1 ≤ b)
    (hbelow : ∀ i < b, F.orbit B 0 (min S.U (S.w - B.B 1)) i < S.p) :
    ((b : ℝ) - 1) * S.g + (S.w - S.p) ≤ B.B (b + 1) := by
  have h := F.challenge_infertile_spending B (b - 1) (by
    intro i hi; exact hbelow i (by omega))
  rw [Nat.sub_add_cancel hb, Nat.cast_sub hb] at h
  have hm := B.mono (show b ≤ b + 1 by omega)
  push_cast at h
  linarith

/-- A first fertile level exists inside the finite stack under the manuscript's
linear layer bound. There is no assumption of additional physical levels. -/
theorem exists_first_fertile {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hlevels : S.ρ ≤ S.w + ((ℓ : ℝ) - 1) * S.g - S.p) :
    ∃ b < ℓ, S.p ≤ F.orbit B 0 (min S.U (S.w - B.B 1)) b ∧
      ∀ i < b, F.orbit B 0 (min S.U (S.w - B.B 1)) i < S.p := by
  have hex : ∃ b, b < ℓ ∧ S.p ≤ F.orbit B 0 (min S.U (S.w - B.B 1)) b := by
    by_contra h
    push Not at h
    have hs := F.challenge_infertile_spending B (ℓ - 1) (by
      intro i hi; exact h i (by omega))
    rw [Nat.sub_add_cancel hℓ, Nat.cast_sub hℓ] at hs
    push_cast at hs
    linarith [B.bound ℓ]
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi
  have hn := Nat.find_min hex hi
  have hil : i < ℓ := hi.trans (Nat.find_spec hex).1
  exact lt_of_not_ge (fun hp => hn ⟨hil, hp⟩)

/-- Before the first band exit, every step after the source expansion gains at
least `g`. The endpoint may be zero: no untruncated equality is used. -/
theorem source_prefix_spending (b k : ℕ)
    (hband : ∀ i, 1 ≤ i → i ≤ k → F.orbit B b S.σ i ∈ Icc S.a S.p) :
    S.h + (k : ℝ) * S.g ≤ F.orbit B b S.σ (k + 1) +
      (B.B (b + (k + 1) + 1) - B.B (b + 1)) := by
  induction k with
  | zero =>
    have hs := F.orbit_step B b S.σ 0
    change F.F S.σ - (B.B (b + 1 + 1) - B.B (b + 1)) ≤
      F.orbit B b S.σ 1 at hs
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.zero_add]
    linarith [F.source]
  | succ k ih =>
    have hi := ih (fun i hi hk => hband i hi (by omega))
    have hm := hband (k + 1) (by omega) le_rfl
    have hg := F.grow _ ⟨hm.1, hm.2.trans (by
      dsimp [Parameters.U]; linarith [S.g_pos])⟩
    rw [min_eq_right (show F.orbit B b S.σ (k + 1) + S.g ≤ S.U by
      dsimp [Parameters.U]; linarith [hm.2])] at hg
    have hs := F.orbit_step B b S.σ (k + 1)
    dsimp [Budget.r] at hs
    simp only [Nat.add_assoc] at hs hi ⊢
    push_cast
    linarith

/-- Case (III)'s strict premium `W > κ + (m-1)g`, including complete erasure.
Here `m = k+1` and `κ = h-a`; normalized profiles take `h = β(σ)-δ`. -/
theorem deep_crush_premium (b k : ℕ)
    (hband : ∀ i, 1 ≤ i → i ≤ k → F.orbit B b S.σ i ∈ Icc S.a S.p)
    (hcrush : F.orbit B b S.σ (k + 1) < S.a) :
    S.h - S.a + (k : ℝ) * S.g < B.B (b + (k + 1) + 1) - B.B (b + 1) := by
  have h := F.source_prefix_spending B b k hband
  linarith

end ProofOfSpace.Reference.Growth

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Reference

/-! # Accounting lemmas for the revised manuscript transition

These lemmas make the September 16–18 transition's first-fertile certificate,
deep-crush premium, and floor-based remaining delay explicit. The revised
paper's `κ` is `Parameters.K = h-a-2g`, whereas the original public latency
statement uses `κ = h-a`. They use the
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

/-- The linear bound for the paper's floor-clock distance (Definition `def:tau`). -/
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

/-- September 17 notation: the surplus `K = κ_old-2g` absorbs the two levels
in the previous certificate. This is an algebraic change, not a stronger bound. -/
theorem crush_certificate_reparametrize (W κ : ℝ) :
    T.remainingDelay (p + g - W) + 2 - κ / g =
      T.remainingDelay (p + g - W) - (κ - 2 * g) / g := by
  have hg : g ≠ 0 := ne_of_gt T.positive
  field_simp [hg]
  ring

/-- The revised certificate increment in the paper's surplus notation. -/
theorem crush_surplus_le {W K : ℝ}
    (hfloor : T.y 0 ≤ p + g - W) (hW : g ≤ W) :
    T.remainingDelay (p + g - W) - K / g ≤ (W - K) / g - 1 := by
  have h := T.regrowth_allowance hfloor hW
  rw [sub_div]
  linarith

/-- September 18: eliminate the actual spending `W` using the kill length `m`.
The Lipschitz estimate has the direction needed for an upper certificate bound. -/
theorem crush_length_certificate {W K : ℝ} {m : ℕ}
    (hK : 0 ≤ K) (_hm : 1 ≤ m)
    (hfloor : T.y 0 ≤ p + g - W)
    (hW : K + ((m : ℝ) + 1) * g ≤ W) :
    T.remainingDelay (p + g - W) + ((m : ℝ) + 1) - W / g ≤
      T.remainingDelay (p - K - (m : ℝ) * g) - K / g := by
  have hg := T.positive
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have horder : p + g - W ≤ p - K - (m : ℝ) * g := by linarith
  have htop : p - K - (m : ℝ) * g ≤ p := by nlinarith
  have h := (ProofOfSpace.Delay.scale_calculus T.positive T.spaced
    hfloor horder (htop.trans T.reaches)).2
  have h := (le_div_iff₀ hg).mp h
  have hWdiv : W / g * g = W := div_mul_cancel₀ _ (ne_of_gt hg)
  have hKdiv : K / g * g = K := div_mul_cancel₀ _ (ne_of_gt hg)
  dsimp [remainingDelay]
  nlinarith

end ProofOfSpace.Delay.Trajectory

namespace ProofOfSpace.Reference.Budget

variable {S : Parameters} (B : Budget S)

/-- A local crush must carry its spending window, in addition to the scalar
remaining-budget bound in the revised Transition statement. -/
theorem window_le_remaining {b e : ℕ} {c W : ℝ}
    (hcert : ((b : ℝ) - c) * S.g ≤ B.B (b + 1))
    (hwindow : W ≤ B.B (e + 1) - B.B (b + 1)) :
    W ≤ S.ρ - ((b : ℝ) - c) * S.g := by
  linarith [B.bound (e + 1)]

/-- The disjoint consecutive windows required by Terminal iteration.
An individual bound on each `W r` would not justify the sum bound. -/
theorem terminal_budget {q : ℕ} (b : ℕ → ℕ) (W : ℕ → ℝ) (c : ℝ)
    (hcert : ((b 0 : ℝ) - c) * S.g ≤ B.B (b 0 + 1))
    (hwindow : ∀ r < q, W r ≤ B.B (b (r + 1) + 1) - B.B (b r + 1)) :
    ∑ r ∈ Finset.range q, W r ≤ S.ρ - ((b 0 : ℝ) - c) * S.g := by
  have htel : ∀ k ≤ q, ∑ r ∈ Finset.range k, W r ≤
      B.B (b k + 1) - B.B (b 0 + 1) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have := ih (by omega)
      have := hwindow k (by omega)
      linarith
  have := htel q le_rfl
  linarith [B.bound (b q + 1)]

/-- Rationing uses the revised strict crush threshold `K+2g`. -/
theorem terminal_crush_count {q : ℕ} (hq : 0 < q)
    (b : ℕ → ℕ) (W : ℕ → ℝ) (c : ℝ)
    (hcert : ((b 0 : ℝ) - c) * S.g ≤ B.B (b 0 + 1))
    (hwindow : ∀ r < q, W r ≤ B.B (b (r + 1) + 1) - B.B (b r + 1))
    (hpremium : ∀ r < q, S.K + 2 * S.g < W r) :
    (q : ℝ) * (S.K + 2 * S.g) < S.ρ - ((b 0 : ℝ) - c) * S.g := by
  have hsum : (∑ _r ∈ Finset.range q, (S.K + 2 * S.g)) <
      ∑ r ∈ Finset.range q, W r := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    intro r hr
    exact hpremium r (Finset.mem_range.mp hr)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum.trans_le (B.terminal_budget b W c hcert hwindow)

/-- The revised local certificate follows by adding the old certificate,
crush spending and regrowth spending. No seed-fertility lower bound on the
parent's regrowth time is assumed. -/
theorem crush_certificate {b m i : ℕ} {c W R d : ℝ}
    (hcert : ((b : ℝ) - c) * S.g ≤ B.B (b + 1))
    (hcrush : S.K + ((m : ℝ) + 1) * S.g ≤ W)
    (hregrow : ((i : ℝ) - 1 - d) * S.g ≤ R)
    (hwindow : B.B (b + 1) + W + R ≤ B.B (b + m + i + 1)) :
    (((b + m + i : ℕ) : ℝ) - (c + d - S.K / S.g)) * S.g ≤
      B.B (b + m + i + 1) := by
  have hdiv : S.K / S.g * S.g = S.K := div_mul_cancel₀ _ (ne_of_gt S.g_pos)
  push_cast
  nlinarith

/-- The manuscript's optimized certificate, with actual crush and regrowth
windows. In contrast to `crush_certificate`, its delay is evaluated at the
minimum permitted crush spending, not at the actual spending. -/
theorem crush_length_certificate {free : ℝ → ℝ}
    (T : ProofOfSpace.Delay.Trajectory free S.p S.g)
    {b m i : ℕ} {c W R : ℝ} (hm : 1 ≤ m)
    (hfloor : T.y 0 ≤ S.p + S.g - W)
    (hcert : ((b : ℝ) - c) * S.g ≤ B.B (b + 1))
    (hcrush : S.K + ((m : ℝ) + 1) * S.g ≤ W)
    (hregrow : ((i : ℝ) - 1 - T.remainingDelay (S.p + S.g - W)) * S.g ≤ R)
    (hwindow : B.B (b + 1) + W + R ≤ B.B (b + m + i + 1)) :
    (((b + m + i : ℕ) : ℝ) -
      (c + T.remainingDelay (S.p - S.K - (m : ℝ) * S.g) - S.K / S.g)) * S.g ≤
        B.B (b + m + i + 1) := by
  have h := T.crush_length_certificate S.K_nonneg hm hfloor hcrush
  have hWdiv : W / S.g * S.g = W := div_mul_cancel₀ _ (ne_of_gt S.g_pos)
  have hKdiv : S.K / S.g * S.g = S.K := div_mul_cancel₀ _ (ne_of_gt S.g_pos)
  push_cast
  nlinarith [S.g_pos]

/-- Sum the exact kill-length premiums over disjoint windows. Strictness
requires at least one crush; the empty plan is handled separately. -/
theorem terminal_kill_budget {q : ℕ} (hq : 0 < q)
    (b m : ℕ → ℕ) (W : ℕ → ℝ) (c : ℝ)
    (hcert : ((b 0 : ℝ) - c) * S.g ≤ B.B (b 0 + 1))
    (hwindow : ∀ r < q, W r ≤ B.B (b (r + 1) + 1) - B.B (b r + 1))
    (hpremium : ∀ r < q, S.K + ((m r : ℝ) + 1) * S.g < W r) :
    ∑ r ∈ Finset.range q, (S.K + ((m r : ℝ) + 1) * S.g) <
      S.ρ - ((b 0 : ℝ) - c) * S.g := by
  have hsum : (∑ r ∈ Finset.range q, (S.K + ((m r : ℝ) + 1) * S.g)) <
      ∑ r ∈ Finset.range q, W r := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    intro r hr
    exact hpremium r (Finset.mem_range.mp hr)
  exact hsum.trans_le (B.terminal_budget b W c hcert hwindow)

end ProofOfSpace.Reference.Budget

namespace ProofOfSpace.Reference.Growth

open Set
variable {S : Parameters} (F : Growth S) (B : Budget S)

/-- A normalized fertile parent survives any later spending. This proves the
parent-floor estimate directly, rather than applying a lemma about red-free
initial weight to an arbitrary set. -/
theorem fertile_orbit (b k : ℕ) :
    F.orbit B b S.p k ∈ Icc S.a S.U ∧
      (0 < k → S.U - (B.B (b + k + 1) - B.B (b + 1)) ≤
        F.orbit B b S.p k) := by
  induction k with
  | zero =>
    refine ⟨⟨S.a_le_p, ?_⟩, by omega⟩
    change S.p ≤ S.p + S.g
    linarith [S.g_pos]
  | succ k ih =>
    have hs := F.orbit_step B b S.p k
    have hlo : S.U - (B.B (b + (k + 1) + 1) - B.B (b + 1)) ≤
        F.orbit B b S.p (k + 1) := by
      cases k with
      | zero =>
        have hfree := F.fertile (x := S.p) ih.1 le_rfl
        simpa only [orbit, hfree, Budget.r, Nat.add_zero] using hs
      | succ k =>
        have hi := ih.2 (by omega)
        have hg := F.nondecreasing_step ih.1
        dsimp [Budget.r] at hs
        simp only [Nat.add_assoc] at hs hi ⊢
        linarith
    refine ⟨⟨?_, F.orbit_cap B ih.1⟩, fun _ => hlo⟩
    have hbudget := B.diff_le_rho (b + 1) (b + (k + 1) + 1)
    linarith [S.a_le_U_sub_rho]

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

/-- The same strict spending bound with September 17's `κ = K`.
The exit index is `m = k+1`, so the premium is `K+(m+1)g`. -/
theorem deep_crush_surplus (b k : ℕ)
    (hband : ∀ i, 1 ≤ i → i ≤ k → F.orbit B b S.σ i ∈ Icc S.a S.p)
    (hcrush : F.orbit B b S.σ (k + 1) < S.a) :
    S.K + ((k : ℝ) + 2) * S.g < B.B (b + (k + 1) + 1) - B.B (b + 1) := by
  have h := F.deep_crush_premium B b k hband hcrush
  dsimp [Parameters.K]
  nlinarith

end ProofOfSpace.Reference.Growth

/-! The September 17 proof constructs the first fertile *parent* after a
crush. It cannot assign that depth the free fertility lower bound of the
discarded *source*. This example checks the local recurrence and regime;
it is not a counterexample graph to every alternative in the Transition
theorem's existential disjunction. -/
namespace ProofOfSpace.Reference.DeepCrushExample

open Set
noncomputable section

def beta (x : ℝ) : ℝ := 2 * x - x ^ 2
def expand (x : ℝ) : ℝ := beta x - 1 / 1000
def floor : ℝ := 1 / 100
def target : ℝ := 99 / 100
def source : ℝ := 1 / 40
def budget : ℝ := 1 / 20
def gain : ℝ := expand target - target

def orbit (x : ℝ) : ℕ → ℝ
  | 0 => x
  | i + 1 => max 0 (expand (orbit x i) - if i = 0 then budget else 0)

theorem beta_monotone : MonotoneOn beta (Icc 0 1) := by
  intro x hx y hy hxy
  dsimp [beta]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
    (show 0 ≤ 2 - x - y by linarith [hx.2, hy.2])]

theorem beta_concave : ConcaveOn ℝ (Icc 0 1) beta := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x _ y _ u v hu hv huv
  simp only [smul_eq_mul, beta]
  have h := mul_nonneg (mul_nonneg hu hv) (sq_nonneg (x - y))
  nlinarith [sq_nonneg (u * x + v * y - x),
    show u = 1 - v by linarith]

/-- Conditions (a)--(c), taking `ζ-δ=target`, and the band endpoint gain. -/
theorem regime :
    0 < floor ∧ floor < source ∧ source < target ∧ 0 < gain ∧
    budget + floor ≤ target ∧ budget + floor < expand target ∧
    expand floor - floor = gain ∧ 2 * gain ≤ expand source - source := by
  norm_num [floor, source, target, budget, gain, expand, beta]

/-- All spending is on the first level. The maximal high-spending stride is
four levels, since five base rates cost less than the budget and six do not. -/
theorem stride : 5 * gain < budget ∧ budget ≤ 6 * gain := by
  norm_num [gain, budget, expand, beta, target]

theorem source_erased (i : ℕ) : orbit source (i + 1) = 0 := by
  induction i with
  | zero => norm_num [orbit, source, budget, expand, beta]
  | succ i ih =>
    rw [orbit, ih]
    norm_num [expand, beta]

/-- The construction is in case (III), yet its first fertile parent is only
two levels above the input, before even the source's first two free steps
reach fertility. Thus the constructed depth does not satisfy `b' ≥ b+t_σ`. -/
theorem early_parent_regrowth :
    orbit source 5 < source ∧ orbit source 1 < floor ∧
    orbit target 1 < target ∧ target ≤ orbit target 2 ∧
    source < target ∧ expand source < target ∧ expand (expand source) < target := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, source_erased,
    show (1 : ℕ) = 0 + 1 from rfl, source_erased]
  norm_num [orbit, source, target, floor, budget, expand, beta]

end
end ProofOfSpace.Reference.DeepCrushExample

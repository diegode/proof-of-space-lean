/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Sources
import ProofOfSpace.UniformGain

/-! # Latency amplification from interval expansion and depth robustness -/
namespace ProofOfSpace
open Finset Set
universe u

namespace UniformGain

noncomputable def ofProfile (E : Parameters) (β : ℝ → ℝ) (δ : ℝ)
    (hgain : ∀ x ∈ Icc E.a E.p, x + E.g ≤ β x - δ)
    (hsource : E.h ≤ β E.σ - δ) : Growth E where
  F x := min E.U (β (min x E.p) - δ)
  cap x _ := min_le_left _ _
  grow x hx := by
    apply le_min (min_le_left _ _)
    by_cases hp : x ≤ E.p
    · rw [min_eq_left hp]
      exact (min_le_right _ _).trans (hgain x ⟨hx.1, hp⟩)
    · rw [min_eq_right (le_of_not_ge hp)]
      have h := hgain E.p ⟨E.a_le_p, le_rfl⟩
      exact (min_le_left _ _).trans h
  source := by
    rw [min_eq_left E.source_le_p]
    exact le_min E.h_le hsource

end UniformGain

namespace Concrete.Pebbling

open UniformGain
variable {V : Type u} {ℓ n : ℕ} {G : LayeredGraph V ℓ n}
    {δ : ℝ} {E : Parameters} (P : Pebbling G δ E.ρ)

noncomputable def uniformBudget : UniformGain.Budget E where
  B t := ∑ i ∈ Finset.range t, P.spend i
  zero := by simp
  mono := by
    intro t v htv
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono htv)
    intro i _ _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  bound := P.black_total

@[simp] theorem uniformBudget_r (d : ℕ) : P.uniformBudget.r d = P.spend d := by
  simp [uniformBudget, UniformGain.Budget.r, Finset.sum_range_succ]

@[simp] theorem uniformBudget_one : P.uniformBudget.B 1 = P.spend 0 := by
  simp [uniformBudget]

theorem orbit_le_footprint (hn : 0 < n) {β : ℝ → ℝ}
    (hgain : ∀ x ∈ Icc E.a E.p, x + E.g ≤ β x - δ)
    (hsource : E.h ≤ β E.σ - δ) (hexp : G.Expands β E.a E.p)
    {S : Finset V} {t : ℕ} {x : ℝ}
    (hinit : x ≤ weight n (P.layerFootprint S t))
    (hfloor : ∀ k, (ofProfile E β δ hgain hsource).orbit P.uniformBudget t x k ∈
      Icc E.a E.U) (k : ℕ) (hk : t + k < ℓ) :
    (ofProfile E β δ hgain hsource).orbit P.uniformBudget t x k ≤
      weight n (P.layerFootprint S (t + k)) := by
  induction k with
  | zero => simpa [Growth.orbit] using hinit
  | succ k ih =>
    have hi := ih (by omega)
    let f := (ofProfile E β δ hgain hsource).orbit P.uniformBudget t x k
    have hmem := hfloor k
    have hquery : min f E.p ∈ Icc E.a E.p :=
      ⟨le_min hmem.1 E.a_le_p, min_le_right _ _⟩
    have hs := P.layerFootprint_step hn hexp (d := t + k) (by omega) hquery
      ((min_le_left _ _).trans hi)
    have hfree : (ofProfile E β δ hgain hsource).F f ≤ β (min f E.p) - δ :=
      min_le_right _ _
    have hmax := max_le_max (le_refl (0 : ℝ))
      (sub_le_sub_right hfree (P.spend (t + k + 1)))
    simpa only [Growth.orbit, uniformBudget_r, Nat.add_assoc] using hmax.trans hs

/-- S completed path link and its continuation sources. -/
structure Link (S : Finset V) (d₀ q s : ℕ) where
  depth : ℕ
  inside : depth < ℓ
  count : ℕ
  count_pos : 0 < count
  source : Finset V
  source_layer : source ⊆ G.layer depth
  source_available : ∀ v ∈ source, P.unpebbled v
  source_card : source.card = s
  expandable : P.uniformBudget.Expandable depth
  tail : ∀ v ∈ source, P.PathTo S v ((count : ℝ) * q)
  realized : P.HasUnpebbledPathInFootprint S (d₀ + ((count : ℝ) - 1) * q)

namespace Link

variable {P} {S : Finset V} {d₀ q s : ℕ}

noncomputable def base {b : ℕ} (hb : b < ℓ) (hexp : P.uniformBudget.Expandable b)
    (SD : P.SourceData S b d₀ s q) : P.Link S d₀ q s where
  depth := b
  inside := hb
  count := 1
  count_pos := by omega
  source := SD.source
  source_layer := SD.source_sub.trans (P.layerFootprint_subset S b)
  source_available := fun v hv =>
    P.footprint_available S ((P.mem_layerFootprint S).mp (SD.source_sub hv)).2
  source_card := SD.source_card
  expandable := hexp
  tail := by
    intro v hv
    obtain ⟨Q, hfirst, hmem, hlen⟩ := SD.source_path v hv
    have h := P.splice_challenge hmem
    rw [hfirst] at h
    apply P.pathTo_mono S _ h
    simpa using (show (q : ℝ) ≤ Q.length by exact_mod_cast hlen)
  realized := by
    refine ⟨SD.long.first, P.pathTo_mono S ?_ (P.splice_challenge SD.long_mem)⟩
    simpa using (show (d₀ : ℝ) ≤ SD.long.length by exact_mod_cast SD.long_length)

noncomputable def extend (L : P.Link S d₀ q s) {b : ℕ}
    (hdepth : L.depth < b) (hb : b < ℓ) (hexp : P.uniformBudget.Expandable b)
    (SD : P.SourceData L.source b d₀ s q) : P.Link S d₀ q s where
  depth := b
  inside := hb
  count := L.count + 1
  count_pos := by omega
  source := SD.source
  source_layer := SD.source_sub.trans (P.layerFootprint_subset L.source b)
  source_available := fun v hv =>
    P.footprint_available L.source ((P.mem_layerFootprint L.source).mp (SD.source_sub hv)).2
  source_card := SD.source_card
  expandable := hexp
  tail := by
    intro v hv
    obtain ⟨Q, hfirst, hmem, hlen⟩ := SD.source_path v hv
    have h := P.splice_source (by omega : b ≠ L.depth) L.source_layer L.tail hmem
    rw [hfirst] at h
    apply P.pathTo_mono S _ h
    have : (q : ℝ) ≤ Q.length := by exact_mod_cast hlen
    push_cast; nlinarith
  realized := by
    refine ⟨SD.long.first, P.pathTo_mono S ?_
      (P.splice_source (by omega : b ≠ L.depth) L.source_layer L.tail SD.long_mem)⟩
    have : (d₀ : ℝ) ≤ SD.long.length := by exact_mod_cast SD.long_length
    push_cast; nlinarith

end Link

noncomputable def chainSystem (hn : 0 < n) {β : ℝ → ℝ}
    (hgain : ∀ x ∈ Icc E.a E.p, x + E.g ≤ β x - δ)
    (hsource : E.h ≤ β E.σ - δ) (hexp : G.Expands β E.a E.p)
    {t d₀ m s : ℕ} (hDR : G.DepthRobust t d₀) (hTm : t ≤ m)
    (hq : 1 ≤ min d₀ (d₀ + m + 1 - (t + s)))
    (hp : E.p = (m : ℝ) / n) (hσ : E.σ = (s : ℝ) / n)
    (S : Finset V) (hA : S ⊆ G.layer 0) (hred : ∀ v ∈ S, v ∉ P.red 0)
    (hweight : E.w ≤ weight n S) :
    UniformGain.System (ofProfile E β δ hgain hsource) P.uniformBudget ℓ
      (fun z => P.HasUnpebbledPathInFootprint S
        (d₀ + ((z : ℝ) - 1) * (min d₀ (d₀ + m + 1 - (t + s))))) := by
  classical
  let q := min d₀ (d₀ + m + 1 - (t + s))
  let F := ofProfile E β δ hgain hsource
  let x := min E.U (E.w - P.uniformBudget.B 1)
  let ctx := Option (P.Link S d₀ q s)
  let start : ctx → ℕ := fun X => match X with | none => 0 | some L => L.depth + 1
  let count : ctx → ℕ := fun X => match X with | none => 0 | some L => L.count
  let f : ctx → ℕ → ℝ := fun X d => match X with
    | none => F.orbit P.uniformBudget 0 x d
    | some L => F.orbit P.uniformBudget L.depth E.σ (d - L.depth)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hchallenge : ∀ k, F.orbit P.uniformBudget 0 x k ∈ Icc E.a E.U :=
    fun k => (F.challenge_orbit P.uniformBudget k).1
  have hinit : x ≤ weight n (P.layerFootprint S 0) := by
    apply le_trans _ (P.challenge_start_le hn hA hred hweight)
    exact (min_le_right _ _).trans (by simp only [uniformBudget_one]; exact le_max_right _ _)
  have hactual0 (b : ℕ) (hb : b < ℓ) : f none b ≤ weight n (P.layerFootprint S b) := by
    simpa only [Nat.zero_add] using
      P.orbit_le_footprint hn hgain hsource hexp hinit hchallenge b (by omega)
  have hactualL (L : P.Link S d₀ q s) (b : ℕ) (hlb : L.depth ≤ b) (hb : b < ℓ) :
      f (some L) b ≤ weight n (P.layerFootprint L.source b) := by
    have hstart : E.σ ≤ weight n (P.layerFootprint L.source L.depth) := by
      apply P.source_le_layerFootprint L.source_layer L.source_available
      simp only [hσ, weight, L.source_card, le_refl]
    have h := P.orbit_le_footprint hn hgain hsource hexp hstart
      (fun k => (F.source_orbit P.uniformBudget L.depth L.expandable k).1)
      (b - L.depth) (by omega)
    simpa only [Nat.add_sub_of_le hlb] using h
  refine {
    Context := ctx, start := start, count := count, f := f,
    mem := ?_, step := ?_, result := ?_, next := ?_,
    initial := none, initial_start := rfl, initial_count := rfl, initial_bound := ?_ }
  · intro X d hd
    cases X with
    | none => exact hchallenge d
    | some L => exact (F.source_orbit P.uniformBudget L.depth L.expandable _).1
  · intro X d hd
    cases X with
    | none => simpa [f, Nat.zero_add] using F.orbit_step P.uniformBudget 0 x d
    | some L =>
      have hld : L.depth ≤ d := by dsimp [start] at hd; omega
      have h := F.orbit_step P.uniformBudget L.depth E.σ (d - L.depth)
      simpa only [f, Nat.add_sub_of_le hld,
        show d + 1 - L.depth = d - L.depth + 1 by omega] using h
  · intro X hpos
    cases X with
    | none => exact False.elim (Nat.lt_irrefl 0 hpos)
    | some L => exact L.realized
  · intro X b hstart hb hfert hexpand
    have hmake {Y : Finset V} (hY : E.p ≤ weight n (P.layerFootprint Y b)) :
        Nonempty (P.SourceData Y b d₀ s q) := by
      apply P.sourceData (hDR b hb) hTm hq
      rw [hp, weight, div_le_div_iff_of_pos_right hnR] at hY
      exact_mod_cast hY
    cases X with
    | none =>
      let SD := (hmake (hfert.trans (hactual0 b hb))).some
      let L := Link.base hb hexpand SD
      refine ⟨some L, rfl, rfl, ?_⟩
      change E.h - P.uniformBudget.r (b + 1) ≤ F.orbit P.uniformBudget b E.σ (b + 1 - b)
      rw [show b + 1 - b = 1 by omega]
      exact (sub_le_sub_right F.source _).trans (le_max_right _ _)
    | some L =>
      have hLb : L.depth < b := by dsimp [start] at hstart; omega
      let SD := (hmake (hfert.trans (hactualL L b hLb.le hb))).some
      let L' := L.extend hLb hb hexpand SD
      refine ⟨some L', rfl, rfl, ?_⟩
      change E.h - P.uniformBudget.r (b + 1) ≤ F.orbit P.uniformBudget b E.σ (b + 1 - b)
      rw [show b + 1 - b = 1 by omega]
      exact (sub_le_sub_right F.source _).trans (le_max_right _ _)
  · change E.U - min E.U (E.w - P.uniformBudget.B 1) ≤ _
    have hB := P.uniformBudget.nonneg 1
    have h0 := le_max_left (0 : ℝ) (E.U - E.w)
    have h1 := le_max_right (0 : ℝ) (E.U - E.w)
    rcases le_total E.U (E.w - P.uniformBudget.B 1) with ht | ht
    · rw [min_eq_left ht]; linarith
    · rw [min_eq_right ht]; linarith

theorem latency (hn : 0 < n) {β : ℝ → ℝ}
    (hgain : ∀ x ∈ Icc E.a E.p, x + E.g ≤ β x - δ)
    (hsource : E.h ≤ β E.σ - δ) (hexp : G.Expands β E.a E.p)
    {t d₀ m s z : ℕ} (hDR : G.DepthRobust t d₀) (hTm : t ≤ m)
    (hq : 1 ≤ min d₀ (d₀ + m + 1 - (t + s)))
    (hp : E.p = (m : ℝ) / n) (hσ : E.σ = (s : ℝ) / n) (hz : 1 ≤ z)
    (hlevels : E.ρ + E.g + max (E.p - E.w) E.C + ((z : ℝ) - 1) * E.C < E.g * ℓ)
    (S : Finset V) (hA : S ⊆ G.layer 0) (hred : ∀ v ∈ S, v ∉ P.red 0)
    (hweight : E.w ≤ weight n S) :
    P.HasUnpebbledPathInFootprint S
      (d₀ + ((z : ℝ) - 1) * (min d₀ (d₀ + m + 1 - (t + s)))) := by
  let CS := P.chainSystem hn hgain hsource hexp hDR hTm hq hp hσ S hA hred hweight
  apply CS.count_links hz _ hlevels
  intro i j hij hj
  apply P.hasPath_mono S _ hj
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hq0 : (0 : ℝ) ≤ min d₀ (d₀ + m + 1 - (t + s)) := Nat.cast_nonneg _
  nlinarith

end Concrete.Pebbling
end ProofOfSpace

/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Model
import ProofOfSpace.PortModel

/-! # Layered graphs built from Chung port permutations -/

namespace ProofOfSpace.Concrete
open Finset Set

/-- A topologically ordered DAG on `Fin n`, to be used inside one layer. -/
structure StandaloneGraph (n : ℕ) where
  /-- The intra-layer edge relation. -/
  edge : Fin n → Fin n → Prop
  /-- Edges respect the node order, so the graph is acyclic. -/
  edge_lt : ∀ {u v}, edge u v → u.val < v.val

/-- The layered stack built from Chung port permutations. -/
noncomputable def portStack (H : StandaloneGraph n) (ℓ : ℕ)
    (P : ℕ → PortInterlayer n) : LayeredGraph (ℕ × Fin n) ℓ n where
  layer k := if k < ℓ then Finset.univ.image (fun i : Fin n => (k, i)) else ∅
  depth v := v.1
  rank v := (ℓ - v.1) * n + v.2.val
  intra k u v := u.1 = k ∧ v.1 = k ∧ k < ℓ ∧ H.edge u.2 v.2
  inter k u v := u.1 = k + 1 ∧ v.1 = k ∧ k + 1 < ℓ ∧
    ∃ q ∈ PortInterlayer.ports ({v.2} : Finset (Fin n)), ((P k).perm q).2 = u.2
  pred k T := if k + 1 < ℓ then
    ((P k).neighborhood ((T.filter fun v => v.1 = k).image Prod.snd)).image
      (fun i : Fin n => (k + 1, i)) else ∅
  layer_mem := by
    intro k v
    by_cases hk : k < ℓ
    · rw [if_pos hk]
      simp only [hk, and_true]
      constructor
      · intro hv
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
        rw [← hi]
      · intro hv
        exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
    · simp [hk]
  layer_card := by
    intro k hk
    rw [if_pos hk, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_univ, Fintype.card_fin]
  intra_mem := by
    rintro k u v ⟨hu, hv, hk, -⟩
    constructor <;> rw [if_pos hk]
    · exact Finset.mem_image.2 ⟨u.2, Finset.mem_univ _, by rw [← hu]⟩
    · exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
  inter_mem := by
    rintro k u v ⟨hu, hv, hk, -⟩
    constructor
    · rw [if_pos hk]
      exact Finset.mem_image.2 ⟨u.2, Finset.mem_univ _, by rw [← hu]⟩
    · rw [if_pos (show k < ℓ by omega)]
      exact Finset.mem_image.2 ⟨v.2, Finset.mem_univ _, by rw [← hv]⟩
  intra_rank := by
    rintro k u v ⟨hu, hv, -, hedge⟩
    rw [hu, hv]
    exact Nat.add_lt_add_left (H.edge_lt hedge) _
  inter_rank := by
    rintro k u v ⟨hu, hv, hk, -⟩
    have hsplit : (ℓ - (k + 1)) * n + n = (ℓ - k) * n := by
      have : ℓ - k = (ℓ - (k + 1)) + 1 := by omega
      rw [this]
      ring
    calc
      (ℓ - u.1) * n + u.2.val < (ℓ - (k + 1)) * n + n := by rw [hu]; omega
      _ = (ℓ - k) * n := hsplit
      _ ≤ (ℓ - v.1) * n + v.2.val := by rw [hv]; omega
  pred_subset := by
    intro k T
    by_cases hk : k + 1 < ℓ
    · rw [if_pos hk, if_pos hk]
      exact Finset.image_subset_image (Finset.subset_univ _)
    · rw [if_neg hk]
      exact Finset.empty_subset _
  pred_edge := by
    intro k T u hu
    by_cases hk : k + 1 < ℓ
    · rw [if_pos hk] at hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
      rw [PortInterlayer.neighborhood] at hi
      obtain ⟨q, hq, hqi⟩ := Finset.mem_image.1 hi
      rw [PortInterlayer.ports, Finset.mem_product] at hq
      obtain ⟨v, hvfilter, hvq⟩ := Finset.mem_image.1 hq.2
      rw [Finset.mem_filter] at hvfilter
      refine ⟨v, hvfilter.1, rfl, hvfilter.2, hk, q, ?_, ?_⟩
      · rw [PortInterlayer.ports, Finset.mem_product]
        exact ⟨Finset.mem_univ _, by simp [hvq]⟩
      · exact hqi
    · rw [if_neg hk] at hu
      simp at hu

theorem portStack_expands (H : StandaloneGraph n) (ℓ : ℕ)
    (P : ℕ → PortInterlayer n) (β : ℝ → ℝ) (a p : ℝ)
    (hP : ∀ k, k + 1 < ℓ → ∀ T x, x ∈ Icc a p → x ≤ (T.card : ℝ) / n →
      β x * n ≤ ((P k).neighborhood T).card) :
    (portStack H ℓ P).Expands β a p := by
  intro k T x hk hT hxactive hx
  change T ⊆ (if k < ℓ then Finset.univ.image (fun i : Fin n => (k, i)) else ∅) at hT
  change _ ≤ ((if k + 1 < ℓ then
    ((P k).neighborhood ((T.filter fun v => v.1 = k).image Prod.snd)).image
      (fun i : Fin n => (k + 1, i)) else ∅).card : ℝ)
  let I := (T.filter fun v => v.1 = k).image Prod.snd
  have hdepth : ∀ v ∈ T, v.1 = k := by
    intro v hv
    have := hT hv
    rw [if_pos (show k < ℓ by omega)] at this
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    rw [← hi]
  have hfilter : T.filter (fun v => v.1 = k) = T :=
    Finset.filter_eq_self.2 hdepth
  have hIcard : I.card = T.card := by
    change ((T.filter fun v => v.1 = k).image Prod.snd).card = T.card
    rw [hfilter, Finset.card_image_iff.mpr]
    intro a ha b hb hab
    apply Prod.ext
    · exact (hdepth a ha).trans (hdepth b hb).symm
    · exact hab
  have hxI : x ≤ (I.card : ℝ) / n := by rwa [hIcard]
  rw [if_pos hk, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  exact hP k hk I x hxactive hxI


theorem portStack_depthRobust (H : StandaloneGraph n) (ℓ : ℕ)
    (P : ℕ → PortInterlayer n) {t d₀ : ℕ}
    (hH : ∀ X : Finset (Fin n), t ≤ X.card →
      ∃ p : List (Fin n), p ≠ [] ∧ p.IsChain H.edge ∧
        (∀ v ∈ p, v ∈ X) ∧ d₀ ≤ p.length) :
    (portStack H ℓ P).DepthRobust t d₀ := by
  classical
  intro k hk X hX hXcard
  have hdepth : ∀ v ∈ X, v.1 = k := by
    intro v hv
    exact (((portStack H ℓ P).layer_mem).mp (hX hv)).1
  have hcard : (X.image Prod.snd).card = X.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact Prod.ext ((hdepth a ha).trans (hdepth b hb).symm) hab
  obtain ⟨p, hp, hc, hm, hl⟩ := hH (X.image Prod.snd) (by rwa [hcard])
  refine ⟨p.map (fun i => (k, i)), by simpa using hp, ?_, ?_, by simpa using hl⟩
  · exact List.isChain_map_of_isChain _ (fun a b h => ⟨rfl, rfl, hk, h⟩) hc
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp (hm w hw)
    have : v = (k, w) := Prod.ext (hdepth v hv) hvw
    rwa [← this]

end ProofOfSpace.Concrete

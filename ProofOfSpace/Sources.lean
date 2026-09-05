/-
Copyright (c) 2026 Diego de Estrada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diego de Estrada
-/
import ProofOfSpace.Model

/-! # Exact source counts from ordinary depth robustness

All lengths count vertices. The `+1` makes the prefix and full-source endpoints
instances of one integer formula, without a separate mixing parameter.
-/
namespace ProofOfSpace.Concrete
open Finset Set
universe u
variable {V : Type u} {ℓ n : ℕ}

namespace LayeredGraph
variable (G : LayeredGraph V ℓ n)

noncomputable def deepSources (F : Finset V) (q : ℕ) : Finset V := by
  classical
  exact F.filter fun v => ∃ Q : Path G.edge (fun x => x ∈ F),
    q ≤ Q.length ∧ Q.first = v

theorem mem_deepSources {F : Finset V} {q : ℕ} {v : V} :
    v ∈ G.deepSources F q ↔ v ∈ F ∧
      ∃ Q : Path G.edge (fun x => x ∈ F), q ≤ Q.length ∧ Q.first = v := by
  classical
  simp [deepSources]

theorem deepSources_subset (F : Finset V) (q : ℕ) : G.deepSources F q ⊆ F := by
  classical
  exact Finset.filter_subset _ _

/-- S `p`-vertex footprint contains at least `p-t+d₀-q+1` sources of `q`-vertex paths. -/
theorem card_deepSources {d t d₀ p q : ℕ} {F : Finset V}
    (hDR : G.DepthRobustAt d t d₀) (hF : F ⊆ G.layer d)
    (hP : p ≤ F.card) (hTP : t ≤ p) (hq : 1 ≤ q) (hqD : q ≤ d₀) :
    p - t + (d₀ - q + 1) ≤ (G.deepSources F q).card := by
  classical
  let W := G.deepSources F q
  obtain ⟨Y, hYW, hYcard⟩ := Finset.exists_subset_card_eq
    (min_le_right (p - t) W.card)
  have hYF : Y ⊆ F := hYW.trans (G.deepSources_subset F q)
  have hYsmall : Y.card ≤ p - t := by rw [hYcard]; exact min_le_left _ _
  have hlarge : t ≤ (F \ Y).card := by
    rw [Finset.card_sdiff_of_subset hYF]; omega
  obtain ⟨l, hne, hchain, hmem, hlen⟩ :=
    hDR (F \ Y) (Finset.sdiff_subset.trans hF) hlarge
  let Q : Path G.edge (fun x => x ∈ F) := {
    nodes := l
    nonempty := hne
    chain := hchain.imp fun _ _ h => Or.inl ⟨d, h⟩
    unpebbled' := fun v hv => (Finset.mem_sdiff.mp (hmem v hv)).1 }
  let m := d₀ - q + 1
  have hm : m ≤ Q.length := by dsimp [m, Q, Path.length]; omega
  let Z := Finset.univ.image fun i : Fin m => Q.nodes[i.val]'(lt_of_lt_of_le i.isLt hm)
  have hZcard : Z.card = m := by
    dsimp [Z]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Fin.ext ((G.path_nodup Q).getElem_inj_iff.mp hij)
  have hZW : Z ⊆ W := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    have hi : i.val < Q.length := lt_of_lt_of_le i.isLt hm
    apply G.mem_deepSources.mpr
    refine ⟨Q.unpebbled' _ (List.getElem_mem _), Q.drop i.val hi, ?_, ?_⟩
    · rw [Path.drop_length]
      have := i.isLt
      dsimp [m] at this
      have : d₀ ≤ Q.length := hlen
      omega
    · exact Path.drop_first _ _ _
  have hdisj : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro v hvY hvZ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvZ
    exact (Finset.mem_sdiff.mp (hmem _ (List.getElem_mem _))).2 hvY
  have hsum : Y.card + Z.card ≤ W.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hYW hZW)
  rw [hYcard, hZcard] at hsum
  dsimp [m] at hsum
  change p - t + (d₀ - q + 1) ≤ W.card
  omega

end LayeredGraph

namespace Pebbling
variable {G : LayeredGraph V ℓ n} {δ ρ : ℝ} (B : Pebbling G δ ρ)

/-- Both the complete path and the continuation sources live inside the footprint. -/
structure SourceData (S : Finset V) (b d₀ s q : ℕ) where
  long : Path G.edge B.unpebbled
  long_mem : ∀ v ∈ long.nodes, v ∈ B.layerFootprint S b
  long_length : d₀ ≤ long.length
  source : Finset V
  source_sub : source ⊆ B.layerFootprint S b
  source_card : source.card = s
  source_path : ∀ v ∈ source, ∃ Q : Path G.edge B.unpebbled,
    Q.first = v ∧ (∀ x ∈ Q.nodes, x ∈ B.layerFootprint S b) ∧ q ≤ Q.length

theorem sourceData {S : Finset V} {b t d₀ p s : ℕ}
    (hDR : G.DepthRobustAt b t d₀) (hTP : t ≤ p)
    (hq : 1 ≤ min d₀ (d₀ + p + 1 - (t + s)))
    (hfert : p ≤ (B.layerFootprint S b).card) :
    Nonempty (B.SourceData S b d₀ s (min d₀ (d₀ + p + 1 - (t + s)))) := by
  classical
  let F := B.layerFootprint S b
  let q := min d₀ (d₀ + p + 1 - (t + s))
  have hqD : q ≤ d₀ := min_le_left _ _
  have hcount := G.card_deepSources hDR (B.layerFootprint_subset S b) hfert hTP hq hqD
  have hSW : s ≤ (G.deepSources F q).card := by
    have hqsum : q ≤ d₀ + p + 1 - (t + s) := min_le_right _ _
    change p - t + (d₀ - q + 1) ≤ (G.deepSources F q).card at hcount
    omega
  obtain ⟨Z, hZW, hZcard⟩ := Finset.exists_subset_card_eq hSW
  have hZF : Z ⊆ F := hZW.trans (G.deepSources_subset F q)
  have havail : ∀ v ∈ F, B.unpebbled v := fun v hv =>
    B.footprint_available S ((B.mem_layerFootprint S).mp hv).2
  obtain ⟨l, hlne, hlchain, hlmem, hllen⟩ :=
    hDR F (B.layerFootprint_subset S b) (hTP.trans hfert)
  let L : Path G.edge B.unpebbled := {
    nodes := l
    nonempty := hlne
    chain := hlchain.imp fun _ _ h => Or.inl ⟨b, h⟩
    unpebbled' := fun v hv => havail v (hlmem v hv) }
  refine ⟨⟨L, hlmem, hllen, Z, hZF, hZcard, ?_⟩⟩
  intro v hv
  obtain ⟨_, Q, hQlen, hQfirst⟩ := G.mem_deepSources.mp (hZW hv)
  let R : Path G.edge B.unpebbled := {
    nodes := Q.nodes
    nonempty := Q.nonempty
    chain := Q.chain
    unpebbled' := fun x hx => havail x (Q.unpebbled' x hx) }
  exact ⟨R, hQfirst, Q.unpebbled', hQlen⟩

end Pebbling
end ProofOfSpace.Concrete

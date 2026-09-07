import ProofOfSpace.Model
import Mathlib.Data.Finset.Lattice.Fold

/-! # Ordered graphs and block depth robustness

Vertices are numbered from zero. Path lengths count vertices. Block deletion at
`v` removes the at most `b` vertices ending at `v`, truncated at vertex zero.
-/
namespace ProofOfSpace.DRSample

open Finset

/-- An ordered directed graph, with every edge pointing to a larger vertex. -/
structure OrderedGraph (n : ℕ) where
  edge : Fin n → Fin n → Prop
  increasing : ∀ {u v}, edge u v → u < v

variable {n : ℕ}

/-- A path of at least `d` vertices, avoiding the deleted vertices. -/
def HasPath (G : OrderedGraph n) (deleted : Finset (Fin n)) (d : ℝ) : Prop :=
  ∃ P : List (Fin n), P ≠ [] ∧ P.IsChain G.edge ∧
    (∀ v ∈ P, v ∉ deleted) ∧ d ≤ (P.length : ℝ)

/-- The deleted set is quantified after the graph has been sampled. -/
def DepthRobust (G : OrderedGraph n) (e : ℕ) (d : ℝ) : Prop :=
  ∀ deleted : Finset (Fin n), deleted.card ≤ e → HasPath G deleted d

/-- The union of left intervals of width `b` ending at members of `S`. -/
def blockDeleted (b : ℕ) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact univ.filter fun u => ∃ v ∈ S, u ≤ v ∧ v.val < u.val + b

/-- Block depth robustness counts interval endpoints, including overlapping
intervals and intervals truncated at zero. -/
def BlockDepthRobust (G : OrderedGraph n) (e : ℕ) (d : ℝ) (b : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ e → HasPath G (blockDeleted b S) d

theorem mem_blockDeleted {b : ℕ} {S : Finset (Fin n)} {u : Fin n} :
    u ∈ blockDeleted b S ↔ ∃ v ∈ S, u ≤ v ∧ v.val < u.val + b := by
  classical
  simp [blockDeleted]

theorem subset_blockDeleted {b : ℕ} (hb : 0 < b) (S : Finset (Fin n)) :
    S ⊆ blockDeleted b S := by
  intro v hv
  exact mem_blockDeleted.mpr ⟨v, hv, le_rfl, by omega⟩

theorem HasPath.mono_deleted {G : OrderedGraph n} {S T : Finset (Fin n)}
    {d : ℝ} (h : HasPath G T d) (hST : S ⊆ T) : HasPath G S d := by
  obtain ⟨P, hne, hchain, havoid, hlen⟩ := h
  exact ⟨P, hne, hchain, fun v hv hS => havoid v hv (hST hS), hlen⟩

theorem HasPath.mono_length {G : OrderedGraph n} {S : Finset (Fin n)}
    {d d' : ℝ} (h : HasPath G S d) (hdd' : d' ≤ d) : HasPath G S d' := by
  obtain ⟨P, hne, hchain, havoid, hlen⟩ := h
  exact ⟨P, hne, hchain, havoid, hdd'.trans hlen⟩

/-- The implication used in Conjecture 1 requires no additional random event. -/
theorem BlockDepthRobust.depthRobust {G : OrderedGraph n} {e b : ℕ} {d : ℝ}
    (h : BlockDepthRobust G e d b) (hb : 0 < b) : DepthRobust G e d := by
  intro S hS
  exact (h S hS).mono_deleted (subset_blockDeleted hb S)

theorem DepthRobust.mono {G : OrderedGraph n} {e e' : ℕ} {d d' : ℝ}
    (h : DepthRobust G e d) (he : e' ≤ e) (hd : d' ≤ d) : DepthRobust G e' d' := by
  intro S hS
  exact (h S (hS.trans he)).mono_length hd

theorem BlockDepthRobust.mono {G : OrderedGraph n} {e e' b : ℕ} {d d' : ℝ}
    (h : BlockDepthRobust G e d b) (he : e' ≤ e) (hd : d' ≤ d) :
    BlockDepthRobust G e' d' b := by
  intro S hS
  exact (h S (hS.trans he)).mono_length hd

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.MetaProbability

/-! # The original graph sampled in independent rows of destinations -/
namespace ProofOfSpace.DRSample
open Finset Classical

def rowGraph {n m : ℕ} (hm : 0 < m) (R : ℕ)
    (s : SampleSpace (Fin m → Finset (Fin n)) R) : OrderedGraph n where
  edge u v := u < v ∧ (u.val + 1 = v.val ∨
    u ∈ getSample (fun _ => ∅) R s (v.val / m) ⟨v.val % m, Nat.mod_lt _ hm⟩)
  increasing h := h.1

theorem rowGraph_hasLine {n m R : ℕ} (hm : 0 < m)
    (s : SampleSpace (Fin m → Finset (Fin n)) R) : HasLine (rowGraph hm R s) := by
  intro u v huv
  exact ⟨by change u.val < v.val; omega, Or.inl huv⟩

theorem rowGraph_edge {n m R j : ℕ} (hm : 0 < m)
    (s : SampleSpace (Fin m → Finset (Fin n)) R) (k : Fin m) (v : Fin n)
    (hv : v.val = j * m + k.val) (u : Fin n) (huv : u < v)
    (hu : u ∈ getSample (fun _ => ∅) R s j k) : (rowGraph hm R s).edge u v := by
  refine ⟨huv, Or.inr ?_⟩
  have hdiv : v.val / m = j := by
    rw [hv]
    have hk := k.isLt
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hmod : (⟨v.val % m, Nat.mod_lt _ hm⟩ : Fin m) = k := by
    apply Fin.ext
    change v.val % m = k.val
    rw [hv]
    have hdivision := Nat.mod_add_div v.val m
    rw [hdiv, hv] at hdivision
    nlinarith
  simpa only [hdiv, hmod] using hu

theorem mapped_meta_edge_port {n m M : ℕ} (hm : 3 ≤ m) (hn : M * m ≤ n)
    (s : SampleSpace (Fin m → Finset (Fin n)) M) (i j : Fin M)
    (h : (exposedGraph M (mapSamples (metaParents hm hn) M s)).edge i j) :
    PortEdge (rowGraph (by omega) M s) m i j := by
  have hij : i.val < j.val := h.1
  have hchoice := h.2
  rw [choiceAt_mapSamples (metaParents hm hn) (fun _ => ∅) s j.isLt] at hchoice
  obtain ⟨_, hkind⟩ := (mem_filter.mp hchoice).2
  rcases hkind with hline | ⟨k, hk, a, ha⟩
  · have hjn : j.val * m < n := by
      have hjM := j.isLt
      have hmul := Nat.mul_le_mul_right m (show j.val + 1 ≤ M by omega)
      nlinarith
    have huN : (i.val + 1) * m - 1 < n := by rw [hline]; omega
    let u : Fin n := ⟨(i.val + 1) * m - 1, huN⟩
    let v : Fin n := ⟨j.val * m, hjn⟩
    refine ⟨u, v, rowGraph_hasLine (by omega) s u v ?_, ?_, ?_, le_rfl, ?_⟩
    · dsimp [u, v]
      rw [hline]
      have hjpos : 0 < j.val := by omega
      have hprod : 0 < j.val * m := Nat.mul_pos hjpos (by omega)
      omega
    · dsimp [u]
      have ht : 0 < m / 3 := by omega
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · dsimp [u]
      have hpos : 0 < (i.val + 1) * m := by positivity
      omega
    · dsimp [v]
      have ht : 0 < m / 3 := by omega
      omega
  · have hvN : j.val * m + k.val < n := by
      have hmul := Nat.mul_le_mul_right m (show j.val + 1 ≤ M by omega)
      nlinarith [k.isLt]
    let v : Fin n := ⟨j.val * m + k.val, hvN⟩
    have hout := outgoingVertex_bounds hm hn i a
    have hsource : (outgoingVertex hm hn i a) < v := by
      have hmul := Nat.mul_le_mul_right m (show i.val + 1 ≤ j.val by omega)
      change (outgoingVertex hm hn i a).val < j.val * m + k.val
      omega
    refine ⟨outgoingVertex hm hn i a, v,
      rowGraph_edge (by omega) s k v rfl _ hsource ha, ?_, hout.2, ?_, ?_⟩
    · dsimp [outgoingVertex]; omega
    · dsimp [v]; omega
    · dsimp [v]; omega

theorem getSample_future {α : Type*} (fallback : α) {R j : ℕ}
    (s : SampleSpace α R) (hj : R ≤ j) : getSample fallback R s j = fallback := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [getSample, if_neg (by omega)]
    exact ih s.1 (by omega)

theorem rowGraph_mono {n m R : ℕ} (hm : 0 < m)
    (s : SampleSpace (Fin m → Finset (Fin n)) R) (row : Fin m → Finset (Fin n))
    {u v : Fin n} (h : (rowGraph hm R s).edge u v) :
    (rowGraph hm (R + 1) (s, row)).edge u v := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hline | hsample
  · exact Or.inl hline
  · right
    have hne : v.val / m ≠ R := by
      intro he
      rw [getSample_future (fun _ => ∅) s (show R ≤ v.val / m by omega)] at hsample
      exact notMem_empty _ hsample
    simpa only [getSample, if_neg hne] using hsample

theorem HasPath.mono_graph {n : ℕ} {G H : OrderedGraph n}
    (hgraph : ∀ u v, G.edge u v → H.edge u v) {D : Finset (Fin n)} {d : ℝ}
    (h : HasPath G D d) : HasPath H D d := by
  obtain ⟨P, hne, hc, ha, hl⟩ := h
  exact ⟨P, hne, hc.imp hgraph, ha, hl⟩

theorem BlockDepthRobust.mono_graph {n e b : ℕ} {d : ℝ} {G H : OrderedGraph n}
    (hgraph : ∀ u v, G.edge u v → H.edge u v) (h : BlockDepthRobust G e d b) :
    BlockDepthRobust H e d b := fun S hS => (h S hS).mono_graph hgraph

end ProofOfSpace.DRSample

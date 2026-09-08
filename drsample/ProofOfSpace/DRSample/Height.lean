import ProofOfSpace.DRSample.Basic

/-! # Actual depth labels in an ordered DAG -/
namespace ProofOfSpace.DRSample

open Finset
variable {n : ℕ}

noncomputable def OrderedGraph.parents (G : OrderedGraph n) (v : Fin n) :
    Finset (Fin n) := by
  classical
  exact univ.filter fun u => G.edge u v

@[simp] theorem OrderedGraph.mem_parents {G : OrderedGraph n} {u v : Fin n} :
    u ∈ G.parents v ↔ G.edge u v := by
  classical
  simp [OrderedGraph.parents]

/-- Deleted vertices have height zero. A surviving vertex has height one plus
its maximum predecessor height, with maximum zero for an empty predecessor set. -/
noncomputable def height (G : OrderedGraph n) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  if v ∈ S then 0 else
    (G.parents v).attach.sup (fun u => height G S u.val) + 1
termination_by v.val
decreasing_by
  exact G.increasing (OrderedGraph.mem_parents.mp u.property)

theorem height_eq_zero {G : OrderedGraph n} {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ S) : height G S v = 0 := by
  rw [height, if_pos hv]

theorem height_pos {G : OrderedGraph n} {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∉ S) : 0 < height G S v := by
  rw [height, if_neg hv]
  omega

theorem height_pos_iff {G : OrderedGraph n} {S : Finset (Fin n)} {v : Fin n} :
    0 < height G S v ↔ v ∉ S := by
  refine ⟨fun h hv => ?_, height_pos⟩
  rw [height_eq_zero hv] at h
  omega

theorem height_lt_of_edge {G : OrderedGraph n} {S : Finset (Fin n)}
    {u v : Fin n} (hv : v ∉ S) (huv : G.edge u v) :
    height G S u < height G S v := by
  classical
  rw [height.eq_def G S v, if_neg hv]
  have hmem : u ∈ G.parents v := OrderedGraph.mem_parents.mpr huv
  have hle := Finset.le_sup (f := fun a : {u // u ∈ G.parents v} => height G S a.val)
    (Finset.mem_attach (G.parents v) ⟨u, hmem⟩)
  exact Nat.lt_succ_of_le hle

/-- The depth recurrence equates a shallow destination with avoidance of a
nested set of previously exposed predecessors. -/
theorem height_le_iff {G : OrderedGraph n} {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∉ S) {k : ℕ} (hk : 0 < k) :
    height G S v ≤ k ↔ ∀ u, G.edge u v → height G S u < k := by
  classical
  rw [height.eq_def G S v, if_neg hv]
  constructor
  · intro h u hu
    have hmem : u ∈ G.parents v := OrderedGraph.mem_parents.mpr hu
    have hle := Finset.le_sup (f := fun a : {u // u ∈ G.parents v} => height G S a.val)
      (Finset.mem_attach (G.parents v) ⟨u, hmem⟩)
    dsimp only at hle
    omega
  · intro h
    have hle : (G.parents v).attach.sup (fun u => height G S u.val) ≤ k - 1 := by
      apply Finset.sup_le
      intro u _
      have := h u.val (OrderedGraph.mem_parents.mp u.property)
      omega
    omega


/-- Every positive depth label is witnessed by an actual surviving path. -/
theorem height_path (G : OrderedGraph n) (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) :
    ∃ P : List (Fin n), P ≠ [] ∧ P.IsChain G.edge ∧
      (∀ u ∈ P, u ∉ S) ∧ P.getLast? = some v ∧ P.length = height G S v := by
  classical
  induction v using (measure (fun v : Fin n => v.val)).wf.induction with
  | h v ih =>
    set a := (G.parents v).attach.sup (fun u => height G S u.val) with ha
    have hheight : height G S v = a + 1 := by
      rw [height.eq_def G S v, if_neg hv]
    by_cases ha0 : a = 0
    · refine ⟨[v], by simp, .singleton _, ?_, by simp, ?_⟩
      · simpa using hv
      · simp [hheight, ha0]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      obtain ⟨u, hu, hau⟩ := (Finset.le_sup_iff hapos).mp (le_refl a)
      have huv : G.edge u.val v := OrderedGraph.mem_parents.mp u.property
      have huS : u.val ∉ S := height_pos_iff.mp (lt_of_lt_of_le hapos hau)
      obtain ⟨P, hne, hchain, havoid, hlast, hlen⟩ := ih u.val (G.increasing huv) huS
      have huheight : height G S u.val = a := le_antisymm
        (Finset.le_sup (f := fun u : {u // u ∈ G.parents v} => height G S u.val) hu) hau
      refine ⟨P ++ [v], by simp, hchain.append (.singleton _) ?_, ?_, by simp, ?_⟩
      · simpa [hlast] using huv
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact havoid w hw
        · simpa using List.mem_singleton.mp hw ▸ hv
      · simp [hlen, huheight, hheight]

/-- The largest actual depth label in the graph. -/
noncomputable def depth (G : OrderedGraph n) (S : Finset (Fin n)) : ℕ :=
  univ.sup (height G S)

theorem height_le_depth (G : OrderedGraph n) (S : Finset (Fin n)) (v : Fin n) :
    height G S v ≤ depth G S :=
  Finset.le_sup (f := height G S) (mem_univ v)

theorem hasPath_of_le_depth {G : OrderedGraph n} {S : Finset (Fin n)} {d : ℝ}
    (hd : 0 < d) (h : d ≤ (depth G S : ℝ)) : HasPath G S d := by
  classical
  have hpos : 0 < depth G S := by exact_mod_cast (lt_of_lt_of_le hd h)
  obtain ⟨v, _, hv⟩ := (Finset.le_sup_iff hpos).mp (le_refl (depth G S))
  obtain ⟨P, hne, hchain, havoid, _, hlen⟩ :=
    height_path G S v (height_pos_iff.mp (hpos.trans_le hv))
  refine ⟨P, hne, hchain, havoid, ?_⟩
  rw [hlen]
  exact h.trans (by exact_mod_cast hv)

end ProofOfSpace.DRSample

import ProofOfSpace.DRSample.TriangularProbability

namespace ProofOfSpace.DRSample
open Finset Classical

theorem OrderedGraph.ext_edge {n : ℕ} {G H : OrderedGraph n} (h : G.edge = H.edge) : G = H := by
  cases G
  cases H
  simp_all

def triangleDestination {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (jk : Fin M × Fin (20 * a)) : Fin n :=
  ⟨t + jk.1.val * (20 * a) + jk.2.val, by
    have h := Nat.mul_le_mul_right (20 * a) jk.1.isLt
    nlinarith [jk.2.isLt]⟩

theorem triangleDestination_injective {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) : Function.Injective (triangleDestination hn) := by
  intro x y he
  have hv := congrArg Fin.val he
  dsimp [triangleDestination] at hv
  have hv' : x.1.val * (20 * a) + x.2.val = y.1.val * (20 * a) + y.2.val := by omega
  have hmod := congrArg (fun z => z % (20 * a)) hv'
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod, zero_add,
    Nat.mod_eq_of_lt x.2.isLt,
    Nat.mod_eq_of_lt y.2.isLt] at hmod
  have hdiv : x.1.val = y.1.val := by nlinarith
  exact Prod.ext (Fin.ext hdiv) (Fin.ext hmod)

def triangleFlatGraph {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (rows : Fin M × Fin (20 * a) → Finset (Fin n)) : OrderedGraph M where
  edge i j := i < j ∧ i ∈ triangleParents hn j.val (fun k => rows (j, k))
  increasing h := h.1

def triangleGraph {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (sets : Fin n → Finset (Fin n)) : OrderedGraph M :=
  triangleFlatGraph hn (fun jk => sets (triangleDestination hn jk))

theorem triangle_graph_samples {n t a M : ℕ} (hn : t + M * (20 * a) ≤ n)
    (s : SampleSpace (Fin (20 * a) → Finset (Fin n)) M) :
    triangleFlatGraph hn (fun jk => getSample (fun _ => ∅) M s jk.1.val jk.2) =
      exposedGraph M (mapSamples (triangleParents hn) M s) := by
  have he : (triangleFlatGraph hn (fun jk => getSample (fun _ => ∅) M s jk.1.val jk.2)).edge =
      (exposedGraph M (mapSamples (triangleParents hn) M s)).edge := by
    funext i j
    simp only [triangleFlatGraph, exposedGraph,
      choiceAt_mapSamples (triangleParents hn) (fun _ => ∅) s j.isLt]
    rfl
  exact OrderedGraph.ext_edge he

theorem triangleGraph_probability {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (p : ℕ → FiniteLaw (Finset (Fin n)))
    (event : OrderedGraph M → Prop) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets => event (triangleGraph hn sets)) =
      (independentSamples (triangleRowLaw t a p) M).probability
        (fun s => event (exposedGraph M (mapSamples (triangleParents hn) M s))) := by
  have hrows := independentSamples_as_pi (fun _ : Fin (20 * a) => (∅ : Finset (Fin n)))
    (triangleRowLaw t a p) M
  have hflat := congrArg (fun law => law.map
    (fun rows (jk : Fin M × Fin (20 * a)) => rows jk.1 jk.2)) hrows
  rw [FiniteLaw.map_comp] at hflat
  change _ = (FiniteLaw.pi (fun j : Fin M =>
    FiniteLaw.pi (fun k : Fin (20 * a) => p (t + j.val * (20 * a) + k.val)))).map _ at hflat
  rw [FiniteLaw.pi_uncurry] at hflat
  have hver := FiniteLaw.pi_map_injective (fun v : Fin n => p v.val)
    (triangleDestination hn) (triangleDestination_injective ha hn)
  change _ = FiniteLaw.pi (fun jk : Fin M × Fin (20 * a) =>
    p (t + jk.1.val * (20 * a) + jk.2.val)) at hver
  have he := hflat.trans hver.symm
  have hprob := congrArg (fun law => law.probability (fun rows => event (triangleFlatGraph hn rows))) he
  simp only [FiniteLaw.probability_map, Function.comp_def, triangle_graph_samples] at hprob
  exact hprob.symm

theorem triangleGraph_robustness {n t a M : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hn : t + M * (20 * a) ≤ n) (p : ℕ → FiniteLaw (Finset (Fin n)))
    {eta : ℝ} (heta : 0 < eta)
    (havoid : ∀ v < n, ∀ U : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents U) ≤
        Real.exp (-eta * ∑ u ∈ U, harmonicAt n v u)) :
    (FiniteLaw.pi (fun v : Fin n => p v.val)).probability (fun sets =>
      DepthRobust (triangleGraph hn sets) (M / 3)
        ((M / 2 : ℝ) * Real.exp (-323 / (eta * (20 * a : ℕ))))) ≥
      1 - Real.exp (-((8 / 5 : ℝ) - Real.log 4) * M) := by
  rw [triangleGraph_probability ha hn p
    (fun G => DepthRobust G (M / 3) ((M / 2 : ℝ) * Real.exp (-323 / (eta * (20 * a : ℕ)))))]
  have h := multiscale_mapped_sharp hM (triangleRowLaw t a p) (triangleParents hn)
    (lambda := eta * (119 / 800 : ℝ) * (20 * a : ℕ)) (by positivity)
    (fun j hj A => triangleParents_avoidance ha hn hj p heta.le havoid A)
  apply h.trans
  apply FiniteLaw.probability_mono
  intro s hs
  apply hs.mono le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hB : (0 : ℝ) < (20 * a : ℕ) := by positivity
  field_simp
  nlinarith

theorem incomingGraph_hasLine {n : ℕ} (sets : Fin n → Finset (Fin n)) :
    HasLine (incomingGraph sets) := by
  intro u v huv
  exact ⟨by change u.val < v.val; omega, Or.inl huv⟩

theorem triangleGraph_edge_port {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (sets : Fin n → Finset (Fin n)) (i j : Fin M)
    (he : (triangleGraph hn sets).edge i j) : TrianglePortEdge (incomingGraph sets) t a i j := by
  have hij : i.val < j.val := he.1
  obtain ⟨_, hkind⟩ := (mem_filter.mp he.2).2
  rcases hkind with hline | ⟨k, hk, p, hp, hmem⟩
  · have hjn : t + j.val * (20 * a) < n := by
      have h := Nat.mul_le_mul_right (20 * a) j.isLt
      nlinarith
    have hjpos : 0 < t + j.val * (20 * a) := by
      have : 0 < j.val := by omega
      positivity
    let u : Fin n := ⟨t + j.val * (20 * a) - 1, by omega⟩
    let v : Fin n := ⟨t + j.val * (20 * a), hjn⟩
    have huv : u.val + 1 = v.val := by dsimp [u, v]; omega
    refine ⟨u, v, incomingGraph_hasLine sets u v huv, ?_, ?_, le_rfl, ?_, ?_⟩
    all_goals dsimp [u, v]; rw [← hline]; simp only [Nat.add_mul, Nat.one_mul]; omega
  · let v := triangleDestination hn (j, k)
    have hsource : triangleSource hn i p < v := by
      have h := Nat.mul_le_mul_right (20 * a) (Nat.succ_le_iff.mpr hij)
      change t + i.val * (20 * a) + 10 * a + p.val < t + j.val * (20 * a) + k.val
      nlinarith [p.isLt]
    have hmem' : triangleSource hn i p ∈ sets v := hmem
    have hoff := (mem_filter.mp hp).2
    refine ⟨triangleSource hn i p, v, ⟨hsource, Or.inr hmem'⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp [triangleSource, v, triangleDestination]; nlinarith [p.isLt]

end ProofOfSpace.DRSample

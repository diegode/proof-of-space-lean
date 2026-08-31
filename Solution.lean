import ProofOfSpace.ChungFilecoin
import ProofOfSpace.UnionBound

/-!
# Proved probabilistic Chung-8 latency theorem

This is the proved counterpart of `Challenge.lean`. It transports the statement's
eight-permutation sample to the construction library, applies the exact finite union
bound, constructs the repeated-interlayer stack, and invokes the deterministic latency
theorem whenever the sampled interlayer realizes the Chung-8 profile.
-/

namespace ProofOfSpaceStatement

open Finset Set
open scoped ENNReal
open ProofOfSpace

structure ChungInterlayer (n : ℕ) where
  perm : Fin 8 → Equiv.Perm (Fin n)
deriving Fintype

instance (n : ℕ) : Nonempty (ChungInterlayer n) :=
  ⟨⟨fun _ => Equiv.refl (Fin n)⟩⟩

namespace ChungInterlayer

noncomputable def uniformLaw (n : ℕ) : PMF (ChungInterlayer n) :=
  PMF.uniformOfFintype (ChungInterlayer n)

end ChungInterlayer

def interlayerEquiv (n : ℕ) :
    ChungInterlayer n ≃ Concrete.PermutationInterlayer n 8 where
  toFun P := ⟨P.perm⟩
  invFun P := ⟨P.perm⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

noncomputable def probabilityOf {A : Type*} (p : PMF A) (Q : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if Q a then p a else 0

def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (Q : A → Prop)
    (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p Q

private theorem probabilityOf_interlayerEquiv (Q : ChungInterlayer n → Prop) :
    probabilityOf (ChungInterlayer.uniformLaw n) Q =
      Concrete.probabilityOf (Concrete.PermutationInterlayer.uniformLaw n 8)
        (fun P => Q ((interlayerEquiv n).symm P)) := by
  classical
  unfold probabilityOf Concrete.probabilityOf ChungInterlayer.uniformLaw
    Concrete.PermutationInterlayer.uniformLaw
  rw [← (interlayerEquiv n).tsum_eq]
  apply tsum_congr
  intro P
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (interlayerEquiv n)]
  rfl

noncomputable def chord (a u b v x : ℝ) : ℝ :=
  u + (v - u) / (b - a) * (x - a)

noncomputable def chung8Beta (x : ℝ) : ℝ :=
  min (chord 0 0 (5089 / 100000) (1 / 5) x)
    (min (chord (5089 / 100000) (1 / 5) (46 / 625) (1331 / 5000) x)
    (min (chord (46 / 625) (1331 / 5000) (74 / 625) (3031 / 8000) x)
    (min (chord (74 / 625) (3031 / 8000) (811 / 5000) (4663 / 10000) x)
    (min (chord (811 / 5000) (4663 / 10000) (571 / 2500) (1143 / 2000) x)
    (min (chord (571 / 2500) (1143 / 2000) (3201 / 10000) (6799 / 10000) x)
    (min (chord (3201 / 10000) (6799 / 10000) (857 / 2000) (1929 / 2500) x)
    (min (chord (857 / 2000) (1929 / 2500) (5337 / 10000) (4189 / 5000) x)
    (min (chord (5337 / 10000) (4189 / 5000) (4969 / 8000) (551 / 625) x)
    (min (chord (4969 / 8000) (551 / 625) (3669 / 5000) (579 / 625) x)
    (min (chord (3669 / 5000) (579 / 625) (4 / 5) (94911 / 100000) x)
      (chord (4 / 5) (94911 / 100000) 1 1 x)))))))))))

namespace ChungInterlayer

def neighborhood {n : ℕ} (P : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  T.biUnion fun v => Finset.univ.image fun j : Fin 8 => P.perm j v

def Expands {n : ℕ} (P : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n),
    chung8Beta ((T.card : ℝ) / n) * n ≤ (P.neighborhood T).card

end ChungInterlayer

noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (chung8Beta ((k : ℝ) / n) * n) - 1 else 0

noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ((∑ k ∈ Finset.Ico 1 (n + 1), n.choose k *
        (n.choose (chung8FailureProfile n k) *
          ((chung8FailureProfile n k).descFactorial k * Nat.factorial (n - k)) ^ 8) : ℕ) :
      ℝ≥0∞) /
    ((Nat.factorial n ^ 8 : ℕ) : ℝ≥0∞)


structure LatencyData (ℓ : ℕ) where
  n : ℕ
  /-- The path fraction `α_π` produced by within-layer depth robustness. -/
  αpi : ℝ
  /-- The per-layer red-pebble budget `δ`, as a fraction of the layer width. -/
  δ : ℝ
  /-- The within-layer robustness threshold `π`: deleting at most `(1 - π) n` nodes of a
  layer still leaves an intra-layer path on `α_π n` surviving nodes. -/
  pi : ℝ
  /-- The total black-pebble budget `ρ = 1 - ε_space`, as a fraction of the layer width. -/
  ρ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def LatencyData.layer {ℓ : ℕ} (M : LatencyData ℓ) (d : ℕ) :
    Finset (ℕ × Fin M.n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin M.n => (d, i)) else ∅

def LatencyData.depth {ℓ : ℕ} (M : LatencyData ℓ) (v : ℕ × Fin M.n) : ℕ := v.1

def LatencyData.intraEdge {ℓ : ℕ} (M : LatencyData ℓ) (d : ℕ)
    (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d ∧ v.1 = d ∧ d < ℓ ∧ M.intra u.2 v.2

def LatencyData.interEdge {ℓ : ℕ} (M : LatencyData ℓ)
    (P : ChungInterlayer M.n) (d : ℕ)
    (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d + 1 ∧ v.1 = d ∧ d + 1 < ℓ ∧
    ∃ j : Fin 8, u.2 = P.perm j v.2

def LatencyData.edge {ℓ : ℕ} (M : LatencyData ℓ) (P : ChungInterlayer M.n)
    (u v : ℕ × Fin M.n) : Prop :=
  (∃ d, M.intraEdge d u v) ∨ (∃ d, M.interEdge P d u v)

class LiteratureHypotheses {ℓ : ℕ} (M : LatencyData ℓ) : Prop where
  intra_rank : ∀ {u v}, M.intra u v → u.val < v.val
  depth_robust : ∀ X : Finset (Fin M.n),
    ((X.card : ℝ) ≤ (1 - M.pi) * M.n) →
    ∃ p : List (Fin M.n), p ≠ [] ∧ p.IsChain M.intra ∧
      (∀ v ∈ p, v ∉ X) ∧ M.αpi * M.n ≤ (p.length : ℝ)
  black_subset : ∀ d, M.black d ⊆ M.layer d
  red_subset : ∀ d, M.red d ⊆ M.layer d
  black_total : ∀ m,
    ∑ d ∈ Finset.range m, ((M.black d).card : ℝ) / M.n ≤ M.ρ
  red_bound : ∀ d, ((M.red d).card : ℝ) ≤ M.δ * M.n
  n_pos : 0 < M.n

def LatencyEvent {ℓ : ℕ} (M : LatencyData ℓ) (A : Finset (ℕ × Fin M.n))
    (L : ℝ) (P : ChungInterlayer M.n) : Prop :=
  ∃ u a, a ∈ A ∧ ∃ Q : List (ℕ × Fin M.n),
    Q ≠ [] ∧ Q.IsChain (M.edge P) ∧
    (∀ v ∈ Q, v ∉ M.black (M.depth v) ∧ v ∉ M.red (M.depth v)) ∧
    Q.head? = some u ∧ Q.getLast? = some a ∧
    L ≤ (Q.length : ℝ)

private theorem failure_bound_eq (n : ℕ) :
    chung8FailureBound n =
      Concrete.permutationExpansionFailureBound ChungCurve.chung8Setting n 8 := by
  rfl

theorem latency_chung8_whp
    {ℓ : ℕ} (M : LatencyData ℓ) (A : Finset (ℕ × Fin M.n)) (L : ℝ)
    (hdet : ∀ P : ChungInterlayer M.n, P.Expands → LatencyEvent M A L P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (LatencyEvent M A L) (chung8FailureBound M.n) := by
  classical
  have hprofile :
      Concrete.PermutationExpansionWhpClaim ChungCurve.chung8Setting M.n 8
        (Concrete.permutationExpansionFailureBound ChungCurve.chung8Setting M.n 8) :=
    Concrete.permutationExpansion_canonical_whp ChungCurve.chung8Setting M.n 8
  rw [Concrete.PermutationExpansionWhpClaim, Concrete.HoldsWithFailureAtMost] at hprofile
  rw [HoldsWithFailureAtMost, failure_bound_eq, probabilityOf_interlayerEquiv]
  refine hprofile.trans ?_
  apply Concrete.probabilityOf_mono
  intro P hP
  let P' : ChungInterlayer M.n := (interlayerEquiv M.n).symm P
  apply hdet P'
  intro T
  exact hP T

/-- The Filecoin 15-layer specialization. Unlike `latency_chung8_whp`, this is where the
Filecoin values `π = 4/5`, `α_π = 1/5`, `δ = 189/5000`, `ρ = 4/5`, the source weight
`4311/5000`,
the within-layer robustness assumptions, and the concrete latency length enter. -/
theorem chung8_latency_15
    (M : LatencyData 15) [H : LiteratureHypotheses M]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hαpi : M.αpi = (1 : ℝ) / 5)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hpi : M.pi = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hweight : (4311 : ℝ) / 5000 ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (LatencyEvent M A
        ((1 : ℝ) / 5 * M.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * M.n))
      (chung8FailureBound M.n) := by
  apply latency_chung8_whp M A
  intro P hP
  let Pc : Concrete.PermutationInterlayer M.n 8 := interlayerEquiv M.n P
  have hPc : Pc.Expands ChungCurve.chung8Setting := by
    intro T
    exact hP T
  let standalone : Concrete.StandaloneGraph M.n :=
    { edge := M.intra, edge_lt := fun {_ _} h => H.intra_rank h }
  let G := Concrete.permutationStack standalone ChungCurve.chung8Setting 15 8 M.αpi H.n_pos
    (fun _ => Pc) (fun _ _ => hPc)
  let pebbling : Concrete.Pebbling G := {
    black := M.black
    red := M.red
    black_subset := by
      intro d v hv
      exact H.black_subset d hv
    red_subset := by
      intro d v hv
      exact H.red_subset d hv
    black_total := by
      intro m
      simpa only [ChungCurve.chung8Setting_rho, hρ] using H.black_total m
    red_bound := by
      intro d
      simpa only [ChungCurve.chung8Setting_delta, hδ] using H.red_bound d
  }
  have hDepth : G.DepthRobust G.αpi := by
    apply Concrete.permutationStack_depthRobust_of_nodeDR
    intro X hX
    apply H.depth_robust X
    have heq : (1 - ChungCurve.chung8Setting.pi) * (M.n : ℝ) =
        (1 - M.pi) * M.n := by
      rw [ChungCurve.chung8Setting_pi, hpi]
    rwa [heq] at hX
  have hA' : A ⊆ G.layer 0 := hA
  have hweight' : ChungCurve.chung8Setting.ζδ ≤ Concrete.Pebbling.weight M.n A := by
    simpa only [ChungCurve.chung8Setting_zetaDelta, Concrete.Pebbling.weight] using hweight
  have hpath := ProofOfSpace.ChungCurve.chung8_latency_15_deterministic G pebbling H.n_pos
    hαpi hDepth A hA' hred hweight'
  rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
  refine ⟨u, a, ha, Q.nodes, Q.nonempty, ?_, Q.unpebbled', ?_, ?_, hlength⟩
  · exact Q.chain
  · rw [List.head?_eq_some_head Q.nonempty]
    exact congrArg some hfirst
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast

end ProofOfSpaceStatement

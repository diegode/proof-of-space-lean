import ProofOfSpace.ChungFilecoinExpansion

namespace ProofOfSpaceStatement

open Finset Set
open scoped ENNReal
open ProofOfSpace

structure ChungInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)
deriving Fintype

instance (n : ℕ) : Nonempty (ChungInterlayer n) := ⟨⟨Equiv.refl _⟩⟩

namespace ChungInterlayer

noncomputable def uniformLaw (n : ℕ) : PMF (ChungInterlayer n) :=
  PMF.uniformOfFintype (ChungInterlayer n)

def ports {n : ℕ} (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

def neighborhood {n : ℕ} (P : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  (ports T).image fun q => (P.perm q).2

end ChungInterlayer

noncomputable def probabilityOf {A : Type*} (p : PMF A) (Q : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if Q a then p a else 0

def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (Q : A → Prop)
    (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p Q

noncomputable def chung8PebblingAlphaMin : ℝ := 961821 / 74555000
noncomputable def chung8PebblingAlphaMax : ℝ := 14155 / 14911
noncomputable def chung8AlphaMin : ℝ := chung8PebblingAlphaMin / 2
noncomputable def chung8AlphaMax : ℝ := 14533 / 14911
noncomputable def epsilonChung : ℝ := 1 / 2 ^ (22 : ℕ)
noncomputable def chung8Delta : ℝ := 189 / 10000
noncomputable def chung8DeltaN (n : ℕ) : ℝ := chung8Delta - 1 / n

noncomputable def chungExponent8 (x y : ℝ) : ℝ :=
  Real.binEntropy x + Real.binEntropy y +
    8 * (y * Real.binEntropy (x / y) - Real.binEntropy x)

def chung8AdmissibleFailure (n k m : ℕ) : Prop :=
  k < m ∧ m < n ∧
  chung8AlphaMin ≤ 1 - (m : ℝ) / n ∧
  chung8DeltaN n ≤ (m : ℝ) / n - (k : ℝ) / n ∧
  chungExponent8 ((k : ℝ) / n) ((m : ℝ) / n) ≤
    -epsilonChung * Real.log 2

noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  by classical exact ((Finset.range n).filter (chung8AdmissibleFailure n k)).sup id

namespace ChungInterlayer

def Expands {n : ℕ} (P : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n),
    chung8AlphaMin ≤ (T.card : ℝ) / n →
    (T.card : ℝ) / n ≤ chung8AlphaMax →
    chung8FailureProfile n T.card < (P.neighborhood T).card

end ChungInterlayer

noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (1 / 8) /
        (2 * Real.pi * chung8AlphaMin * Real.sqrt (chung8DeltaN n)) *
      Real.exp (-(n : ℝ) * epsilonChung * Real.log 2))

class ChungExpansionConditions (n : ℕ) : Prop where
  n_pos : 0 < n
  delta_pos : 0 < chung8DeltaN n
  grid_buffer : 1 / (n : ℝ) ≤ chung8AlphaMax - chung8PebblingAlphaMax

class ChungSecurityConditions (n : ℕ) (lambda : ℝ) : Prop
    extends ChungExpansionConditions n where
  security :
    (lambda - 12 / 5 - Real.logb 2 chung8AlphaMin -
      Real.logb 2 (chung8DeltaN n) / 2) / epsilonChung < n

/-- A static black/red pebbling position on an `ℓ`-layer stacked graph. -/
structure PebblingGame (ℓ : ℕ) where
  n : ℕ
  αpi : ℝ
  δ : ℝ
  pi : ℝ
  ρ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (M : PebblingGame ℓ) (d : ℕ) :
    Finset (ℕ × Fin M.n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin M.n => (d, i)) else ∅

def PebblingGame.depth {ℓ : ℕ} (M : PebblingGame ℓ) (v : ℕ × Fin M.n) : ℕ := v.1

def PebblingGame.intraEdge {ℓ : ℕ} (M : PebblingGame ℓ) (d : ℕ)
    (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d ∧ v.1 = d ∧ d < ℓ ∧ M.intra u.2 v.2

def PebblingGame.interEdge {ℓ : ℕ} (M : PebblingGame ℓ)
    (P : ChungInterlayer M.n) (d : ℕ) (u v : ℕ × Fin M.n) : Prop :=
  u.1 = d + 1 ∧ v.1 = d ∧ d + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin M.n)), (P.perm q).2 = u.2

def PebblingGame.edge {ℓ : ℕ} (M : PebblingGame ℓ) (P : ChungInterlayer M.n)
    (u v : ℕ × Fin M.n) : Prop :=
  (∃ d, M.intraEdge d u v) ∨ (∃ d, M.interEdge P d u v)

/-- Structural graph assumptions and pebble-budget constraints for an admissible game. -/
class PebblingGame.IsAdmissible {ℓ : ℕ} (M : PebblingGame ℓ) : Prop where
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

/-- The game has an unpebbled directed path of length at least `L` ending in `A`. -/
def PebblingGame.HasUnpebbledPathTo {ℓ : ℕ} (M : PebblingGame ℓ)
    (A : Finset (ℕ × Fin M.n))
    (L : ℝ) (P : ChungInterlayer M.n) : Prop :=
  ∃ u a, a ∈ A ∧ ∃ Q : List (ℕ × Fin M.n),
    Q ≠ [] ∧ Q.IsChain (M.edge P) ∧
    (∀ v ∈ Q, v ∉ M.black (M.depth v) ∧ v ∉ M.red (M.depth v)) ∧
    Q.head? = some u ∧ Q.getLast? = some a ∧ L ≤ (Q.length : ℝ)

/-! ### Bridges to the proved library -/

def interlayerEquiv (n : ℕ) : ChungInterlayer n ≃ Concrete.PortInterlayer n where
  toFun P := ⟨P.perm⟩
  invFun P := ⟨P.perm⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

private theorem probabilityOf_interlayerEquiv (Q : ChungInterlayer n → Prop) :
    probabilityOf (ChungInterlayer.uniformLaw n) Q =
      Concrete.probabilityOf (Concrete.PortInterlayer.uniformLaw n)
        (fun P => Q ((interlayerEquiv n).symm P)) := by
  classical
  unfold probabilityOf Concrete.probabilityOf ChungInterlayer.uniformLaw
    Concrete.PortInterlayer.uniformLaw
  rw [← (interlayerEquiv n).tsum_eq]
  apply tsum_congr
  intro P
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (interlayerEquiv n)]
  rfl

private theorem public_profile_iff (P : ChungInterlayer n) :
    P.Expands ↔
      (interlayerEquiv n P).ExpandsProfileOn chung8AlphaMin chung8AlphaMax
        (chung8FailureProfile n) := by
  rw [ChungInterlayer.Expands, Concrete.PortInterlayer.ExpandsProfileOn]
  constructor <;> intro h T ha hb
  · simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T ha hb
  · simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T ha hb

private theorem internalExpansionConditions (n : ℕ) [C : ChungExpansionConditions n] :
    ChungCurve.FiniteExpansionConditions n where
  n_pos := C.n_pos
  delta_pos := by simpa [chung8DeltaN, chung8Delta, ChungCurve.finiteExpansionMargin,
    ChungCurve.expansionMargin] using C.delta_pos
  grid_buffer := by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin, chung8AlphaMax, chung8PebblingAlphaMax,
      ChungCurve.expansionAlphaMax_eq, ChungCurve.filecoinAlphaMax] using C.grid_buffer

private theorem internalSecurityConditions (n : ℕ) (lambda : ℝ)
    [C : ChungSecurityConditions n lambda] :
    ChungCurve.ExpansionSecurityConditions n lambda where
  n_pos := C.n_pos
  delta_pos := by simpa [chung8DeltaN, chung8Delta, ChungCurve.finiteExpansionMargin,
    ChungCurve.expansionMargin] using C.delta_pos
  grid_buffer := by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin, chung8AlphaMax, chung8PebblingAlphaMax,
      ChungCurve.expansionAlphaMax_eq, ChungCurve.filecoinAlphaMax] using C.grid_buffer
  security := by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin, chung8DeltaN, chung8Delta,
      ChungCurve.finiteExpansionMargin, ChungCurve.expansionMargin, epsilonChung,
      ChungCurve.expansionEpsilon] using C.security

private theorem publicFailureProfile_le (n k : ℕ) : chung8FailureProfile n k ≤ n := by
  classical
  rw [chung8FailureProfile]
  apply Finset.sup_le
  intro m hm
  exact (Finset.mem_range.1 (Finset.mem_filter.1 hm).1).le

private theorem polygonProfile_admissible (n : ℕ) [ChungCurve.FiniteExpansionConditions n]
    (k : ℕ) (hk : chung8AlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ chung8AlphaMax) :
    chung8AdmissibleFailure n k (ChungCurve.roundedExpansionProfile n k) := by
  have hk' : ChungCurve.expansionAlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ ChungCurve.expansionAlphaMax := by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin, chung8AlphaMax, ChungCurve.expansionAlphaMax_eq] using hk
  obtain ⟨_, hkm, hmn, hcomp, hgap, hexp⟩ :=
    ChungCurve.roundedExpansionProfile_spec n k hk'
  exact ⟨hkm, hmn, by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin] using hcomp, by
    simpa [chung8DeltaN, chung8Delta, ChungCurve.finiteExpansionMargin,
      ChungCurve.expansionMargin] using hgap, by
    simpa [chungExponent8, ProofOfSpace.chungExponent, epsilonChung,
      ChungCurve.expansionEpsilon] using hexp⟩

private theorem polygonProfile_le_public (n : ℕ) [ChungCurve.FiniteExpansionConditions n]
    (k : ℕ) (hk : chung8AlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ chung8AlphaMax) :
    ChungCurve.roundedExpansionProfile n k ≤ chung8FailureProfile n k := by
  classical
  have hadm := polygonProfile_admissible n k hk
  have hmem : ChungCurve.roundedExpansionProfile n k ∈
      (Finset.range n).filter (chung8AdmissibleFailure n k) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 hadm.2.1, hadm⟩
  rw [chung8FailureProfile]
  exact Finset.le_sup (s := (Finset.range n).filter (chung8AdmissibleFailure n k))
    (f := fun m : ℕ => m) hmem

private theorem publicFailureProfile_spec (n : ℕ) [ChungCurve.FiniteExpansionConditions n]
    (k : ℕ) (hk : chung8AlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ chung8AlphaMax) :
    0 < k ∧ k < chung8FailureProfile n k ∧ chung8FailureProfile n k < n ∧
      chung8AlphaMin ≤ 1 - (chung8FailureProfile n k : ℝ) / n ∧
      chung8DeltaN n ≤
        (chung8FailureProfile n k : ℝ) / n - (k : ℝ) / n ∧
      chungExponent8 ((k : ℝ) / n) ((chung8FailureProfile n k : ℝ) / n) ≤
        -epsilonChung * Real.log 2 := by
  classical
  have hadm := polygonProfile_admissible n k hk
  let s := (Finset.range n).filter (chung8AdmissibleFailure n k)
  have hcand : ChungCurve.roundedExpansionProfile n k ∈ s :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 hadm.2.1, hadm⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup s ⟨_, hcand⟩ id
  have hmAdm := (Finset.mem_filter.1 hm).2
  have hprofile : chung8FailureProfile n k = m := by
    change s.sup id = m
    exact hmax
  have hk' : ChungCurve.expansionAlphaMin ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ ChungCurve.expansionAlphaMax := by
    simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
      ChungCurve.filecoinAlphaMin, chung8AlphaMax, ChungCurve.expansionAlphaMax_eq] using hk
  have hk0 := (ChungCurve.roundedExpansionProfile_spec n k hk').1
  rw [hprofile]
  exact ⟨hk0, hmAdm.1, hmAdm.2.1, hmAdm.2.2.1, hmAdm.2.2.2.1, hmAdm.2.2.2.2⟩

theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (M : PebblingGame ℓ) [C : ChungExpansionConditions M.n]
    (A : Finset (ℕ × Fin M.n)) (L : ℝ)
    (hdet : ∀ P : ChungInterlayer M.n, P.Expands → M.HasUnpebbledPathTo A L P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A L) (chung8FailureBound M.n) := by
  classical
  letI : ChungCurve.FiniteExpansionConditions M.n := internalExpansionConditions M.n
  have hw := Concrete.portExpansion_whp_exponential M.n chung8AlphaMin chung8AlphaMax
    (chung8DeltaN M.n) epsilonChung (chung8FailureProfile M.n)
    C.n_pos (by norm_num [chung8AlphaMin, chung8PebblingAlphaMin]) C.delta_pos
    (publicFailureProfile_le M.n) (publicFailureProfile_spec M.n)
  rw [Concrete.HoldsWithFailureAtMost] at hw
  rw [HoldsWithFailureAtMost, probabilityOf_interlayerEquiv]
  refine hw.trans (Concrete.probabilityOf_mono _ fun P hP => ?_)
  apply hdet ((interlayerEquiv M.n).symm P)
  rw [public_profile_iff]
  simpa using hP

theorem chung8_pebbling_latency_15
    (lambda : ℝ) (M : PebblingGame 15) [H : PebblingGame.IsAdmissible M]
    [C : ChungSecurityConditions M.n lambda]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hαpi : M.αpi = (1 : ℝ) / 5)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hpi : M.pi = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hweight : (4311 : ℝ) / 5000 ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A
        ((1 : ℝ) / 5 * M.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * M.n))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  classical
  have hgeneric : HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A
        ((1 : ℝ) / 5 * M.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * M.n))
      (chung8FailureBound M.n) := by
    apply chung8_pebbling_latency_whp M A
    intro P hP
    let Pc : Concrete.PortInterlayer M.n := interlayerEquiv M.n P
    letI : ChungCurve.FiniteExpansionConditions M.n := internalExpansionConditions M.n
    have hpublic : Pc.ExpandsProfileOn chung8AlphaMin chung8AlphaMax
        (chung8FailureProfile M.n) := (public_profile_iff P).1 hP
    have hprofile : Pc.ExpandsProfileOn ChungCurve.expansionAlphaMin
        ChungCurve.expansionAlphaMax (ChungCurve.roundedExpansionProfile M.n) := by
      intro T ha hb
      have hk : chung8AlphaMin ≤ (T.card : ℝ) / M.n ∧
          (T.card : ℝ) / M.n ≤ chung8AlphaMax := by
        simpa [chung8AlphaMin, chung8PebblingAlphaMin, ChungCurve.expansionAlphaMin,
          ChungCurve.filecoinAlphaMin, chung8AlphaMax,
          ChungCurve.expansionAlphaMax_eq] using And.intro ha hb
      exact (polygonProfile_le_public M.n T.card hk).trans_lt
        (hpublic T hk.1 hk.2)
    have hPc : Pc.Expands ChungCurve.chung8Setting :=
      ChungCurve.portExpands_filecoin_of_profile M.n Pc hprofile
    let standalone : Concrete.StandaloneGraph M.n :=
      { edge := M.intra, edge_lt := fun {_ _} h => H.intra_rank h }
    let G := Concrete.portStack standalone ChungCurve.chung8Setting 15 M.αpi H.n_pos
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
      apply Concrete.portStack_depthRobust_of_nodeDR
      intro X hX
      apply H.depth_robust X
      have heq : (1 - ChungCurve.chung8Setting.pi) * (M.n : ℝ) =
          (1 - M.pi) * M.n := by
        rw [ChungCurve.chung8Setting_pi, hpi]
      rwa [heq] at hX
    have hA' : A ⊆ G.layer 0 := hA
    have hweight' : ChungCurve.chung8Setting.ζδ ≤ Concrete.Pebbling.weight M.n A := by
      simpa only [ChungCurve.chung8Setting_zetaDelta, Concrete.Pebbling.weight] using hweight
    have hpath := ChungCurve.chung8_latency_15_deterministic G pebbling H.n_pos
      hαpi hDepth A hA' hred hweight'
    rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
    refine ⟨u, a, ha, Q.nodes, Q.nonempty, ?_, Q.unpebbled', ?_, ?_, hlength⟩
    · exact Q.chain
    · rw [List.head?_eq_some_head Q.nonempty]
      exact congrArg some hfirst
    · rw [List.getLast?_eq_some_getLast Q.nonempty]
      exact congrArg some hlast
  letI : ChungCurve.ExpansionSecurityConditions M.n lambda :=
    internalSecurityConditions M.n lambda
  have hbound := ChungCurve.expansionFailureBound_le_security M.n lambda
  rw [HoldsWithFailureAtMost] at hgeneric ⊢
  refine (tsub_le_tsub_left ?_ 1).trans hgeneric
  change ChungCurve.expansionFailureBound M.n ≤ _
  exact hbound

end ProofOfSpaceStatement

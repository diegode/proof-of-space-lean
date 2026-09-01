import ProofOfSpace.ChungFilecoinExpansion
import ProofOfSpace.ChungRelative

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

noncomputable def chungExponent8 (x y : ℝ) : ℝ :=
  Real.binEntropy x + Real.binEntropy y +
    8 * (y * Real.binEntropy (x / y) - Real.binEntropy x)

noncomputable def chung8Level (x y : ℝ) : ℝ :=
  min (Real.binEntropy x) (Real.binEntropy y) / 2 ^ (23 : ℕ)

noncomputable def chung8Beta (x : ℝ) : ℝ :=
  if x = 1 then 1
  else sSup {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x y}

noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (chung8Beta ((k : ℝ) / n) * n) - 1 else 0

namespace ChungInterlayer

def Expands {n : ℕ} (P : ChungInterlayer n) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty →
    chung8FailureProfile n T.card < (P.neighborhood T).card

end ChungInterlayer

noncomputable def chung8PortHitProb (n k m : ℕ) : ℝ≥0∞ :=
  ((8 * m).descFactorial (8 * k) : ℝ≥0∞) /
    ((8 * n).descFactorial (8 * k) : ℝ≥0∞)

noncomputable def chung8FailureBound (n : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => 1 / (n : ℝ) ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1),
    (n.choose k : ℝ≥0∞) *
      ((n.choose (chung8FailureProfile n k) : ℝ≥0∞) *
        chung8PortHitProb n k (chung8FailureProfile n k))

class ChungSecurityConditions (n : ℕ) (lambda : ℝ) : Prop where
  n_pos : 0 < n
  security :
    chung8FailureBound n ≤ ENNReal.ofReal (Real.exp (-lambda * Real.log 2))

/-- A static black/red pebbling position on an `ℓ`-layer stacked graph. -/
structure PebblingGame (ℓ : ℕ) where
  n : ℕ
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (M : PebblingGame ℓ) (d : ℕ) :
    Finset (ℕ × Fin M.n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin M.n => (d, i)) else ∅

def PebblingGame.depth {ℓ : ℕ} (M : PebblingGame ℓ) (v : ℕ × Fin M.n) : ℕ := v.1

def PebblingGame.latencyLength {ℓ : ℕ} (M : PebblingGame ℓ) (σ : ℝ) (z : ℕ) : ℝ :=
  M.απ * M.n + ((z : ℝ) - 1) * (M.απ - σ) * M.n

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
    ((X.card : ℝ) ≤ (1 - M.π) * M.n) →
    ∃ p : List (Fin M.n), p ≠ [] ∧ p.IsChain M.intra ∧
      (∀ v ∈ p, v ∉ X) ∧ M.απ * M.n ≤ (p.length : ℝ)
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

def Chung8LatencyRegion (ℓ z : ℕ) (απ δ π ρ ζ σ : ℝ) : Prop :=
  σ < απ ∧
    ∀ (M : PebblingGame ℓ), M.απ = απ → M.δ = δ → M.π = π → M.ρ = ρ → M.ζ = ζ →
      PebblingGame.IsAdmissible M →
      ∀ (A : Finset (ℕ × Fin M.n)), A ⊆ M.layer 0 →
        M.ζ ≤ (A.card : ℝ) / M.n →
        ∀ P : ChungInterlayer M.n, P.Expands →
          M.HasUnpebbledPathTo A (M.latencyLength σ z) P

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

private theorem filecoinBeta_le_chung8Beta {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ChungCurve.filecoinBeta x ≤ chung8Beta x := by
  rw [chung8Beta, if_neg (ne_of_lt h1)]
  apply le_csSup
  · exact ⟨1, fun y hy ↦ hy.1.2.le⟩
  · have hxb : x < ChungCurve.filecoinBeta x :=
      ChungCurve.filecoinBeta_expands ⟨h0, h1⟩
    have hb1 : ChungCurve.filecoinBeta x < 1 := by
      have hmono := ChungCurve.filecoinBeta_strictMono h1
      simpa using hmono
    refine ⟨⟨hxb, hb1⟩, ?_⟩
    have hcert := ChungCurve.filecoinBeta_sec_lt_level h0 h1
    have hlevel : chung8Level x (ChungCurve.filecoinBeta x) ≤
        ChungCurve.chungLevel x := by
      rw [chung8Level, ChungCurve.chungLevel]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    rw [show chungExponent8 x (ChungCurve.filecoinBeta x) =
        ChungCurve.sec 8 x (ChungCurve.filecoinBeta x) by
      rw [chungExponent8, ← ChungCurve.chungExponent_eq_sec h0 hxb hb1]
      rfl]
    linarith

private theorem chung8Beta_le_one (x : ℝ) : chung8Beta x ≤ 1 := by
  classical
  rw [chung8Beta]
  split_ifs
  · exact le_rfl
  · rcases Set.eq_empty_or_nonempty
        {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x y} with he | hne
    · rw [he, Real.sSup_empty]
      norm_num
    · exact csSup_le hne fun y hy => hy.1.2.le

private theorem publicFailureProfile_le (n k : ℕ) : chung8FailureProfile n k ≤ n := by
  rw [chung8FailureProfile]
  split_ifs with hk
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hmul : chung8Beta ((k : ℝ) / n) * n ≤ n := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (chung8Beta_le_one ((k : ℝ) / n)) hnR.le
      exact (Nat.sub_le _ _).trans (Nat.ceil_le.mpr hmul)
  · exact Nat.zero_le _

private theorem public_profile_iff (P : ChungInterlayer n) (hn : 0 < n) :
    P.Expands ↔ (interlayerEquiv n P).ExpandsProfileOn (1 / (n : ℝ)) 1
      (chung8FailureProfile n) := by
  rw [ChungInterlayer.Expands, Concrete.PortInterlayer.ExpandsProfileOn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h T ha _
    have hT : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hzero
      subst T
      simp only [Finset.card_empty, Nat.cast_zero, zero_div] at ha
      have hpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
      linarith
    simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T hT
  · intro h T hT
    have hk : 1 ≤ T.card := Finset.one_le_card.mpr hT
    have ha : 1 / (n : ℝ) ≤ (T.card : ℝ) / n := by
      exact (div_le_div_iff_of_pos_right hnR).2 (by exact_mod_cast hk)
    have hb : (T.card : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]
      have hcard : T.card ≤ n := by simpa using Finset.card_le_univ T
      exact_mod_cast hcard
    simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T ha hb

/-- A functional Chung-8 profile certificate supplies operational expansion for any
setting whose expansion curve is bounded by the functional Chung threshold. -/
private theorem portExpands_of_public (P : ChungInterlayer n) (hn : 0 < n)
    (S : Setting)
    (hdom : ∀ {x t : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      0 < t → x ≤ t → S.β x ≤ chung8Beta t)
    (hP : P.Expands) : (interlayerEquiv n P).Expands S := by
  classical
  intro T x hx hxt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t : ℝ := (T.card : ℝ) / n
  have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hnR]
    exact_mod_cast hTn
  have hx0 : 0 ≤ x := S.αmin_nonneg.trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans S.αmax_le_one
  by_cases hT : T.Nonempty
  · have hk : 1 ≤ T.card := Finset.one_le_card.mpr hT
    have htpos : 0 < t := by
      dsimp [t]
      exact div_pos (by exact_mod_cast hk) hnR
    have hprofile : chung8FailureProfile n T.card <
        ((interlayerEquiv n P).neighborhood T).card := by
      simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
        ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using hP T hT
    rw [chung8FailureProfile, if_pos hTn] at hprofile
    have hceil : Nat.ceil (chung8Beta t * n) ≤
        ((interlayerEquiv n P).neighborhood T).card := by
      change Nat.ceil (chung8Beta ((T.card : ℝ) / n) * n) ≤ _
      omega
    calc
      S.β x * n ≤ chung8Beta t * n :=
        mul_le_mul_of_nonneg_right
          (hdom ⟨hx0, hx1⟩ ⟨ht0, ht1⟩ htpos hxt) hnR.le
      _ ≤ (Nat.ceil (chung8Beta t * n) : ℝ) := Nat.le_ceil _
      _ ≤ ((interlayerEquiv n P).neighborhood T).card := by exact_mod_cast hceil
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    simp only [Finset.card_empty, Nat.cast_zero, zero_div] at hxt
    have hxzero : x = 0 := le_antisymm hxt hx0
    simp [hxzero, S.β_zero]

private theorem chung8_pebbling_latency_whp_raw
    {ℓ : ℕ} (M : PebblingGame ℓ) (hn : 0 < M.n)
    (A : Finset (ℕ × Fin M.n)) (L : ℝ)
    (hdet : ∀ P : ChungInterlayer M.n, P.Expands → M.HasUnpebbledPathTo A L P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A L) (chung8FailureBound M.n) := by
  classical
  have hfail := Concrete.portExpansion_failure_le M.n (1 / (M.n : ℝ)) 1
    (chung8FailureProfile M.n)
    (one_div_pos.mpr (by exact_mod_cast hn)) (publicFailureProfile_le M.n)
  have hfail' : Concrete.probabilityOf (Concrete.PortInterlayer.uniformLaw M.n)
      (fun P => ¬ P.ExpandsProfileOn (1 / (M.n : ℝ)) 1 (chung8FailureProfile M.n)) ≤
      chung8FailureBound M.n := by
    simpa [chung8FailureBound, chung8PortHitProb, Concrete.hitProb] using hfail
  have hw := Concrete.holdsWithFailureAtMost_of_compl_le _ _ hfail'
  rw [Concrete.HoldsWithFailureAtMost] at hw
  rw [HoldsWithFailureAtMost, probabilityOf_interlayerEquiv]
  refine hw.trans (Concrete.probabilityOf_mono _ fun P hP => ?_)
  apply hdet ((interlayerEquiv M.n).symm P)
  rw [public_profile_iff _ hn]
  simpa using hP

private theorem chung8_pebbling_of_expands_whp
    {ℓ : ℕ} (lambda : ℝ) (M : PebblingGame ℓ)
    [C : ChungSecurityConditions M.n lambda]
    (A : Finset (ℕ × Fin M.n)) (L : ℝ)
    (hdet : ∀ P : ChungInterlayer M.n, P.Expands → M.HasUnpebbledPathTo A L P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A L)
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  have hgeneric := chung8_pebbling_latency_whp_raw M C.n_pos A L hdet
  rw [HoldsWithFailureAtMost] at hgeneric ⊢
  exact (tsub_le_tsub_left C.security 1).trans hgeneric

theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (lambda : ℝ) (M : PebblingGame ℓ)
    [H : PebblingGame.IsAdmissible M] [C : ChungSecurityConditions M.n lambda]
    (z : ℕ) (σ : ℝ)
    (hregion : Chung8LatencyRegion ℓ z M.απ M.δ M.π M.ρ M.ζ σ)
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hweight : M.ζ ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A (M.latencyLength σ z))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  apply chung8_pebbling_of_expands_whp lambda M A
  intro P hP
  exact hregion.2 M rfl rfl rfl rfl rfl H A hA hweight P hP

theorem chung8_pebbling_latency_15
    (lambda : ℝ) (M : PebblingGame 15) [H : PebblingGame.IsAdmissible M]
    [C : ChungSecurityConditions M.n lambda]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hαπ : M.απ = (1 : ℝ) / 5)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hπ : M.π = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hζ : M.ζ = (9 : ℝ) / 10)
    (hweight : M.ζ ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A (M.latencyLength ((74 : ℝ) / 625) 2))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  classical
  have hregion : Chung8LatencyRegion 15 2 ((1 : ℝ) / 5)
      ((189 : ℝ) / 5000) ((4 : ℝ) / 5) ((4 : ℝ) / 5) ((9 : ℝ) / 10)
      ((74 : ℝ) / 625) := by
    refine ⟨by norm_num, ?_⟩
    intro N hNαπ hNδ hNπ hNρ hNζ hN B hB hBweight P hP
    let Pc : Concrete.PortInterlayer N.n := interlayerEquiv N.n P
    have hPc : Pc.Expands ChungCurve.chung8Setting := by
      change (interlayerEquiv N.n P).Expands ChungCurve.chung8Setting
      apply portExpands_of_public P hN.n_pos ChungCurve.chung8Setting
      · intro x t _ ht htpos hxt
        change ChungCurve.filecoinBeta x ≤ chung8Beta t
        by_cases htone : t = 1
        · subst t
          calc
            ChungCurve.filecoinBeta x ≤ ChungCurve.filecoinBeta 1 :=
              ChungCurve.filecoinBeta_strictMono.monotone hxt
            _ = chung8Beta 1 := by simp [chung8Beta]
        · have htlt : t < 1 := lt_of_le_of_ne ht.2 htone
          exact (ChungCurve.filecoinBeta_strictMono.monotone hxt).trans
            (filecoinBeta_le_chung8Beta htpos htlt)
      · exact hP
    let standalone : Concrete.StandaloneGraph N.n :=
      { edge := N.intra, edge_lt := fun {_ _} h => hN.intra_rank h }
    let G := Concrete.portStack standalone ChungCurve.chung8Setting 15 N.απ hN.n_pos
      (fun _ => Pc) (fun _ _ => hPc)
    let pebbling : Concrete.Pebbling G := {
      black := N.black
      red := N.red
      black_subset := by
        intro d v hv
        exact hN.black_subset d hv
      red_subset := by
        intro d v hv
        exact hN.red_subset d hv
      black_total := by
        intro m
        simpa only [ChungCurve.chung8Setting_rho, hNρ] using hN.black_total m
      red_bound := by
        intro d
        simpa only [ChungCurve.chung8Setting_delta, hNδ] using hN.red_bound d
    }
    have hDepth : G.DepthRobust G.αpi := by
      apply Concrete.portStack_depthRobust_of_nodeDR
      intro X hX
      apply hN.depth_robust X
      simpa only [ChungCurve.chung8Setting_pi, hNπ] using hX
    -- The challenge set is only assumed to have weight `ζ`; discarding its red
    -- nodes leaves the red-free set of weight `ζ_δ = ζ - δ` that the deterministic
    -- argument starts from, using the per-layer red bound `red_bound 0`.
    have hB' : B \ N.red 0 ⊆ G.layer 0 := Finset.sdiff_subset.trans hB
    have hBred : ∀ v ∈ B \ N.red 0, v ∉ N.red 0 := fun _ hv => (Finset.mem_sdiff.mp hv).2
    have hweight' : ChungCurve.chung8Setting.ζδ ≤
        Concrete.Pebbling.weight N.n (B \ N.red 0) := by
      have hnpos : (0 : ℝ) < N.n := by exact_mod_cast hN.n_pos
      have hred0 : ((N.red 0).card : ℝ) ≤ (189 : ℝ) / 5000 * N.n := by
        simpa only [hNδ] using hN.red_bound 0
      have hcardNat : B.card ≤ (B \ N.red 0).card + (N.red 0).card :=
        (Finset.card_le_card Finset.subset_union_left).trans_eq
          (Finset.card_sdiff_add_card B (N.red 0)).symm
      have hcard : (B.card : ℝ) ≤ ((B \ N.red 0).card : ℝ) + ((N.red 0).card : ℝ) := by
        exact_mod_cast hcardNat
      rw [hNζ, le_div_iff₀ hnpos] at hBweight
      simp only [ChungCurve.chung8Setting_zetaDelta, Concrete.Pebbling.weight]
      rw [le_div_iff₀ hnpos]
      linarith
    have hGαπ : G.αpi = (1 : ℝ) / 5 := by
      change N.απ = (1 : ℝ) / 5
      exact hNαπ
    have hpath := ChungCurve.chung8_latency_15_deterministic G pebbling hN.n_pos hGαπ
      hDepth (B \ N.red 0) hB' hBred hweight'
    rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
    have hlatency : N.latencyLength ((74 : ℝ) / 625) 2 =
        (1 : ℝ) / 5 * N.n + ((1 : ℝ) / 5 - (74 : ℝ) / 625) * N.n := by
      simp only [PebblingGame.latencyLength, hNαπ]
      push_cast
      ring
    refine ⟨u, a, (Finset.mem_sdiff.mp ha).1, Q.nodes, Q.nonempty, Q.chain,
      Q.unpebbled', ?_, ?_, ?_⟩
    · rw [List.head?_eq_some_head Q.nonempty]
      exact congrArg some hfirst
    · rw [List.getLast?_eq_some_getLast Q.nonempty]
      exact congrArg some hlast
    · rw [hlatency]
      exact hlength
  apply chung8_pebbling_latency_whp lambda M 2 ((74 : ℝ) / 625) ?_ A hA hweight
  simpa only [hαπ, hδ, hπ, hρ, hζ] using hregion

end ProofOfSpaceStatement

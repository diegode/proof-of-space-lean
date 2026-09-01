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

noncomputable def chung8Level (x : ℝ) : ℝ :=
  Real.binEntropy x / 2 ^ (23 : ℕ)

noncomputable def chung8Beta (x : ℝ) : ℝ :=
  if x = 1 then 1
  else sSup {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x}

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

noncomputable def chung8LatencyThreshold (z : ℕ) : ℝ :=
  (463 : ℝ) / 774 + ((z : ℝ) - 1) * (4 - 675 / 1113 + 331 / 774) + 11600 / 1113

/-- A static black/red pebbling position on an `ℓ`-layer stacked graph. -/
structure PebblingGame (ℓ : ℕ) where
  n : ℕ
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  σ : ℝ
  ζδ : ℝ
  αg : ℝ
  αmin : ℝ
  αmax : ℝ
  mid : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

def PebblingGame.layer {ℓ : ℕ} (M : PebblingGame ℓ) (d : ℕ) :
    Finset (ℕ × Fin M.n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin M.n => (d, i)) else ∅

def PebblingGame.depth {ℓ : ℕ} (M : PebblingGame ℓ) (v : ℕ × Fin M.n) : ℕ := v.1

def PebblingGame.latencyLength {ℓ : ℕ} (M : PebblingGame ℓ) (z : ℕ) : ℝ :=
  M.απ * M.n + ((z : ℝ) - 1) * (M.απ - M.σ) * M.n

noncomputable def PebblingGame.latencyConstants {ℓ : ℕ} (M : PebblingGame ℓ) : ℕ × ℕ :=
  let gainD := fun x ↦ chung8Beta x - M.δ - x
  let betaD := fun x ↦ chung8Beta x - M.δ
  let gpi := gainD M.π
  let piBar := 1 - chung8Beta M.π
  let zetaFloor := M.ζδ - M.ρ
  let gtilde := min (gainD zetaFloor) gpi
  let sigmaHat := min M.σ (1 - chung8Beta M.σ)
  let lam := min piBar sigmaHat
  let ghat := min gpi (gainD M.σ / 2)
  let infertileCap := fun h ↦ Nat.ceil ((M.ρ - (M.ζδ - M.π)) / h)
  let blockedCap := fun g ↦ Nat.ceil (M.ρ / g) - 1
  let sCap := infertileCap gtilde + blockedCap ghat
  let growthSpan := fun x ↦ max 1 ⌊(M.π - M.σ + x) / ghat⌋₊
  let asymptoticGrowth := max 1 ((M.π - M.σ) / ghat)
  let growthPot := fun split v ↦
    (min v split - M.σ) / (2 * ghat) + (max v split - split) / ghat
  let growthConst := min asymptoticGrowth (growthPot M.mid M.π + 1)
  let h₁ := growthConst + 1
  let ledgerSlack := 2 * M.ρ / ghat
  let gmin := min ghat gtilde
  let jointSlack := 2 * M.ρ / gmin
  let searchHead := max 0 (1 + (M.π - M.ζδ) / gtilde)
  let spendCap := ⌈M.ρ / ghat⌉₊
  let growthCap := growthSpan M.ρ
  let h₀ := growthCap + 2 * spendCap
  let bMax := blockedCap (betaD M.π - lam)
  let s₀ := sCap + bMax * h₀
  let jointEntry :=
    if bMax = 0 then ⌈((ℓ : ℝ) - searchHead - jointSlack) / h₁⌉₊ else 0
  let z := max 1 (max
    ⌈((ℓ : ℝ) - sCap - ledgerSlack - bMax * h₁) / (((bMax : ℝ) + 1) * h₁)⌉₊
    (max jointEntry ((ℓ - s₀) / ((bMax + 1) * h₀) + 1)))
  (s₀, z)

noncomputable def PebblingGame.latencyOverhead {ℓ : ℕ} (M : PebblingGame ℓ) : ℕ :=
  M.latencyConstants.1

noncomputable def PebblingGame.latencyLinks {ℓ : ℕ} (M : PebblingGame ℓ) : ℕ :=
  M.latencyConstants.2

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

class ChungLatencyConditions {ℓ : ℕ} (M : PebblingGame ℓ) : Prop where
  beta_maps : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → chung8Beta x ∈ Set.Icc (0 : ℝ) 1
  beta_zero : chung8Beta 0 = 0
  beta_mono : StrictMonoOn chung8Beta (Set.Icc (0 : ℝ) 1)
  beta_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) chung8Beta
  beta_expands : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 → x < chung8Beta x
  beta_reversal : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 →
    chung8Beta (1 - chung8Beta x) = 1 - x
  alphaG_mem : M.αg ∈ Set.Ioo (0 : ℝ) 1
  alphaG_max : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → x ≠ M.αg →
    chung8Beta x - x < chung8Beta M.αg - M.αg
  delta_nonneg : 0 ≤ M.δ
  rho_pos : 0 < M.ρ
  pi_mem : M.π ∈ Set.Ioo (0 : ℝ) 1
  alphaG_lt_pi : M.αg < M.π
  gpi_pos : 0 < chung8Beta M.π - M.δ - M.π
  alphaMin_mem : M.αmin ∈ Set.Icc (0 : ℝ) M.αg
  alphaMax_mem : M.αmax ∈ Set.Icc M.αg 1
  gain_min : chung8Beta M.αmin - M.δ - M.αmin = 0
  gain_max : chung8Beta M.αmax - M.δ - M.αmax = 0
  sigma_gt : M.αmin < M.σ
  sigma_lt : M.σ < M.π
  mid_ge : M.σ ≤ M.mid
  mid_le : M.mid ≤ M.π
  mid_gain : 2 * min (chung8Beta M.π - M.δ - M.π)
      ((chung8Beta M.σ - M.δ - M.σ) / 2) ≤
    chung8Beta M.mid - M.δ - M.mid
  entry : M.αmin < M.ζδ - M.ρ
  zeta_le : M.ζδ ≤ M.αmax
  sigma_lt_alphaPi : M.σ < M.απ
  inside : M.latencyOverhead < ℓ

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

private theorem chung8Beta_eq_shifted {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    chung8Beta x = ChungCurve.shiftedBeta 8 (ChungCurve.chungLevel x) x := by
  rw [chung8Beta, if_neg (ne_of_lt h1)]
  unfold ChungCurve.shiftedBeta
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, ChungCurve.shiftedSec]
  constructor
  · rintro ⟨hy, hlt⟩
    refine ⟨hy, ?_⟩
    rw [← ChungCurve.chungExponent_eq_sec h0 hy.1 hy.2]
    simp only [chungExponent8, ProofOfSpace.chungExponent, chung8Level,
      ChungCurve.chungLevel] at hlt ⊢
    linarith
  · rintro ⟨hy, hlt⟩
    refine ⟨hy, ?_⟩
    rw [← ChungCurve.chungExponent_eq_sec h0 hy.1 hy.2] at hlt
    change ProofOfSpace.chungExponent 8 x y < -chung8Level x
    simp only [ProofOfSpace.chungExponent, chung8Level,
      ChungCurve.chungLevel] at hlt ⊢
    linarith

private theorem filecoinBeta_lt_chung8Beta {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ChungCurve.filecoinBeta x < chung8Beta x := by
  rw [chung8Beta_eq_shifted h0 h1]
  exact ChungCurve.filecoinBeta_lt_shiftedBeta_level h0 h1

private theorem chung8Beta_le_one (x : ℝ) : chung8Beta x ≤ 1 := by
  classical
  rw [chung8Beta]
  split_ifs
  · exact le_rfl
  · rcases Set.eq_empty_or_nonempty
        {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x} with he | hne
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

private theorem chung8_pebbling_latency_potential_whp
    {ℓ : ℕ} (lambda : ℝ) (M : PebblingGame ℓ)
    [H : PebblingGame.IsAdmissible M] [C : ChungSecurityConditions M.n lambda]
    (z : ℕ) (hz : 1 ≤ z)
    (hlayers : chung8LatencyThreshold z < (ℓ : ℝ))
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hσ_lt : M.σ < M.απ)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hπ : M.π = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hσ : M.σ = (74 : ℝ) / 625)
    (hζδ : M.ζδ = (4311 : ℝ) / 5000)
    (hweight : M.ζδ ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A (M.latencyLength z))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  classical
  apply chung8_pebbling_of_expands_whp lambda M A
  intro P hP
  let Pc : Concrete.PortInterlayer M.n := interlayerEquiv M.n P
  have hPc : Pc.Expands ChungCurve.chung8Setting := by
    change (interlayerEquiv M.n P).Expands ChungCurve.chung8Setting
    apply portExpands_of_public P H.n_pos ChungCurve.chung8Setting
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
          (filecoinBeta_lt_chung8Beta htpos htlt).le
    · exact hP
  let standalone : Concrete.StandaloneGraph M.n :=
    { edge := M.intra, edge_lt := fun {_ _} h => H.intra_rank h }
  let G := Concrete.portStack standalone ChungCurve.chung8Setting ℓ M.απ H.n_pos
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
        (1 - M.π) * M.n := by
      rw [ChungCurve.chung8Setting_pi, hπ]
    rwa [heq] at hX
  have hA' : A ⊆ G.layer 0 := hA
  have hweight' : ChungCurve.chung8Setting.ζδ ≤ Concrete.Pebbling.weight M.n A := by
    simpa only [ChungCurve.chung8Setting_zetaDelta, Concrete.Pebbling.weight, hζδ]
      using hweight
  have hσapi : ChungCurve.chung8Tracking.σ < G.αpi := by
    change ChungCurve.chung8Tracking.σ < M.απ
    simpa only [ChungCurve.chung8Tracking_sigma, hσ] using hσ_lt
  have hzreal : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hznonneg : 0 ≤ (z : ℝ) - 1 := sub_nonneg.mpr hzreal
  have hspan := ChungCurve.chung8_potSpan_lt
  have hcharge := ChungCurve.chung8_ledgerCharge_lt
  have hspanMul : ((z : ℝ) - 1) *
        LedgerCert.potSpan ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert ≤
      ((z : ℝ) - 1) * (4 - 675 / 1113 + 331 / 774) :=
    mul_le_mul_of_nonneg_left hspan.le hznonneg
  have hledger :
      LedgerCert.potHead ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert +
          ((z : ℝ) - 1) *
            LedgerCert.potSpan ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert +
          ChungCurve.chung8LedgerCert.lam * ChungCurve.chung8Setting.ρ /
            ChungCurve.chung8Tracking.ghat < (ℓ : ℝ) := by
    calc
      _ ≤ LedgerCert.potHead ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert +
            ((z : ℝ) - 1) * (4 - 675 / 1113 + 331 / 774) +
            ChungCurve.chung8LedgerCert.lam * ChungCurve.chung8Setting.ρ /
              ChungCurve.chung8Tracking.ghat :=
        add_le_add_left
          (add_le_add_right hspanMul
            (LedgerCert.potHead ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert)) _
      _ < LedgerCert.potHead ChungCurve.chung8RefChain ChungCurve.chung8LedgerCert +
            ((z : ℝ) - 1) * (4 - 675 / 1113 + 331 / 774) + 11600 / 1113 :=
        add_lt_add_right hcharge _
      _ = chung8LatencyThreshold z := by
        rw [ChungCurve.chung8_potHead_eq]
        rfl
      _ < (ℓ : ℝ) := hlayers
  have hpath := ProofOfSpace.latency_potential G pebbling ChungCurve.chung8Tracking
    ChungCurve.chung8LedgerCert H.n_pos hσapi hDepth ChungCurve.chung8_zeta_le
    ChungCurve.chung8_entry ChungCurve.chung8_nobreak hz hledger A hA' hred hweight'
  rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
  have hlatency : ProofOfSpace.latencyLength G.αpi ChungCurve.chung8Tracking.σ M.n z =
      M.latencyLength z := by
    change ProofOfSpace.latencyLength M.απ ChungCurve.chung8Tracking.σ M.n z =
      M.latencyLength z
    simp only [ProofOfSpace.latencyLength, PebblingGame.latencyLength,
      ChungCurve.chung8Tracking_sigma, hσ]
  refine ⟨u, a, ha, Q.nodes, Q.nonempty, ?_, Q.unpebbled', ?_, ?_, ?_⟩
  · exact Q.chain
  · rw [List.head?_eq_some_head Q.nonempty]
    exact congrArg some hfirst
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast
  · rw [← hlatency]
    exact hlength

/-- The high-probability Chung-8 specialization of the break-aware general latency
theorem. All latency parameters remain symbolic. -/
theorem chung8_pebbling_latency_whp
    {ℓ : ℕ} (lambda : ℝ) (M : PebblingGame ℓ)
    [H : PebblingGame.IsAdmissible M] [C : ChungSecurityConditions M.n lambda]
    [D : ChungLatencyConditions M]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hweight : M.ζδ ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A (M.latencyLength M.latencyLinks))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  classical
  apply chung8_pebbling_of_expands_whp lambda M A
  intro P hP
  let Pc : Concrete.PortInterlayer M.n := interlayerEquiv M.n P
  let setting : Setting := {
    β := chung8Beta
    αg := M.αg
    δ := M.δ
    pi := M.π
    ρ := M.ρ
    ζδ := M.ζδ
    αmin := M.αmin
    αmax := M.αmax
    β_maps := by intro x hx; exact D.beta_maps hx
    β_zero := D.beta_zero
    β_strictMonoOn := D.beta_mono
    β_concaveOn := D.beta_concave
    β_expands := by intro x hx; exact D.beta_expands hx
    β_reversal := by intro x hx; exact D.beta_reversal hx
    αg_mem := D.alphaG_mem
    αg_max := by intro x hx hne; exact D.alphaG_max hx hne
    δ_nonneg := D.delta_nonneg
    ρ_nonneg := D.rho_pos.le
    pi_mem := D.pi_mem
    αg_lt_pi := D.alphaG_lt_pi
    gpi_pos := D.gpi_pos
    αmin_mem := D.alphaMin_mem
    αmax_mem := D.alphaMax_mem
    gainD_αmin := D.gain_min
    gainD_αmax := D.gain_max
  }
  let tracking : Tracking setting := {
    σ := M.σ
    σ_gt := D.sigma_gt
    σ_lt := D.sigma_lt
    mid := M.mid
    mid_ge := D.mid_ge
    mid_le := D.mid_le
    mid_gain := by simpa [setting, Setting.gpi, Setting.gainD] using D.mid_gain
  }
  have hPc : Pc.Expands setting := by
    change (interlayerEquiv M.n P).Expands setting
    apply portExpands_of_public P H.n_pos setting
    · intro x t hx ht _ hxt
      change chung8Beta x ≤ chung8Beta t
      exact D.beta_mono.monotoneOn hx ht hxt
    · exact hP
  let standalone : Concrete.StandaloneGraph M.n :=
    { edge := M.intra, edge_lt := fun {_ _} h => H.intra_rank h }
  let G := Concrete.portStack standalone setting ℓ M.απ H.n_pos
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
      simpa [setting] using H.black_total m
    red_bound := by
      intro d
      simpa [setting] using H.red_bound d
  }
  let regime : GeneralRegime setting := {
    entry := D.entry
    zeta_le := D.zeta_le
  }
  have hDepth : G.DepthRobust G.αpi := by
    apply Concrete.portStack_depthRobust_of_nodeDR
    intro X hX
    apply H.depth_robust X
    simpa [setting] using hX
  have hinside : ProofOfSpace.s₀ setting tracking < ℓ := by
    change M.latencyOverhead < ℓ
    exact D.inside
  have hpath := ProofOfSpace.latency_general G pebbling tracking regime H.n_pos D.rho_pos
    D.sigma_lt_alphaPi hDepth hinside A hA hred hweight
  rcases hpath with ⟨u, a, ha, Q, hfirst, hlast, hlength⟩
  have hlinks : ProofOfSpace.zMin setting tracking ℓ = M.latencyLinks := by rfl
  have hlatency : ProofOfSpace.latencyLength G.αpi tracking.σ M.n
      (ProofOfSpace.zMin setting tracking ℓ) = M.latencyLength M.latencyLinks := by
    rw [hlinks]
    rfl
  refine ⟨u, a, ha, Q.nodes, Q.nonempty, Q.chain, Q.unpebbled', ?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head Q.nonempty]
    exact congrArg some hfirst
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast
  · rw [← hlatency]
    exact hlength

theorem chung8_pebbling_latency_15
    (lambda : ℝ) (M : PebblingGame 15) [H : PebblingGame.IsAdmissible M]
    [C : ChungSecurityConditions M.n lambda]
    (A : Finset (ℕ × Fin M.n)) (hA : A ⊆ M.layer 0)
    (hred : ∀ v ∈ A, v ∉ M.red 0)
    (hαπ : M.απ = (1 : ℝ) / 5)
    (hδ : M.δ = (189 : ℝ) / 5000)
    (hπ : M.π = (4 : ℝ) / 5)
    (hρ : M.ρ = (4 : ℝ) / 5)
    (hσ : M.σ = (74 : ℝ) / 625)
    (hζδ : M.ζδ = (4311 : ℝ) / 5000)
    (hweight : M.ζδ ≤ (A.card : ℝ) / M.n) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw M.n)
      (M.HasUnpebbledPathTo A (M.latencyLength 2))
      (ENNReal.ofReal (Real.exp (-lambda * Real.log 2))) := by
  apply chung8_pebbling_latency_potential_whp lambda M 2 (by norm_num)
    (by norm_num [chung8LatencyThreshold]) A hA hred
  · rw [hσ, hαπ]
    norm_num
  · exact hδ
  · exact hπ
  · exact hρ
  · exact hσ
  · exact hζδ
  · exact hweight

end ProofOfSpaceStatement

import ProofOfSpace.ChungFilecoinExpansion
import ProofOfSpace.ChungFilecoinGeneral
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

/-- Chung-8 expansion demanded only of source sets whose density lies in `[a, b]`. -/
def ExpandsOn {n : ℕ} (P : ChungInterlayer n) (a b : ℝ) : Prop :=
  ∀ T : Finset (Fin n), a ≤ (T.card : ℝ) / n → (T.card : ℝ) / n ≤ b →
    chung8FailureProfile n T.card < (P.neighborhood T).card

end ChungInterlayer

noncomputable def chung8PortHitProb (n k m : ℕ) : ℝ≥0∞ :=
  ((8 * m).descFactorial (8 * k) : ℝ≥0∞) /
    ((8 * n).descFactorial (8 * k) : ℝ≥0∞)

noncomputable def chung8FailureBound (n : ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b),
    (n.choose k : ℝ≥0∞) *
      ((n.choose (chung8FailureProfile n k) : ℝ≥0∞) *
        chung8PortHitProb n k (chung8FailureProfile n k))

class ChungSecurityConditions (n : ℕ) (lambda : ℕ) (a b : ℝ) : Prop where
  n_pos : 0 < n
  a_pos : 0 < a
  security : chung8FailureBound n a b ≤ (2 : ℝ≥0∞)⁻¹ ^ lambda

/-- A static black/red pebbling position on an `ℓ`-layer stacked graph of width `n`. -/
structure PebblingGame (ℓ n : ℕ) where
  απ : ℝ
  δ : ℝ
  π : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

variable {ℓ n : ℕ}

def PebblingGame.layer (_M : PebblingGame ℓ n) (d : ℕ) : Finset (ℕ × Fin n) :=
  if d < ℓ then Finset.univ.image (fun i : Fin n => (d, i)) else ∅

def PebblingGame.depth (_M : PebblingGame ℓ n) (v : ℕ × Fin n) : ℕ := v.1

def PebblingGame.latencyLength (M : PebblingGame ℓ n) (σ : ℝ) (z : ℕ) : ℝ :=
  M.απ * n + ((z : ℝ) - 1) * (M.απ - σ) * n

def PebblingGame.intraEdge (M : PebblingGame ℓ n) (d : ℕ)
    (u v : ℕ × Fin n) : Prop :=
  u.1 = d ∧ v.1 = d ∧ d < ℓ ∧ M.intra u.2 v.2

def PebblingGame.interEdge (_M : PebblingGame ℓ n)
    (P : ChungInterlayer n) (d : ℕ) (u v : ℕ × Fin n) : Prop :=
  u.1 = d + 1 ∧ v.1 = d ∧ d + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin n)), (P.perm q).2 = u.2

def PebblingGame.edge (M : PebblingGame ℓ n) (P : ChungInterlayer n)
    (u v : ℕ × Fin n) : Prop :=
  (∃ d, M.intraEdge d u v) ∨ (∃ d, M.interEdge P d u v)

/-- Structural graph assumptions and pebble-budget constraints for an admissible game. -/
class PebblingGame.IsAdmissible (M : PebblingGame ℓ n) : Prop where
  intra_rank : ∀ {u v}, M.intra u v → u.val < v.val
  depth_robust : ∀ X : Finset (Fin n),
    ((X.card : ℝ) ≤ (1 - M.π) * n) →
    ∃ p : List (Fin n), p ≠ [] ∧ p.IsChain M.intra ∧
      (∀ v ∈ p, v ∉ X) ∧ M.απ * n ≤ (p.length : ℝ)
  black_subset : ∀ d, M.black d ⊆ M.layer d
  red_subset : ∀ d, M.red d ⊆ M.layer d
  black_total : ∀ m,
    ∑ d ∈ Finset.range m, ((M.black d).card : ℝ) / n ≤ M.ρ
  red_bound : ∀ d, ((M.red d).card : ℝ) ≤ M.δ * n
  n_pos : 0 < n

/-- The game has an unpebbled directed path of length at least `L` ending in `A`. -/
def PebblingGame.HasUnpebbledPathTo (M : PebblingGame ℓ n)
    (A : Finset (ℕ × Fin n))
    (L : ℝ) (P : ChungInterlayer n) : Prop :=
  ∃ a ∈ A, ∃ Q : List (ℕ × Fin n),
    Q ≠ [] ∧ Q.IsChain (M.edge P) ∧
    (∀ v ∈ Q, v ∉ M.black (M.depth v) ∧ v ∉ M.red (M.depth v)) ∧
    Q.getLast? = some a ∧ L ≤ (Q.length : ℝ)

def PebblingGame.LatencyEvent (ℓ n z : ℕ) (απ δ π ρ ζ σ : ℝ)
    (P : ChungInterlayer n) : Prop :=
  ∀ M : PebblingGame ℓ n, M.απ = απ → M.δ = δ → M.π = π → M.ρ = ρ → M.ζ = ζ →
    PebblingGame.IsAdmissible M →
    ∀ A : Finset (ℕ × Fin n), A ⊆ M.layer 0 → ζ ≤ (A.card : ℝ) / n →
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

private theorem public_profile_iff (P : ChungInterlayer n) (a b : ℝ) :
    P.ExpandsOn a b ↔ (interlayerEquiv n P).ExpandsProfileOn a b
      (chung8FailureProfile n) := by
  rw [ChungInterlayer.ExpandsOn, Concrete.PortInterlayer.ExpandsProfileOn]
  constructor
  · intro h T ha hb
    simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T ha hb
  · intro h T ha hb
    simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using h T ha hb

private theorem neighborhood_mono {n : ℕ} (P : Concrete.PortInterlayer n)
    {T T' : Finset (Fin n)} (h : T' ⊆ T) :
    P.neighborhood T' ⊆ P.neighborhood T := by
  intro v hv
  rw [Concrete.PortInterlayer.neighborhood, Finset.mem_image] at hv ⊢
  obtain ⟨q, hq, hqv⟩ := hv
  refine ⟨q, ?_, hqv⟩
  rw [Concrete.PortInterlayer.ports, Finset.mem_product] at hq ⊢
  exact ⟨hq.1, h hq.2⟩

/-- A functional Chung-8 profile certificate supplies operational expansion for any
setting whose expansion curve is bounded by the functional Chung threshold.  Expansion
is only assumed on `[a, b]`; a source set denser than `b` is handled by expanding one
of its subsets of the queried density, which the neighbourhood only shrinks. -/
private theorem portExpands_of_public (P : ChungInterlayer n) (hn : 0 < n)
    (S : Setting) (a b : ℝ) (ha : a ≤ S.αmin) (hb : S.αmax + 1 / n ≤ b)
    (hdom : ∀ {x t : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      0 < t → x ≤ t → S.β x ≤ chung8Beta t)
    (hP : P.ExpandsOn a b) : (interlayerEquiv n P).Expands S := by
  classical
  intro T x hx hxt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ x := S.αmin_nonneg.trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans S.αmax_le_one
  have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
  rcases eq_or_lt_of_le hx0 with hxz | hxpos
  · simp [← hxz, S.β_zero]
  -- A subset of `T` whose density is the queried `x`, rounded up.
  have hxT : x * n ≤ (T.card : ℝ) := by
    rw [le_div_iff₀ hnR] at hxt
    exact hxt
  have hkT : ⌈x * (n : ℝ)⌉₊ ≤ T.card := Nat.ceil_le.mpr hxT
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hkT
  have hUn : U.card ≤ n := hUcard ▸ hkT.trans hTn
  have hxU : x * n ≤ (U.card : ℝ) := by
    rw [hUcard]
    exact Nat.le_ceil _
  have hUx : x ≤ (U.card : ℝ) / n := by rw [le_div_iff₀ hnR]; exact hxU
  have hUpos : 0 < ((U.card : ℝ) / n) := lt_of_lt_of_le hxpos hUx
  have hU1 : ((U.card : ℝ) / n) ≤ 1 := by
    rw [div_le_one hnR]; exact_mod_cast hUn
  have hUa : a ≤ (U.card : ℝ) / n := ha.trans (hx.1.trans hUx)
  have hUb : (U.card : ℝ) / n ≤ b := by
    have hceil : ((U.card : ℝ)) ≤ x * n + 1 := by
      rw [hUcard]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    rw [div_le_iff₀ hnR]
    have hxmax : x ≤ S.αmax := hx.2
    have : (1 : ℝ) / n * n = 1 := by field_simp
    nlinarith [hb, hceil, hxmax, hnR]
  have hprofile : chung8FailureProfile n U.card <
      ((interlayerEquiv n P).neighborhood U).card := by
    simpa [ChungInterlayer.neighborhood, Concrete.PortInterlayer.neighborhood,
      ChungInterlayer.ports, Concrete.PortInterlayer.ports, interlayerEquiv] using
      hP U hUa hUb
  rw [chung8FailureProfile, if_pos hUn] at hprofile
  have hceilU : Nat.ceil (chung8Beta ((U.card : ℝ) / n) * n) ≤
      ((interlayerEquiv n P).neighborhood U).card := by omega
  have hmono : ((interlayerEquiv n P).neighborhood U).card ≤
      ((interlayerEquiv n P).neighborhood T).card :=
    Finset.card_le_card (neighborhood_mono _ hUT)
  calc
    S.β x * n ≤ chung8Beta ((U.card : ℝ) / n) * n :=
      mul_le_mul_of_nonneg_right
        (hdom ⟨hx0, hx1⟩ ⟨hUpos.le, hU1⟩ hUpos hUx) hnR.le
    _ ≤ (Nat.ceil (chung8Beta ((U.card : ℝ) / n) * n) : ℝ) := Nat.le_ceil _
    _ ≤ (((interlayerEquiv n P).neighborhood U).card : ℝ) := by exact_mod_cast hceilU
    _ ≤ (((interlayerEquiv n P).neighborhood T).card : ℝ) := by exact_mod_cast hmono

private theorem probabilityOf_mono {A : Type*} (p : PMF A) {Q R : A → Prop}
    (h : ∀ x, Q x → R x) : probabilityOf p Q ≤ probabilityOf p R := by
  classical
  unfold probabilityOf
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hQ : Q x
  · rw [if_pos hQ, if_pos (h x hQ)]
  · rw [if_neg hQ]
    exact zero_le

/-- Every event implied by Chung-8 expansion on `[a, b]` fails only where the exact
port-model union bound over that range does. -/
private theorem chung8_whp_raw (a b : ℝ) (ha : 0 < a)
    (Q : ChungInterlayer n → Prop)
    (hdet : ∀ P : ChungInterlayer n, P.ExpandsOn a b → Q P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n) Q
      (chung8FailureBound n a b) := by
  classical
  have hfail := Concrete.portExpansion_failure_le n a b (chung8FailureProfile n) ha
    (publicFailureProfile_le n)
  have hfail' : Concrete.probabilityOf (Concrete.PortInterlayer.uniformLaw n)
      (fun P => ¬ P.ExpandsProfileOn a b (chung8FailureProfile n)) ≤
      chung8FailureBound n a b := by
    simpa [chung8FailureBound, chung8PortHitProb, Concrete.hitProb] using hfail
  have hw := Concrete.holdsWithFailureAtMost_of_compl_le _ _ hfail'
  rw [Concrete.HoldsWithFailureAtMost] at hw
  rw [HoldsWithFailureAtMost, probabilityOf_interlayerEquiv]
  refine hw.trans (Concrete.probabilityOf_mono _ fun P hP => ?_)
  apply hdet ((interlayerEquiv n).symm P)
  rw [public_profile_iff _ a b]
  simpa using hP

private theorem chung8_of_expands_whp (lambda : ℕ) (a b : ℝ)
    [C : ChungSecurityConditions n lambda a b]
    (Q : ChungInterlayer n → Prop)
    (hdet : ∀ P : ChungInterlayer n, P.ExpandsOn a b → Q P) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n) Q
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  have hgeneric := chung8_whp_raw a b C.a_pos Q hdet
  rw [HoldsWithFailureAtMost] at hgeneric ⊢
  exact (tsub_le_tsub_left C.security 1).trans hgeneric

/-- **The Chung-8 latency theorem, over the parameter window the profile is certified
on.**  Its proof is the whole argument: the port-model union bound, the transfer of the
public expansion profile to the deterministic setting, the layered-graph bridge, the
removal of the red pebbles from the challenge set, and the potential ledger at the
symbolic budget, challenge weight and source weight. -/
theorem chung8_pebbling_latency_whp
    {ℓ n : ℕ} (lambda : ℕ) (a b : ℝ) [ChungSecurityConditions n lambda a b]
    (hn : 1000 ≤ n) (ha : a ≤ 1 / 100) (hb : 24 / 25 ≤ b)
    (απ δ π ρ ζ σ : ℝ) (z : ℕ) (hz : 1 ≤ z)
    (hδ : δ ≤ 189 / 5000) (hπ : π ≤ 4 / 5)
    (hζ : 9 / 10 ≤ ζ) (hζtop : ζ ≤ 49 / 50)
    (hρ : 0 ≤ ρ) (hρtop : ρ ≤ 4 / 5)
    (hentry : 5089 / 100000 + ρ < ζ - 189 / 5000)
    (hσ : 74 / 625 ≤ σ) (hσtop : σ ≤ 3 / 5) (hσαπ : σ < απ)
    (hlevels : 3 / 5 + ((z : ℝ) - 1) * (1911 / 500) + 1187 / 100 * ρ < (ℓ : ℝ)) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n z απ δ π ρ ζ σ)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  classical
  refine chung8_of_expands_whp lambda a b _ ?_
  intro P hP N hNαπ hNδ hNπ hNρ hNζ hN B hB hBweight
  have hnR : (0 : ℝ) < n := by exact_mod_cast hN.n_pos
  have hn1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let Pc : Concrete.PortInterlayer n := interlayerEquiv n P
  let S := ChungCurve.chung8SettingAt ρ (ζ - 189 / 5000) hρ
  have hamin : a ≤ S.αmin := by
    refine ha.trans ?_
    change (1 : ℝ) / 100 ≤ ChungCurve.filecoinAlphaMin
    rw [ChungCurve.filecoinAlphaMin]; norm_num
  have hamax : S.αmax + 1 / (n : ℝ) ≤ b := by
    have h1 : (1 : ℝ) / n ≤ 1 / 1000 :=
      one_div_le_one_div_of_le (by norm_num) hn1000
    have h2 : S.αmax = (14155 : ℝ) / 14911 := by
      change ChungCurve.filecoinAlphaMax = _
      rw [ChungCurve.filecoinAlphaMax]
    rw [h2]
    linarith
  have hPc : Pc.Expands S := by
    apply portExpands_of_public P hN.n_pos S a b hamin hamax
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
  let standalone : Concrete.StandaloneGraph n :=
    { edge := N.intra, edge_lt := fun {_ _} h => hN.intra_rank h }
  let G := Concrete.portStack standalone S ℓ N.απ hN.n_pos (fun _ => Pc) (fun _ _ => hPc)
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
      have h := hN.black_total m
      rw [hNρ] at h
      exact h
    red_bound := by
      intro d
      have h := hN.red_bound d
      rw [hNδ] at h
      have hmono : δ * (n : ℝ) ≤ 189 / 5000 * n :=
        mul_le_mul_of_nonneg_right hδ hnR.le
      exact h.trans hmono
  }
  have hDepth : G.DepthRobust G.αpi := by
    apply Concrete.portStack_depthRobust_of_nodeDR
    intro X hX
    have hX' : ((X.card : ℝ)) ≤ (1 - N.π) * n := by
      have hpi : ((X.card : ℝ)) ≤ (1 - (4 : ℝ) / 5) * n := hX
      have hmono : (1 - (4 : ℝ) / 5) * n ≤ (1 - π) * n := by nlinarith
      rw [hNπ]
      linarith
    exact hN.depth_robust X hX'
  -- The challenge set has weight `ζ`; discarding its red nodes leaves the red-free set
  -- of weight `ζ - δ ≥ ζ_δ` the deterministic argument starts from.
  have hB' : B \ N.red 0 ⊆ G.layer 0 := Finset.sdiff_subset.trans hB
  have hBred : ∀ v ∈ B \ N.red 0, v ∉ N.red 0 := fun _ hv => (Finset.mem_sdiff.mp hv).2
  have hweight' : ζ - 189 / 5000 ≤ Concrete.Pebbling.weight n (B \ N.red 0) := by
    have hred0 : ((N.red 0).card : ℝ) ≤ 189 / 5000 * n := by
      have h := hN.red_bound 0
      rw [hNδ] at h
      exact h.trans (mul_le_mul_of_nonneg_right hδ hnR.le)
    have hcardNat : B.card ≤ (B \ N.red 0).card + (N.red 0).card :=
      (Finset.card_le_card Finset.subset_union_left).trans_eq
        (Finset.card_sdiff_add_card B (N.red 0)).symm
    have hcard : (B.card : ℝ) ≤ ((B \ N.red 0).card : ℝ) + ((N.red 0).card : ℝ) := by
      exact_mod_cast hcardNat
    rw [le_div_iff₀ hnR] at hBweight
    simp only [Concrete.Pebbling.weight]
    rw [le_div_iff₀ hnR]
    linarith
  have hσapi : σ < G.αpi := by
    change σ < N.απ
    rw [hNαπ]; exact hσαπ
  have hpath := ChungCurve.chung8_latency_window (ρ := ρ) (ζδ := ζ - 189 / 5000)
    (σ := σ) hρ hρtop (by linarith) (by linarith) hentry hσ hσtop hz hlevels G pebbling
    hN.n_pos hσapi hDepth (B \ N.red 0) hB' hBred hweight'
  rcases hpath with ⟨u, v, hv, Q, hfirst, hlast, hlength⟩
  refine ⟨v, (Finset.mem_sdiff.mp hv).1, Q.nodes, Q.nonempty, Q.chain,
    Q.unpebbled', ?_, ?_⟩
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast
  · have hlat : N.latencyLength σ z = ProofOfSpace.latencyLength G.αpi σ n z := by
      change N.απ * n + ((z : ℝ) - 1) * (N.απ - σ) * n = _
      simp only [ProofOfSpace.latencyLength]
      rfl
    rw [hlat]
    exact hlength

/-- **The 14-layer Filecoin latency lower bound** at `lambda` bits of security: an
unpebbled path of length `0.2816 n`.  It is the point
`(απ, δ, π, ρ, ζ, σ, z, ℓ) = (0.2, 0.0378, 0.8, 0.8, 0.9, 0.1184, 2, 14)` of
`chung8_pebbling_latency_whp`, whose level condition reads `0.6 + 3.822 + 9.496 < 14`. -/
theorem chung8_pebbling_latency_14
    {n : ℕ} (lambda : ℕ) (hn : 1000 ≤ n)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun P : ChungInterlayer n =>
        ∀ M : PebblingGame 14 n,
          M.απ = (1 : ℝ) / 5 → M.δ = (189 : ℝ) / 5000 → M.π = (4 : ℝ) / 5 →
          M.ρ = (4 : ℝ) / 5 → M.ζ = (9 : ℝ) / 10 →
          PebblingGame.IsAdmissible M →
          ∀ A : Finset (ℕ × Fin n), A ⊆ M.layer 0 →
            (9 : ℝ) / 10 ≤ (A.card : ℝ) / n →
              M.HasUnpebbledPathTo A ((176 : ℝ) / 625 * n) P)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  have hmain := chung8_pebbling_latency_whp (ℓ := 14) (n := n) lambda (1 / 100) (24 / 25)
    hn le_rfl le_rfl ((1 : ℝ) / 5) ((189 : ℝ) / 5000) ((4 : ℝ) / 5) ((4 : ℝ) / 5)
    ((9 : ℝ) / 10) ((74 : ℝ) / 625) 2 (by norm_num) le_rfl le_rfl le_rfl (by norm_num)
    (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by push_cast; norm_num)
  rw [HoldsWithFailureAtMost] at hmain ⊢
  refine hmain.trans (probabilityOf_mono _ ?_)
  intro P hev M hαπ hδ hπ hρ hζ hAdm A hA hweight
  have hlen : M.latencyLength ((74 : ℝ) / 625) 2 = (176 : ℝ) / 625 * n := by
    simp only [PebblingGame.latencyLength, hαπ]
    push_cast
    ring
  rw [← hlen]
  exact hev M hαπ hδ hπ hρ hζ hAdm A hA hweight

end ProofOfSpaceStatement

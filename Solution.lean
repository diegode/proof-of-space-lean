import ProofOfSpace.ChungFilecoinExpansion
import ProofOfSpace.ChungFilecoinGeneral
import ProofOfSpace.ChungRelative
import ProofOfSpace.FullSourcesFilecoin
import ProofOfSpace.ChungFilecoinMirror

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

/-! ### Expansion profiles

The deterministic argument runs on any expansion profile with the properties below.  They
are the expansion calculus of the analysis: the profile maps the unit interval to itself,
fixes `0`, is strictly increasing, concave and expanding, satisfies Chung's reversal law,
has a unique gain maximiser `αg`, and has the two zeros of the adjusted gain
`gain_δ(x) = β(x) - δ - x` as `αmin` and `αmax`.  Only `le_chung8` mentions the sampled
wiring: it is what makes the profile realizable by the uniform port permutation, and it
is why the degree-eight failure bound pays for the event. -/
structure ExpansionProfile where
  /-- The expansion function of the vertical edges. -/
  β : ℝ → ℝ
  /-- The red-pebble fraction the profile is certified at. -/
  δ : ℝ
  /-- The intra-layer robustness threshold. -/
  π : ℝ
  /-- The unique maximiser of the gain `β - id`. -/
  αg : ℝ
  /-- The low zero of the adjusted gain. -/
  αmin : ℝ
  /-- The high zero of the adjusted gain. -/
  αmax : ℝ
  β_maps : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → β x ∈ Set.Icc (0 : ℝ) 1
  β_zero : β 0 = 0
  β_strictMonoOn : StrictMonoOn β (Set.Icc (0 : ℝ) 1)
  β_concaveOn : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) β
  β_expands : ∀ ⦃x⦄, x ∈ Set.Ioo (0 : ℝ) 1 → x < β x
  β_reversal : ∀ ⦃x⦄, x ∈ Set.Ioo (0 : ℝ) 1 → β (1 - β x) = 1 - x
  αg_mem : αg ∈ Set.Ioo (0 : ℝ) 1
  αg_max : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → x ≠ αg → β x - x < β αg - αg
  δ_nonneg : 0 ≤ δ
  π_mem : π ∈ Set.Ioo (0 : ℝ) 1
  αg_lt_π : αg < π
  /-- `δ` is small enough that the fertile gain `g_π` is positive. -/
  gpi_pos : 0 < β π - δ - π
  αmin_mem : αmin ∈ Set.Icc (0 : ℝ) αg
  αmax_mem : αmax ∈ Set.Icc αg 1
  gainD_αmin : β αmin - δ - αmin = 0
  gainD_αmax : β αmax - δ - αmax = 0
  /-- The sampled degree-eight wiring realizes the profile. -/
  le_chung8 : ∀ ⦃x⦄, x ∈ Set.Icc (0 : ℝ) 1 → β x ≤ chung8Beta x

namespace ExpansionProfile

variable (E : ExpansionProfile)

/-- `gain_δ(x) = β(x) - δ - x`. -/
def gainD (x : ℝ) : ℝ := E.β x - E.δ - x

/-- `β_δ(x) = β(x) - δ`, one level of growth against a full red layer. -/
def betaD (x : ℝ) : ℝ := E.β x - E.δ

/-- `g_π = gain_δ(π)`, the gain at the fertility threshold. -/
def gpi : ℝ := E.gainD E.π

/-- `π̄ = 1 - β(π)`, the lower member of the equal-gain mirror pair. -/
def piBar : ℝ := 1 - E.β E.π

/-- `π̂ = min{π̄, σ, 1 - β(σ)}`: the weight a tracked source cannot be pushed below. -/
noncomputable def floor (σ : ℝ) : ℝ := min E.piBar (min σ (1 - E.β σ))

/-- `ĝ = min{g_π, gain_δ(σ)/2}`: the gain the tracking argument runs at. -/
noncomputable def trackingGain (σ : ℝ) : ℝ := min E.gpi (E.gainD σ / 2)

end ExpansionProfile

/-! ### Certified level budgets

A level budget is a reference trajectory for the profile together with the certificate
that prices one step of the search along it.  The trajectory is a finite increasing
sequence from the tracking floor to the fertility threshold, each step within one free
level of growth and each bucket at least `ĝ` wide; `refPotOf` interpolates it, measuring
in levels how far a weight has climbed.  The certificate turns that into the three prices
the layer count is spent on. -/

/-- The piecewise-linear interpolation of `x k ↦ k`: how many free levels of the
trajectory the weight `v` has already covered. -/
noncomputable def refPotOf (m : ℕ) (x : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, max 0 (min 1 ((v - x k) / (x (k + 1) - x k)))

/-- A **certified level budget** for the profile `E` at source weight `σ`, valid for black
weights up to `ρmax`. -/
structure LevelBudget (E : ExpansionProfile) (σ : ℝ) where
  /-- The largest black weight the blocked-range clauses are certified for. -/
  ρmax : ℝ
  σ_gt : E.αmin < σ
  σ_lt : σ < E.π
  /-- A doubled-gain midpoint: `gain_δ ≥ 2 ĝ` still holds there, and concavity spreads it
  over `[σ, mid]`. -/
  mid : ℝ
  mid_ge : σ ≤ mid
  mid_le : mid ≤ E.π
  mid_gain : 2 * E.trackingGain σ ≤ E.gainD mid
  /-- The number of buckets of the reference trajectory. -/
  m : ℕ
  /-- Its points. -/
  x : ℕ → ℝ
  m_pos : 0 < m
  base : x 0 ≤ E.floor σ
  width : ∀ k, k < m → E.trackingGain σ ≤ x (k + 1) - x k
  step : ∀ k, k < m → x (k + 1) ≤ E.betaD (x k)
  mem : ∀ k, k ≤ m → x k ∈ Set.Icc (0 : ℝ) 1
  top : E.π ≤ x m
  /-- Levels charged per unit of black weight, in units of `1/ĝ`. -/
  lam : ℝ
  /-- Bound on the potential a subfertile weight is short of saturation. -/
  loss : ℝ
  /-- The expandability slack the search runs at. -/
  cs : ℝ
  /-- The width of the top bucket. -/
  wtop : ℝ
  /-- The top-bucket chord slope of `β_δ`, per unit of potential. -/
  kappa : ℝ
  /-- Slope and offset of the blocked-range drop. -/
  a2 : ℝ
  b2 : ℝ
  one_le_lam : 1 ≤ lam
  loss_nonneg : 0 ≤ loss
  one_le_cs : 1 ≤ cs
  wtop_pos : 0 < wtop
  kappa_nonneg : 0 ≤ kappa
  loss_ge : ∀ v, x 0 ≤ v → v ≤ E.π → refPotOf m x v - ((m : ℝ) - 1) ≤ loss
  topLip : ∀ u v : ℝ, x m ≤ u → v ≤ u →
    refPotOf m x u - refPotOf m x v ≤ (u - v) / wtop
  chord : ∀ v : ℝ, x (m - 1) ≤ v → v ≤ E.π →
    x m + kappa * (refPotOf m x v - ((m : ℝ) - 1)) ≤ E.betaD v
  ghat_le_lam_wtop : E.trackingGain σ ≤ lam * wtop
  inf_rate : ∀ θ s : ℝ, 0 ≤ θ → θ ≤ loss → 0 ≤ s →
    (x m - E.π) + kappa * θ ≤ s → θ + (s - kappa * θ) / wtop ≤ lam * s / E.trackingGain σ
  blockDrop : ∀ y : ℝ, (1 + cs) * E.trackingGain σ ≤ y → y ≤ ρmax →
    ((m : ℝ)) - refPotOf m x (E.betaD E.π - y) ≤ a2 * y + b2
  blockDrop_one : ∀ y : ℝ, (1 + cs) * E.trackingGain σ ≤ y → 1 ≤ a2 * y + b2
  blk_rate : ∀ y w : ℝ, (1 + cs) * E.trackingGain σ ≤ y → y ≤ ρmax → 0 ≤ w →
    (y / E.trackingGain σ - cs + 1) + (a2 * y + b2 - 1) + w / E.trackingGain σ
      ≤ -loss + lam * (y + w) / E.trackingGain σ

namespace LevelBudget

variable {E : ExpansionProfile} {σ : ℝ} (L : LevelBudget E σ)

/-- What the initial search costs, in layers, at red-free challenge weight `w`. -/
noncomputable def searchCost (w : ℝ) : ℝ := ((L.m : ℝ) - refPotOf L.m L.x w) + L.loss

/-- What one further chain link costs, in layers. -/
noncomputable def linkCost : ℝ := ((L.m : ℝ) - refPotOf L.m L.x σ) + L.loss

/-- What one unit of black-pebble weight costs, in layers. -/
noncomputable def chargeRate : ℝ := L.lam / E.trackingGain σ

end LevelBudget

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
    (E : ExpansionProfile) (σ : ℝ) (L : LevelBudget E σ)
    (απ δ π ρ ζ : ℝ) (z : ℕ) (hz : 1 ≤ z)
    (ha : a ≤ E.αmin) (hb : E.αmax + 1 / n ≤ b)
    (hδ : δ ≤ E.δ) (hπ : π ≤ E.π)
    (hρ : 0 ≤ ρ) (hρtop : ρ ≤ L.ρmax)
    (hentry : E.piBar + ρ < ζ - δ) (hζ : ζ - δ ≤ E.αmax)
    (hnobreak : ρ < E.betaD E.π - E.floor σ)
    (hslack : E.floor σ + (L.cs - 1) * E.trackingGain σ ≤ σ)
    (hσαπ : σ < απ)
    (hlevels : L.searchCost (ζ - δ) + ((z : ℝ) - 1) * L.linkCost
      + L.chargeRate * ρ < (ℓ : ℝ)) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n z απ δ π ρ ζ σ)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  classical
  refine chung8_of_expands_whp lambda a b _ ?_
  intro P hP N hNαπ hNδ hNπ hNρ hNζ hN B hB hBweight
  have hnR : (0 : ℝ) < n := by exact_mod_cast hN.n_pos
  let Pc : Concrete.PortInterlayer n := interlayerEquiv n P
  -- The public profile is the deterministic `Setting`, with the game's budget and its
  -- red-free challenge weight.
  let S : Setting :=
    { β := E.β, αg := E.αg, δ := E.δ, pi := E.π, ρ := ρ, ζδ := ζ - δ
      αmin := E.αmin, αmax := E.αmax
      β_maps := E.β_maps, β_zero := E.β_zero, β_strictMonoOn := E.β_strictMonoOn
      β_concaveOn := E.β_concaveOn, β_expands := E.β_expands, β_reversal := E.β_reversal
      αg_mem := E.αg_mem, αg_max := E.αg_max, δ_nonneg := E.δ_nonneg, ρ_nonneg := hρ
      pi_mem := E.π_mem, αg_lt_pi := E.αg_lt_π, gpi_pos := E.gpi_pos
      αmin_mem := E.αmin_mem, αmax_mem := E.αmax_mem
      gainD_αmin := E.gainD_αmin, gainD_αmax := E.gainD_αmax }
  let T : Tracking S :=
    { σ := σ, σ_gt := L.σ_gt, σ_lt := L.σ_lt, mid := L.mid, mid_ge := L.mid_ge
      mid_le := L.mid_le, mid_gain := L.mid_gain }
  let C : RefChain S T :=
    { m := L.m, x := L.x, m_pos := L.m_pos, base := L.base, width := L.width
      step := L.step, mem := L.mem, top := L.top }
  let Cert : LedgerCert S T C :=
    { lam := L.lam, loss := L.loss, cs := L.cs, wtop := L.wtop, kappa := L.kappa
      a2 := L.a2, b2 := L.b2
      one_le_lam := L.one_le_lam, loss_nonneg := L.loss_nonneg, one_le_cs := L.one_le_cs
      wtop_pos := L.wtop_pos, kappa_nonneg := L.kappa_nonneg
      loss_ge := L.loss_ge, topLip := L.topLip, chord := L.chord
      ghat_le_lam_wtop := L.ghat_le_lam_wtop, inf_rate := L.inf_rate
      blockDrop := fun y hy hyρ => L.blockDrop y hy (le_trans hyρ hρtop)
      blockDrop_one := L.blockDrop_one
      blk_rate := fun y w hy hyρ hw => L.blk_rate y w hy (le_trans hyρ hρtop) hw }
  have hPc : Pc.Expands S := by
    apply portExpands_of_public P hN.n_pos S a b ha hb
    · intro x t hx ht _ hxt
      exact le_trans (E.β_strictMonoOn.monotoneOn hx ht hxt) (E.le_chung8 ht)
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
      exact h.trans (mul_le_mul_of_nonneg_right hδ hnR.le)
  }
  have hDepth : G.DepthRobust G.αpi := by
    apply Concrete.portStack_depthRobust_of_nodeDR
    intro X hX
    refine hN.depth_robust X ?_
    have hmono : (1 - E.π) * n ≤ (1 - π) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hnR.le
    rw [hNπ]
    exact le_trans hX hmono
  -- The challenge set has weight `ζ`; discarding its red nodes leaves a red-free set of
  -- weight at least `ζ - δ`, which is what the deterministic argument starts from.
  have hB' : B \ N.red 0 ⊆ G.layer 0 := Finset.sdiff_subset.trans hB
  have hBred : ∀ v ∈ B \ N.red 0, v ∉ N.red 0 := fun _ hv => (Finset.mem_sdiff.mp hv).2
  have hweight' : S.ζδ ≤ Concrete.Pebbling.weight n (B \ N.red 0) := by
    have hred0 : ((N.red 0).card : ℝ) ≤ δ * n := by
      have h := hN.red_bound 0
      rw [hNδ] at h
      exact h
    have hcardNat : B.card ≤ (B \ N.red 0).card + (N.red 0).card :=
      (Finset.card_le_card Finset.subset_union_left).trans_eq
        (Finset.card_sdiff_add_card B (N.red 0)).symm
    have hcard : (B.card : ℝ) ≤ ((B \ N.red 0).card : ℝ) + ((N.red 0).card : ℝ) := by
      exact_mod_cast hcardNat
    rw [le_div_iff₀ hnR] at hBweight
    change ζ - δ ≤ _
    simp only [Concrete.Pebbling.weight]
    rw [le_div_iff₀ hnR]
    linarith
  have hσapi : T.σ < G.αpi := by
    change σ < N.απ
    rw [hNαπ]; exact hσαπ
  have hzcond : LedgerCert.potHead C Cert + ((z : ℝ) - 1) * LedgerCert.potSpan C Cert
      + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ) := by
    have hcharge : Cert.lam * S.ρ / T.ghat = L.chargeRate * ρ := by
      change L.lam * ρ / E.trackingGain σ = L.lam / E.trackingGain σ * ρ
      ring
    rw [hcharge]
    exact hlevels
  have hpath := latency_potential G pebbling T Cert hN.n_pos hσapi hDepth
    (show S.ζδ ≤ S.αmax from hζ) (show S.piBar < S.ζδ - S.ρ from by
      change E.piBar < ζ - δ - ρ
      linarith [hentry])
    (show S.ρ < S.betaD S.pi - T.lam from hnobreak)
    (show T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ from hslack)
    hz hzcond (B \ N.red 0) hB' hBred hweight'
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

/-- **The asymptotic latency theorem, at full link payoff.**

Same probability event, same certified level budget and the same three ledger prices as
`chung8_pebbling_latency_whp`.  Two things change.  The graph hypothesis is stronger: the
game's robustness threshold must clear the profile's by the source weight, `π + σ ≤ E.π`,
which is depth robustness at `E.π - σ`.  In exchange every completed link contributes a
whole `απ n` instead of `(απ - σ) n`, so the path length is linear in the layer count with
slope `απ / L.linkCost` — there is no link count to choose, and no `σ < απ` to assume.

This is `Challenge.lean`'s `chung8_pebbling_latency_full_asymptotic`. -/
theorem chung8_pebbling_latency_full_asymptotic
    {ℓ n : ℕ} (lambda : ℕ) (a b : ℝ) [ChungSecurityConditions n lambda a b]
    (E : ExpansionProfile) (σ : ℝ) (L : LevelBudget E σ)
    (απ δ π ρ ζ : ℝ)
    (ha : a ≤ E.αmin) (hb : E.αmax + 1 / n ≤ b)
    (hδ : δ ≤ E.δ) (hπ : π + σ ≤ E.π)
    (hρ : 0 ≤ ρ) (hρtop : ρ ≤ L.ρmax)
    (hentry : E.piBar + ρ < ζ - δ) (hζ : ζ - δ ≤ E.αmax)
    (hnobreak : ρ < E.betaD E.π - E.floor σ)
    (hslack : E.floor σ + (L.cs - 1) * E.trackingGain σ ≤ σ)
    (hαπ : 0 ≤ απ) (hspan : 0 < L.linkCost)
    (hlevels : L.searchCost (ζ - δ) + L.chargeRate * ρ < (ℓ : ℝ)) :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun P : ChungInterlayer n =>
        ∀ M : PebblingGame ℓ n, M.απ = απ → M.δ = δ → M.π = π → M.ρ = ρ → M.ζ = ζ →
          PebblingGame.IsAdmissible M →
          ∀ B : Finset (ℕ × Fin n), B ⊆ M.layer 0 → ζ ≤ (B.card : ℝ) / n →
            M.HasUnpebbledPathTo B
              (((ℓ : ℝ) - L.searchCost (ζ - δ) - L.chargeRate * ρ) / L.linkCost
                * απ * n) P)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  classical
  refine chung8_of_expands_whp lambda a b _ ?_
  intro P hP N hNαπ hNδ hNπ hNρ hNζ hN B hB hBweight
  have hnR : (0 : ℝ) < n := by exact_mod_cast hN.n_pos
  let Pc : Concrete.PortInterlayer n := interlayerEquiv n P
  -- The public profile is the deterministic `Setting`, with the game's budget and its
  -- red-free challenge weight.
  let S : Setting :=
    { β := E.β, αg := E.αg, δ := E.δ, pi := E.π, ρ := ρ, ζδ := ζ - δ
      αmin := E.αmin, αmax := E.αmax
      β_maps := E.β_maps, β_zero := E.β_zero, β_strictMonoOn := E.β_strictMonoOn
      β_concaveOn := E.β_concaveOn, β_expands := E.β_expands, β_reversal := E.β_reversal
      αg_mem := E.αg_mem, αg_max := E.αg_max, δ_nonneg := E.δ_nonneg, ρ_nonneg := hρ
      pi_mem := E.π_mem, αg_lt_pi := E.αg_lt_π, gpi_pos := E.gpi_pos
      αmin_mem := E.αmin_mem, αmax_mem := E.αmax_mem
      gainD_αmin := E.gainD_αmin, gainD_αmax := E.gainD_αmax }
  let T : Tracking S :=
    { σ := σ, σ_gt := L.σ_gt, σ_lt := L.σ_lt, mid := L.mid, mid_ge := L.mid_ge
      mid_le := L.mid_le, mid_gain := L.mid_gain }
  let C : RefChain S T :=
    { m := L.m, x := L.x, m_pos := L.m_pos, base := L.base, width := L.width
      step := L.step, mem := L.mem, top := L.top }
  let Cert : LedgerCert S T C :=
    { lam := L.lam, loss := L.loss, cs := L.cs, wtop := L.wtop, kappa := L.kappa
      a2 := L.a2, b2 := L.b2
      one_le_lam := L.one_le_lam, loss_nonneg := L.loss_nonneg, one_le_cs := L.one_le_cs
      wtop_pos := L.wtop_pos, kappa_nonneg := L.kappa_nonneg
      loss_ge := L.loss_ge, topLip := L.topLip, chord := L.chord
      ghat_le_lam_wtop := L.ghat_le_lam_wtop, inf_rate := L.inf_rate
      blockDrop := fun y hy hyρ => L.blockDrop y hy (le_trans hyρ hρtop)
      blockDrop_one := L.blockDrop_one
      blk_rate := fun y w hy hyρ hw => L.blk_rate y w hy (le_trans hyρ hρtop) hw }
  have hPc : Pc.Expands S := by
    apply portExpands_of_public P hN.n_pos S a b ha hb
    · intro x t hx ht _ hxt
      exact le_trans (E.β_strictMonoOn.monotoneOn hx ht hxt) (E.le_chung8 ht)
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
      exact h.trans (mul_le_mul_of_nonneg_right hδ hnR.le)
  }
  have hDepth : G.DepthRobustThr (S.pi - T.σ) G.αpi := by
    apply Concrete.portStack_depthRobustThr_of_nodeDR
    intro X hX
    refine hN.depth_robust X ?_
    have hmono : (1 - (E.π - σ)) * n ≤ (1 - π) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hnR.le
    rw [hNπ]
    exact le_trans hX hmono
  -- The challenge set has weight `ζ`; discarding its red nodes leaves a red-free set of
  -- weight at least `ζ - δ`, which is what the deterministic argument starts from.
  have hB' : B \ N.red 0 ⊆ G.layer 0 := Finset.sdiff_subset.trans hB
  have hBred : ∀ v ∈ B \ N.red 0, v ∉ N.red 0 := fun _ hv => (Finset.mem_sdiff.mp hv).2
  have hweight' : S.ζδ ≤ Concrete.Pebbling.weight n (B \ N.red 0) := by
    have hred0 : ((N.red 0).card : ℝ) ≤ δ * n := by
      have h := hN.red_bound 0
      rw [hNδ] at h
      exact h
    have hcardNat : B.card ≤ (B \ N.red 0).card + (N.red 0).card :=
      (Finset.card_le_card Finset.subset_union_left).trans_eq
        (Finset.card_sdiff_add_card B (N.red 0)).symm
    have hcard : (B.card : ℝ) ≤ ((B \ N.red 0).card : ℝ) + ((N.red 0).card : ℝ) := by
      exact_mod_cast hcardNat
    rw [le_div_iff₀ hnR] at hBweight
    change ζ - δ ≤ _
    simp only [Concrete.Pebbling.weight]
    rw [le_div_iff₀ hnR]
    linarith
  have hαpi0 : (0 : ℝ) ≤ G.αpi := by
    change (0 : ℝ) ≤ N.απ
    rw [hNαπ]; exact hαπ
  have hzcond : LedgerCert.potHead C Cert + Cert.lam * S.ρ / T.ghat < (ℓ : ℝ) := by
    have hcharge : Cert.lam * S.ρ / T.ghat = L.chargeRate * ρ := by
      change L.lam * ρ / E.trackingGain σ = L.lam / E.trackingGain σ * ρ
      ring
    rw [hcharge]
    exact hlevels
  have hpath := latency_full_asymptotic G pebbling T Cert hN.n_pos hαpi0 hDepth
    (show S.ζδ ≤ S.αmax from hζ) (show S.piBar < S.ζδ - S.ρ from by
      change E.piBar < ζ - δ - ρ
      linarith [hentry])
    (show S.ρ < S.betaD S.pi - T.lam from hnobreak)
    (show T.lam + (Cert.cs - 1) * T.ghat ≤ T.σ from hslack)
    (show 0 < LedgerCert.potSpan C Cert from hspan)
    hzcond (B \ N.red 0) hB' hBred hweight'
  rcases hpath with ⟨u, v, hv, Q, hfirst, hlast, hlength⟩
  refine ⟨v, (Finset.mem_sdiff.mp hv).1, Q.nodes, Q.nonempty, Q.chain,
    Q.unpebbled', ?_, ?_⟩
  · rw [List.getLast?_eq_some_getLast Q.nonempty]
    exact congrArg some hlast
  · have hlat : ((ℓ : ℝ) - L.searchCost (ζ - δ) - L.chargeRate * ρ) / L.linkCost * απ * n
        = ((ℓ : ℝ) - LedgerCert.potHead C Cert - Cert.lam * S.ρ / T.ghat)
            / LedgerCert.potSpan C Cert * G.αpi * n := by
      have hcharge : Cert.lam * S.ρ / T.ghat = L.chargeRate * ρ := by
        change L.lam * ρ / E.trackingGain σ = L.lam / E.trackingGain σ * ρ
        ring
      rw [hcharge]
      change _ = ((ℓ : ℝ) - L.searchCost (ζ - δ) - L.chargeRate * ρ) / L.linkCost
        * N.απ * n
      rw [hNαπ]
    rw [hlat]
    exact hlength

/-! ### The degree-eight Chung profile as an instance -/

private theorem chung8Beta_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ chung8Beta x := by
  rw [chung8Beta]
  split_ifs with h
  · norm_num
  · exact Real.sSup_nonneg fun y hy => le_trans hx hy.1.1.le

/-- **The degree-eight Chung profile.**  Every field is a theorem about the constructed
finite-size profile of `ChungFilecoinCurve.lean`; `le_chung8` is the certificate that the
sampled port permutation realizes it. -/
noncomputable def chung8Profile : ExpansionProfile where
  β := ChungCurve.chungBeta8
  δ := 189 / 5000
  π := 4 / 5
  αg := ChungCurve.filecoinAlphaG
  αmin := ChungCurve.FiniteSizeProfile.αmin
  αmax := ChungCurve.FiniteSizeProfile.αmax
  β_maps := fun _ hx => ChungCurve.chungBeta8_maps hx
  β_zero := ChungCurve.chungBeta8_zero
  β_strictMonoOn := ChungCurve.chungBeta8_strictMonoOn
  β_concaveOn := ChungCurve.filecoinBeta_concaveOn
  β_expands := fun _ hx => ChungCurve.chungBeta8_expands hx
  β_reversal := fun _ hx => ChungCurve.chungBeta8_reversal hx
  αg_mem := ChungCurve.filecoinAlphaG_mem
  αg_max := fun _ hx hne => ChungCurve.filecoinAlphaG_max hx hne
  δ_nonneg := by norm_num
  π_mem := by norm_num
  αg_lt_π := ChungCurve.chung8_αg_lt_pi
  gpi_pos := by norm_num [ChungCurve.chungBeta8]
  αmin_mem := ChungCurve.FiniteSizeProfile.αmin_mem
  αmax_mem := ChungCurve.FiniteSizeProfile.αmax_mem
  gainD_αmin := ChungCurve.FiniteSizeProfile.gainD_αmin
  gainD_αmax := ChungCurve.FiniteSizeProfile.gainD_αmax
  le_chung8 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]
      simpa [ChungCurve.chungBeta8_zero] using chung8Beta_nonneg (le_refl (0 : ℝ))
    rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · rw [hx1]
      have : ChungCurve.chungBeta8 1 ≤ 1 := (ChungCurve.chungBeta8_maps (by norm_num)).2
      simpa [chung8Beta] using this
    · exact filecoinBeta_le_chung8Beta hx0 hx1

/-- **The Chung-8 level budget**, at any source weight of the certified window.  The
reference trajectory and its certificate do not move with `σ`: the tracking constants
`ĝ` and `π̂` are constant there, because `gain_δ(σ) ≥ 2 g_π` holds across the window by
concavity between its two certified endpoints. -/
noncomputable def chung8BudgetAt (σ : ℝ)
    (h1 : (74 : ℝ) / 625 ≤ σ) (h2 : σ ≤ (3 : ℝ) / 5) : LevelBudget chung8Profile σ :=
  let hρ : (0 : ℝ) ≤ 4 / 5 := by norm_num
  let T := ChungCurve.chung8TrackingAt (ρ := 4 / 5) (ζδ := 4311 / 5000) hρ h1 h2
  let C := ChungCurve.chung8RefChainAt (ρ := 4 / 5) (ζδ := 4311 / 5000) hρ h1 h2
  let Cert := ChungCurve.chung8LedgerCertAt (ρ := 4 / 5) (ζδ := 4311 / 5000)
    hρ le_rfl h1 h2
  { ρmax := 4 / 5
    σ_gt := T.σ_gt
    σ_lt := T.σ_lt
    mid := 3 / 5
    mid_ge := h2
    mid_le := by change (3 : ℝ) / 5 ≤ (4 : ℝ) / 5; norm_num
    mid_gain := T.mid_gain
    m := 4
    x := ChungCurve.chainX
    m_pos := by norm_num
    base := C.base
    width := C.width
    step := C.step
    mem := C.mem
    top := C.top
    lam := 33 / 25
    loss := 331 / 774
    cs := 8 / 5
    wtop := 387 / 2500
    kappa := 447 / 10000
    a2 := 819 / 200
    b2 := 91 / 500
    one_le_lam := by norm_num
    loss_nonneg := by norm_num
    one_le_cs := by norm_num
    wtop_pos := by norm_num
    kappa_nonneg := by norm_num
    -- these three read only the trajectory and the profile, so the fixed-source
    -- certificate serves every source weight
    loss_ge := ChungCurve.chung8LedgerCert.loss_ge
    topLip := ChungCurve.chung8LedgerCert.topLip
    chord := ChungCurve.chung8LedgerCert.chord
    ghat_le_lam_wtop := Cert.ghat_le_lam_wtop
    inf_rate := Cert.inf_rate
    blockDrop := Cert.blockDrop
    blockDrop_one := Cert.blockDrop_one
    blk_rate := Cert.blk_rate }

/-- The budget at the Filecoin source weight `σ = 0.1184`. -/
noncomputable def chung8Budget : LevelBudget chung8Profile ((74 : ℝ) / 625) :=
  chung8BudgetAt ((74 : ℝ) / 625) le_rfl (by norm_num)

/-! ### The prices of the Chung-8 budget

The level condition is `searchCost (ζ - δ) + (z - 1)·linkCost + chargeRate·ρ < ℓ`, and at
the Chung-8 budget its three terms evaluate.  That is what makes the theorem answer
questions about other parameters. -/

theorem chung8Budget_searchCost :
    chung8Budget.searchCost ((4311 : ℝ) / 5000) = 463 / 774 :=
  ChungCurve.chung8_potHead_eq

theorem chung8Budget_linkCost :
    chung8Budget.linkCost < 4 - 675 / 1113 + 331 / 774 :=
  ChungCurve.chung8_potSpan_lt

theorem chung8Budget_chargeRate : chung8Budget.chargeRate = 132000 / 11131 := by
  have h : (33 : ℝ) / 25 * (4 / 5) / ChungCurve.chung8Tracking.ghat = 105600 / 11131 :=
    ChungCurve.chung8_ledgerCharge_eq
  have hg : (0 : ℝ) < ChungCurve.chung8Tracking.ghat := by
    rw [ChungCurve.chung8_ghat_eq, ChungCurve.gpi8_eq]; norm_num
  change (33 : ℝ) / 25 / ChungCurve.chung8Tracking.ghat = _
  field_simp at h ⊢
  linarith

/-- Two links at the Filecoin parameters need fourteen layers: `13.907 < 14`. -/
example : chung8Budget.searchCost ((4311 : ℝ) / 5000)
    + (2 - 1) * chung8Budget.linkCost + chung8Budget.chargeRate * (4 / 5) < 14 := by
  rw [chung8Budget_searchCost, chung8Budget_chargeRate]
  linarith [chung8Budget_linkCost]

/-- Taking a tenth of the space back buys a layer: at `ρ = 7/10`, `12.720 < 13`. -/
example : chung8Budget.searchCost ((4311 : ℝ) / 5000)
    + (2 - 1) * chung8Budget.linkCost + chung8Budget.chargeRate * (7 / 10) < 13 := by
  rw [chung8Budget_searchCost, chung8Budget_chargeRate]
  linarith [chung8Budget_linkCost]

/-- A third link at the Filecoin budget needs eighteen layers: `17.729 < 18`. -/
example : chung8Budget.searchCost ((4311 : ℝ) / 5000)
    + (3 - 1) * chung8Budget.linkCost + chung8Budget.chargeRate * (4 / 5) < 18 := by
  rw [chung8Budget_searchCost, chung8Budget_chargeRate]
  linarith [chung8Budget_linkCost]

/-- Asymptotically one link per `3.822` layers: six links at `ℓ = 30`. -/
example : chung8Budget.searchCost ((4311 : ℝ) / 5000)
    + (6 - 1) * chung8Budget.linkCost + chung8Budget.chargeRate * (4 / 5) < 30 := by
  rw [chung8Budget_searchCost, chung8Budget_chargeRate]
  linarith [chung8Budget_linkCost]

/-! ### The raised-threshold budget

`chung8_pebbling_latency_full_asymptotic` needs `π + σ ≤ E.π`, and the fourteen-layer
profile has `E.π = 4/5`, so at that profile the *game's* robustness threshold has to drop.
The profile below keeps the game at Filecoin's `π = 4/5` and raises the profile's
fertility threshold instead, to `E.π = 4443/5000 = 0.8886` at source weight
`σ = 443/5000 = 0.0886`, so that `π + σ = E.π` on the nose.

Everything the ledger prices moves with `E.π`.  What makes the certificate cheap is the
reversal symmetry `β(1 - β x) = 1 - x` of the polygon: the `β_δ` orbit of the new tracking
floor `1 - β(0.8886) = 0.02834573` is the old chain's `β`-values read backwards, so its
five points `0.02834573, 0.0736, 0.2284, 0.5337, 0.8` are certified breakpoints already.
`ChungFilecoinMirror.lean` carries the chain and its ledger certificate. -/

/-- The degree-eight profile at the raised fertility threshold `0.8886`.  Only `π` moves;
`β`, `δ`, `αg`, `αmin` and `αmax` are `chung8Profile`'s. -/
noncomputable def chung8ProfileHi : ExpansionProfile where
  β := ChungCurve.chungBeta8
  δ := 189 / 5000
  π := 4443 / 5000
  αg := ChungCurve.filecoinAlphaG
  αmin := ChungCurve.FiniteSizeProfile.αmin
  αmax := ChungCurve.FiniteSizeProfile.αmax
  β_maps := fun _ hx => ChungCurve.chungBeta8_maps hx
  β_zero := ChungCurve.chungBeta8_zero
  β_strictMonoOn := ChungCurve.chungBeta8_strictMonoOn
  β_concaveOn := ChungCurve.filecoinBeta_concaveOn
  β_expands := fun _ hx => ChungCurve.chungBeta8_expands hx
  β_reversal := fun _ hx => ChungCurve.chungBeta8_reversal hx
  αg_mem := ChungCurve.filecoinAlphaG_mem
  αg_max := fun _ hx hne => ChungCurve.filecoinAlphaG_max hx hne
  δ_nonneg := by norm_num
  π_mem := by norm_num
  αg_lt_π := by norm_num [ChungCurve.filecoinAlphaG]
  gpi_pos := by norm_num [ChungCurve.chungBeta8]
  αmin_mem := ChungCurve.FiniteSizeProfile.αmin_mem
  αmax_mem := ChungCurve.FiniteSizeProfile.αmax_mem
  gainD_αmin := ChungCurve.FiniteSizeProfile.gainD_αmin
  gainD_αmax := ChungCurve.FiniteSizeProfile.gainD_αmax
  le_chung8 := chung8Profile.le_chung8

/-- **The raised-threshold level budget**, at source weight `σ = 0.0886`.  It is
`ChungFilecoinMirror.lean`'s reference chain and ledger certificate, repackaged: the
`LevelBudget` fields are definitionally the `RefChain` and `LedgerCert` ones. -/
noncomputable def chung8BudgetHi : LevelBudget chung8ProfileHi ((443 : ℝ) / 5000) where
  ρmax := 4 / 5
  σ_gt := ChungCurve.chung8TrackingHi.σ_gt
  σ_lt := ChungCurve.chung8TrackingHi.σ_lt
  mid := 3 / 5
  mid_ge := by norm_num
  mid_le := by change (3 : ℝ) / 5 ≤ 4443 / 5000; norm_num
  mid_gain := ChungCurve.chung8TrackingHi.mid_gain
  m := 5
  x := ChungCurve.chainXHi
  m_pos := by norm_num
  base := ChungCurve.chung8RefChainHi.base
  width := ChungCurve.chung8RefChainHi.width
  step := ChungCurve.chung8RefChainHi.step
  mem := ChungCurve.chung8RefChainHi.mem
  top := ChungCurve.chung8RefChainHi.top
  lam := 9 / 8
  loss := 8860 / 11131
  cs := 233 / 100
  wtop := 11131 / 100000
  kappa := 283 / 10000
  a2 := 4
  b2 := 1 / 2
  one_le_lam := by norm_num
  loss_nonneg := by norm_num
  one_le_cs := by norm_num
  wtop_pos := by norm_num
  kappa_nonneg := by norm_num
  loss_ge := ChungCurve.chung8LedgerCertHi.loss_ge
  topLip := ChungCurve.chung8LedgerCertHi.topLip
  chord := ChungCurve.chung8LedgerCertHi.chord
  ghat_le_lam_wtop := ChungCurve.chung8LedgerCertHi.ghat_le_lam_wtop
  inf_rate := ChungCurve.chung8LedgerCertHi.inf_rate
  blockDrop := ChungCurve.chung8LedgerCertHi.blockDrop
  blockDrop_one := ChungCurve.chung8LedgerCertHi.blockDrop_one
  blk_rate := ChungCurve.chung8LedgerCertHi.blk_rate

theorem chung8BudgetHi_searchCost :
    chung8BudgetHi.searchCost ((4311 : ℝ) / 5000) = 1 + 2640 / 11131 :=
  ChungCurve.chung8Hi_potHead_eq

theorem chung8BudgetHi_linkCost :
    chung8BudgetHi.linkCost = 4 - 25 / 258 + 8860 / 11131 :=
  ChungCurve.chung8Hi_potSpan_eq

theorem chung8BudgetHi_chargeRate :
    chung8BudgetHi.chargeRate = 112500000 / 4525427 := by
  change (9 : ℝ) / 8 / ChungCurve.chung8TrackingHi.ghat = _
  rw [ChungCurve.chung8Hi_ghat]
  norm_num

/-- **The 14-layer Filecoin latency lower bound** at `lambda` bits of security: an
unpebbled path of length `0.2816 n`.  It is `chung8_pebbling_latency_whp` at the
degree-eight profile and its level budget, whose level condition reads
`0.5982 + 3.8212 + 9.4870 < 14`. -/
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
  have hn1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (1 : ℝ) / 100 ≤ chung8Profile.αmin := by
    change (1 : ℝ) / 100 ≤ ChungCurve.filecoinAlphaMin
    rw [ChungCurve.filecoinAlphaMin]; norm_num
  have hb : chung8Profile.αmax + 1 / (n : ℝ) ≤ 24 / 25 := by
    have h1 : (1 : ℝ) / n ≤ 1 / 1000 :=
      one_div_le_one_div_of_le (by norm_num) hn1000
    have h2 : chung8Profile.αmax = (14155 : ℝ) / 14911 := by
      change ChungCurve.filecoinAlphaMax = _
      rw [ChungCurve.filecoinAlphaMax]
    rw [h2]; linarith
  have hζδ : (9 : ℝ) / 10 - 189 / 5000 = 4311 / 5000 := by norm_num
  have hhead : chung8Budget.searchCost ((9 : ℝ) / 10 - 189 / 5000) = 463 / 774 := by
    rw [hζδ]
    exact ChungCurve.chung8_potHead_eq
  have hspan : chung8Budget.linkCost < 4 - 675 / 1113 + 331 / 774 :=
    ChungCurve.chung8_potSpan_lt
  have hcharge : chung8Budget.chargeRate * (4 / 5) = 105600 / 11131 := by
    have h : (33 : ℝ) / 25 * (4 / 5) / ChungCurve.chung8Tracking.ghat = 105600 / 11131 :=
      ChungCurve.chung8_ledgerCharge_eq
    change (33 : ℝ) / 25 / ChungCurve.chung8Tracking.ghat * (4 / 5) = _
    rw [← h]; ring
  have hlevels : chung8Budget.searchCost ((9 : ℝ) / 10 - 189 / 5000)
      + (((2 : ℕ) : ℝ) - 1) * chung8Budget.linkCost
      + chung8Budget.chargeRate * (4 / 5) < ((14 : ℕ) : ℝ) := by
    rw [hhead, hcharge]
    push_cast
    linarith
  have hmain := chung8_pebbling_latency_whp (ℓ := 14) (n := n) lambda (1 / 100) (24 / 25)
    chung8Profile ((74 : ℝ) / 625) chung8Budget ((1 : ℝ) / 5) ((189 : ℝ) / 5000)
    ((4 : ℝ) / 5) ((4 : ℝ) / 5) ((9 : ℝ) / 10) 2 (by norm_num) ha hb le_rfl le_rfl
    (by norm_num) le_rfl
    (by change ChungCurve.chung8Setting.piBar + (4 : ℝ) / 5 < _
        rw [Setting.piBar]
        norm_num [ChungCurve.chungBeta8])
    (by change (9 : ℝ) / 10 - 189 / 5000 ≤ ChungCurve.filecoinAlphaMax
        rw [ChungCurve.filecoinAlphaMax]; norm_num)
    ChungCurve.chung8_nobreak ChungCurve.chung8_cs_slack (by norm_num) hlevels
  rw [HoldsWithFailureAtMost] at hmain ⊢
  refine hmain.trans (probabilityOf_mono _ ?_)
  intro P hev M hαπ hδ hπ hρ hζ hAdm A hA hweight
  have hlen : M.latencyLength ((74 : ℝ) / 625) 2 = (176 : ℝ) / 625 * n := by
    simp only [PebblingGame.latencyLength, hαπ]
    push_cast
    ring
  rw [← hlen]
  exact hev M hαπ hδ hπ hρ hζ hAdm A hA hweight

/-- **The asymptotic Filecoin latency bound at Filecoin's own robustness threshold.**

The point `(απ, δ, π, ρ, ζ, σ) = (0.2, 0.0378, 0.8, 0.8, 0.9, 0.0886)` of
`chung8_pebbling_latency_full_asymptotic`, at every layer count from twenty-two on.  The
game's depth-robustness hypothesis is exactly `chung8_pebbling_latency_14`'s — deleting
any `0.2 n` nodes of a layer must leave an intra-layer path on `0.2 n` nodes — and every
completed chain link still pays the whole `απ n = 0.2 n` rather than `(απ - σ) n`.

What pays for that is the *fertility* threshold, raised to `E.π = 0.8886` so that
`π + σ = E.π`: a footprint of that weight contains `0.0886 n` nodes each beginning a whole
`0.2 n` path inside it, by depth robustness at `0.8886 - 0.0886 = 0.8`.  Raising `E.π`
lowers the tracking gain from `g_π = 0.11131` to `0.04525`, so the ledger's three prices
become `1.2372`, `4.6991` and `19.8876` where `chung8_pebbling_latency_14` has `0.5982`,
`3.8212` and `9.4870`.

The certified slope is `17/400 = 0.0425` of `n` per layer, against the `0.02135` of
`chung8_pebbling_latency_14` — 1.99 times — and the offset `21.2` absorbs the head
`1.2372 + 19.8876 < 21.1249`.  The bound passes `0.2 n` at `ℓ = 26`. -/
theorem chung8_pebbling_latency_asymptotic
    {ℓ n : ℕ} (lambda : ℕ) (hn : 1000 ≤ n) (hℓ : 22 ≤ ℓ)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (fun P : ChungInterlayer n =>
        ∀ M : PebblingGame ℓ n,
          M.απ = (1 : ℝ) / 5 → M.δ = (189 : ℝ) / 5000 → M.π = (4 : ℝ) / 5 →
          M.ρ = (4 : ℝ) / 5 → M.ζ = (9 : ℝ) / 10 →
          PebblingGame.IsAdmissible M →
          ∀ A : Finset (ℕ × Fin n), A ⊆ M.layer 0 →
            (9 : ℝ) / 10 ≤ (A.card : ℝ) / n →
              M.HasUnpebbledPathTo A
                ((17 : ℝ) / 400 * ((ℓ : ℝ) - 106 / 5) * n) P)
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  have hn1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hℓ' : (22 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (1 : ℝ) / 100 ≤ chung8ProfileHi.αmin := by
    change (1 : ℝ) / 100 ≤ ChungCurve.filecoinAlphaMin
    rw [ChungCurve.filecoinAlphaMin]; norm_num
  have hb : chung8ProfileHi.αmax + 1 / (n : ℝ) ≤ 24 / 25 := by
    have h1 : (1 : ℝ) / n ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hn1000
    have h2 : chung8ProfileHi.αmax = (14155 : ℝ) / 14911 := by
      change ChungCurve.filecoinAlphaMax = _
      rw [ChungCurve.filecoinAlphaMax]
    rw [h2]; linarith
  have hζδ : (9 : ℝ) / 10 - 189 / 5000 = 4311 / 5000 := by norm_num
  have hlevels : chung8BudgetHi.searchCost ((9 : ℝ) / 10 - 189 / 5000)
      + chung8BudgetHi.chargeRate * (4 / 5) < (ℓ : ℝ) := by
    rw [hζδ, chung8BudgetHi_searchCost, chung8BudgetHi_chargeRate]
    linarith
  have hmain := chung8_pebbling_latency_full_asymptotic (ℓ := ℓ) (n := n) lambda
    (1 / 100) (24 / 25)
    chung8ProfileHi ((443 : ℝ) / 5000) chung8BudgetHi ((1 : ℝ) / 5) ((189 : ℝ) / 5000)
    ((4 : ℝ) / 5) ((4 : ℝ) / 5) ((9 : ℝ) / 10) ha hb le_rfl
    (by change (4 : ℝ) / 5 + 443 / 5000 ≤ (4443 : ℝ) / 5000; norm_num)
    (by norm_num) le_rfl
    (by change ChungCurve.chung8SettingHi.piBar + (4 : ℝ) / 5 < _
        rw [ChungCurve.chung8Hi_piBar]; norm_num)
    (by change (9 : ℝ) / 10 - 189 / 5000 ≤ ChungCurve.filecoinAlphaMax
        rw [ChungCurve.filecoinAlphaMax]; norm_num)
    ChungCurve.chung8Hi_nobreak ChungCurve.chung8Hi_cs_slack (by norm_num)
    ChungCurve.chung8Hi_potSpan_pos hlevels
  rw [HoldsWithFailureAtMost] at hmain ⊢
  refine hmain.trans (probabilityOf_mono _ ?_)
  intro P hev M hαπ hδ hπ hρ hζ hAdm A hA hweight
  obtain ⟨a, haA, Q, hQne, hQchain, hQunp, hQlast, hQlen⟩ :=
    hev M hαπ hδ hπ hρ hζ hAdm A hA hweight
  refine ⟨a, haA, Q, hQne, hQchain, hQunp, hQlast, le_trans ?_ hQlen⟩
  -- weaken the exact span and head to the round constants of the statement
  rw [hζδ, chung8BudgetHi_searchCost, chung8BudgetHi_chargeRate, chung8BudgetHi_linkCost]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set q : ℝ := ((ℓ : ℝ) - (1 + 2640 / 11131) - 112500000 / 4525427 * (4 / 5))
    / (4 - 25 / 258 + 8860 / 11131) with hqdef
  have hqS : q * (4 - 25 / 258 + 8860 / 11131)
      = (ℓ : ℝ) - (1 + 2640 / 11131) - 112500000 / 4525427 * (4 / 5) := by
    rw [hqdef]; field_simp
  norm_num at hqS
  have hkey : (17 : ℝ) / 400 * ((ℓ : ℝ) - 106 / 5) ≤ q * (1 / 5) := by linarith
  exact mul_le_mul_of_nonneg_right hkey hn0

end ProofOfSpaceStatement

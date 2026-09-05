import ProofOfSpace.Amplification
import ProofOfSpace.PortStack
import ProofOfSpace.PortExpansionProbability
import ProofOfSpace.ChungRelative
import ProofOfSpace.UniformGainNumerics

namespace ProofOfSpaceStatement

open Finset Set
open scoped ENNReal

structure ChungInterlayer (n : ℕ) where
  perm : Equiv.Perm (Fin 8 × Fin n)
deriving Fintype

instance (n : ℕ) : Nonempty (ChungInterlayer n) := ⟨⟨Equiv.refl _⟩⟩

namespace ChungInterlayer

noncomputable def uniformLaw (n : ℕ) : PMF (ChungInterlayer n) :=
  PMF.uniformOfFintype (ChungInterlayer n)

def ports {n : ℕ} (T : Finset (Fin n)) : Finset (Fin 8 × Fin n) :=
  Finset.univ ×ˢ T

def neighborhood {n : ℕ} (p : ChungInterlayer n) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  (ports T).image fun q => (p.perm q).2

end ChungInterlayer

noncomputable def probabilityOf {A : Type*} (p : PMF A) (Q : A → Prop) : ℝ≥0∞ :=
  by classical exact ∑' a, if Q a then p a else 0

def HoldsWithFailureAtMost {A : Type*} (p : PMF A) (Q : A → Prop)
    (δ : ℝ≥0∞) : Prop :=
  1 - δ ≤ probabilityOf p Q

/-- Reyzin's degree-eight union-bound exponent, in nats. -/
noncomputable def chungExponent8 (x y : ℝ) : ℝ :=
  Real.binEntropy x + Real.binEntropy y +
    8 * (y * Real.binEntropy (x / y) - Real.binEntropy x)

/-- A symmetric relative exponent margin. It is invariant under Chung's
anti-diagonal reflection `(x,y) ↦ (1-y,1-x)` and remains meaningful at every
interior pair. -/
noncomputable def chung8Level (x y : ℝ) : ℝ :=
  min (Real.binEntropy x) (Real.binEntropy y) / 2 ^ (23 : ℕ)

/-- The degree-eight Chung expansion function, defined directly by its entropy formula. -/
noncomputable def chung8Beta (x : ℝ) : ℝ :=
  if x = 1 then 1
  else sSup {y | y ∈ Set.Ioo x 1 ∧ chungExponent8 x y < -chung8Level x y}

/-- The largest integer neighbourhood size still counted as a failure. -/
noncomputable def chung8FailureProfile (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.ceil (chung8Beta ((k : ℝ) / n) * n) - 1 else 0

namespace ChungInterlayer

/-- Chung-8 expansion demanded only of source sets whose density lies in `[a, b]`.
The deterministic argument queries expansion at densities bounded away from zero, so
the assumption—and the union bound paying for it—need not cover vanishing densities,
where a Chung profile costs a birthday collision rather than an exponentially small
event. -/
def ExpandsOn {n : ℕ} (p : ChungInterlayer n) (a b : ℝ) : Prop :=
  ∀ T : Finset (Fin n), a ≤ (T.card : ℝ) / n → (T.card : ℝ) / n ≤ b →
    chung8FailureProfile n T.card < (p.neighborhood T).card

end ChungInterlayer

/-- The probability that all source ports land among the target ports. -/
noncomputable def chung8PortHitProb (n k m : ℕ) : ℝ≥0∞ :=
  ((8 * m).descFactorial (8 * k) : ℝ≥0∞) /
    ((8 * n).descFactorial (8 * k) : ℝ≥0∞)

/-- The exact port-model union bound for the functional Chung-8 profile, over the
source densities in `[a, b]`. -/
noncomputable def chung8FailureBound (n : ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ∑ k ∈ (Finset.Ico 1 (n + 1)).filter
      (fun k : ℕ => a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ b),
    (n.choose k : ℝ≥0∞) *
      ((n.choose (chung8FailureProfile n k) : ℝ≥0∞) *
        chung8PortHitProb n k (chung8FailureProfile n k))

/-- The exact Chung-8 union bound on `[a, b]` is at most two to the minus lambda. -/
class ChungSecurityConditions (n : ℕ) (lambda : ℕ) (a b : ℝ) : Prop where
  n_pos : 0 < n
  a_pos : 0 < a
  security : chung8FailureBound n a b ≤ (2 : ℝ≥0∞)⁻¹ ^ lambda

open ProofOfSpace

/-- A static black/red pebbling position and its latency parameters on an `ℓ`-layer
stacked graph of width `n`. The width is a parameter, not a field, so that one
probability space `ChungInterlayer n` serves every game. -/
structure PebblingGame (ℓ n : ℕ) where
  απ : ℝ
  π : ℝ
  δ : ℝ
  ρ : ℝ
  ζ : ℝ
  intra : Fin n → Fin n → Prop
  black : ℕ → Finset (ℕ × Fin n)
  red : ℕ → Finset (ℕ × Fin n)

variable {ℓ n : ℕ}

def PebblingGame.layer (_G : PebblingGame ℓ n) (i : ℕ) : Finset (ℕ × Fin n) :=
  if i < ℓ then Finset.univ.image (fun v : Fin n => (i, v)) else ∅

def PebblingGame.depth (_G : PebblingGame ℓ n) (v : ℕ × Fin n) : ℕ := v.1

def PebblingGame.intraEdge (G : PebblingGame ℓ n) (i : ℕ)
    (u v : ℕ × Fin n) : Prop :=
  u.1 = i ∧ v.1 = i ∧ i < ℓ ∧ G.intra u.2 v.2

def PebblingGame.interEdge (_G : PebblingGame ℓ n)
    (p : ChungInterlayer n) (i : ℕ) (u v : ℕ × Fin n) : Prop :=
  u.1 = i + 1 ∧ v.1 = i ∧ i + 1 < ℓ ∧
    ∃ q ∈ ChungInterlayer.ports ({v.2} : Finset (Fin n)), (p.perm q).2 = u.2

def PebblingGame.edge (G : PebblingGame ℓ n) (p : ChungInterlayer n)
    (u v : ℕ × Fin n) : Prop :=
  (∃ i, G.intraEdge i u v) ∨ (∃ i, G.interEdge p i u v)

/-- Structural graph assumptions and pebble-budget constraints for an admissible game. -/
class PebblingGame.IsAdmissible (G : PebblingGame ℓ n) : Prop where
  intra_rank : ∀ {u v}, G.intra u v → u.val < v.val
  /-- Reyzin parameters: density `π` of survivors guarantees `απ * n` path vertices. -/
  depth_robust : ∀ X : Finset (Fin n), G.π * n ≤ (X.card : ℝ) →
    ∃ P : List (Fin n), P ≠ [] ∧ P.IsChain G.intra ∧
      (∀ v ∈ P, v ∈ X) ∧ G.απ * n ≤ (P.length : ℝ)
  black_subset : ∀ i, G.black i ⊆ G.layer i
  red_subset : ∀ i, G.red i ⊆ G.layer i
  black_total : ∀ m,
    ∑ i ∈ Finset.range m, ((G.black i).card : ℝ) / n ≤ G.ρ
  red_bound : ∀ i, ((G.red i).card : ℝ) ≤ G.δ * n
  n_pos : 0 < n

/-- The game has an unpebbled directed path of length at least `L` ending in `S`. -/
def PebblingGame.HasUnpebbledPathTo (G : PebblingGame ℓ n)
    (S : Finset (ℕ × Fin n))
    (L : ℝ) (p : ChungInterlayer n) : Prop :=
  ∃ v ∈ S, ∃ P : List (ℕ × Fin n),
    P ≠ [] ∧ P.IsChain (G.edge p) ∧
    (∀ w ∈ P, w ∉ G.black (G.depth w) ∧ w ∉ G.red (G.depth w)) ∧
    P.getLast? = some v ∧ L ≤ (P.length : ℝ)

/-- A latency event is uniform over admissible positions and challenges, both of
which may be chosen after observing the sampled wiring. -/
def PebblingGame.LatencyEvent (ℓ n : ℕ) (απ δ π ρ ζ L : ℝ)
    (p : ChungInterlayer n) : Prop :=
  ∀ G : PebblingGame ℓ n, G.απ = απ → G.δ = δ → G.π = π → G.ρ = ρ → G.ζ = ζ →
    PebblingGame.IsAdmissible G →
    ∀ S : Finset (ℕ × Fin n), S ⊆ G.layer 0 → ζ ≤ (S.card : ℝ) / n →
      G.HasUnpebbledPathTo S L p

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

/-- Transfer density expansion to a real query by rounding up to a subset.
The upper endpoint is an integer density, so rounding stays inside the interval. -/
private theorem operational_of_density (W : ChungInterlayer n) (hn : 0 < n)
    (β : ℝ → ℝ) (a : ℝ) (m : ℕ)
    (hmono : MonotoneOn β (Icc a ((m : ℝ) / n)))
    (hexp : ∀ X : Finset (Fin n), a ≤ (X.card : ℝ) / n →
      (X.card : ℝ) / n ≤ (m : ℝ) / n → β ((X.card : ℝ) / n) * n ≤ (W.neighborhood X).card)
    (X : Finset (Fin n)) (x : ℝ) (hx : x ∈ Icc a ((m : ℝ) / n))
    (hX : x ≤ (X.card : ℝ) / n) : β x * n ≤ (W.neighborhood X).card := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkX : Nat.ceil (x * n) ≤ X.card := Nat.ceil_le.mpr ((le_div_iff₀ hnR).mp hX)
  have hkm : Nat.ceil (x * n) ≤ m := Nat.ceil_le.mpr ((le_div_iff₀ hnR).mp hx.2)
  obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hkX
  have hxY : x ≤ (Y.card : ℝ) / n := by
    rw [le_div_iff₀ hnR, hYcard]; exact Nat.le_ceil _
  have hYm : (Y.card : ℝ) / n ≤ (m : ℝ) / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast (hYcard ▸ hkm : Y.card ≤ m)
  have hY := hexp Y (hx.1.trans hxY) hYm
  have hcard : (W.neighborhood Y).card ≤ (W.neighborhood X).card :=
    Finset.card_le_card (neighborhood_mono (interlayerEquiv n W) hYX)
  exact (mul_le_mul_of_nonneg_right
    (hmono hx ⟨hx.1.trans hxY, hYm⟩ hxY) hnR.le).trans
      (hY.trans (by exact_mod_cast hcard))

/-- Latency amplification. The gain `g` is defined at density `m/n`; the interval
hypothesis requires at least this gain at every queried density. -/
theorem pebbling_latency {ℓ n : ℕ} (W : ChungInterlayer n)
    (β : ℝ → ℝ) (απ π : ℝ) (m s z : ℕ) (δ ρ ζ : ℝ) :
    let σ := (s : ℝ) / n
    let g := β ((m : ℝ) / n) - δ - (m : ℝ) / n
    let I := Icc (min (ζ - δ) (β ((m : ℝ) / n) - δ) - ρ) ((m : ℝ) / n)
    let q := min (Nat.ceil (απ * n))
      (Nat.ceil (απ * n) + m + 1 - (Nat.ceil (π * n) + s))
    Nat.ceil (π * n) ≤ m → 1 ≤ q → 1 ≤ z → 0 < g →
    ρ < min (ζ - δ) (β ((m : ℝ) / n) - δ) → σ ∈ I →
    MonotoneOn β I → (∀ x ∈ I, g ≤ β x - δ - x) →
    2 * g ≤ β σ - δ - min (ζ - δ) (β ((m : ℝ) / n) - δ) + ρ →
    (∀ X : Finset (Fin n), (X.card : ℝ) / n ∈ I →
      β ((X.card : ℝ) / n) * n ≤ (W.neighborhood X).card) →
    ρ + g + max ((m : ℝ) / n - (ζ - δ)) (g + β ((m : ℝ) / n) - β σ) +
      ((z : ℝ) - 1) * (g + β ((m : ℝ) / n) - β σ) < g * ℓ →
    PebblingGame.LatencyEvent ℓ n απ δ π ρ ζ
      (Nat.ceil (απ * n) + ((z : ℝ) - 1) * q) W := by
  classical
  dsimp only
  intro htm hq hz hg hentry hσ hmono hgain hsource hexp hlevels
    N hNαπ hNδ hNπ hNρ hNζ hN S hS hSweight
  have hnR : (0 : ℝ) < n := by exact_mod_cast hN.n_pos
  have hρ : 0 ≤ ρ := by simpa [hNρ] using hN.black_total 0
  have htop : (m : ℝ) / n + (β ((m : ℝ) / n) - δ - (m : ℝ) / n) =
      β ((m : ℝ) / n) - δ := by ring
  let R : UniformGain.Parameters := {
    p := (m : ℝ) / n, σ := (s : ℝ) / n,
    g := β ((m : ℝ) / n) - δ - (m : ℝ) / n,
    h := β ((s : ℝ) / n) - δ, w := ζ - δ, ρ := ρ,
    g_pos := hg, rho_nonneg := hρ,
    a_pos := by rw [htop]; linarith,
    a_le_source := by rw [htop]; exact hσ.1,
    source_le_p := hσ.2,
    h_le := by
      rw [htop]
      exact sub_le_sub_right (hmono hσ ⟨hσ.1.trans hσ.2, le_rfl⟩ hσ.2) _,
    source_guard := by rw [htop]; linarith }
  have hrange : Icc R.a R.p =
      Icc (min (ζ - δ) (β ((m : ℝ) / n) - δ) - ρ) ((m : ℝ) / n) := by
    dsimp [UniformGain.Parameters.a, R]; rw [htop]
  have hcost : R.C = R.g + β ((m : ℝ) / n) - β ((s : ℝ) / n) := by
    dsimp [UniformGain.Parameters.C, R]; ring
  let H : Concrete.StandaloneGraph n :=
    { edge := N.intra, edge_lt := fun {_ _} h => hN.intra_rank h }
  let G := Concrete.portStack H ℓ (fun _ => interlayerEquiv n W)
  let B : Concrete.Pebbling G δ ρ := {
    black := N.black, red := N.red,
    black_subset := hN.black_subset, red_subset := hN.red_subset,
    black_total := by simpa [hNρ] using hN.black_total,
    red_bound := by simpa [hNδ] using hN.red_bound }
  have hDR : G.DepthRobust (Nat.ceil (π * n)) (Nat.ceil (απ * n)) := by
    apply Concrete.portStack_depthRobust
    intro X hX
    obtain ⟨Q, hQ, hc, hm, hl⟩ := hN.depth_robust X (by
      rw [hNπ]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hX))
    exact ⟨Q, hQ, hc, hm, Nat.ceil_le.mpr (by simpa [hNαπ] using hl)⟩
  have hGexp : G.Expands β R.a R.p := by
    apply Concrete.portStack_expands
    intro k hk X x hx hX
    apply operational_of_density W hN.n_pos β R.a m
    · rwa [hrange]
    · intro Y hlo hhi
      apply hexp Y
      rw [← hrange]
      exact ⟨hlo, hhi⟩
    · exact hx
    · exact hX
  have hS' : S \ N.red 0 ⊆ G.layer 0 := Finset.sdiff_subset.trans hS
  have hSred : ∀ v ∈ S \ N.red 0, v ∉ B.red 0 := fun _ hv => (Finset.mem_sdiff.mp hv).2
  have hweight : R.w ≤ Concrete.Pebbling.weight n (S \ N.red 0) := by
    have hred0 : ((N.red 0).card : ℝ) ≤ δ * n := by simpa [hNδ] using hN.red_bound 0
    have hcardNat : S.card ≤ (S \ N.red 0).card + (N.red 0).card :=
      (Finset.card_le_card Finset.subset_union_left).trans_eq
        (Finset.card_sdiff_add_card S (N.red 0)).symm
    have hcard : (S.card : ℝ) ≤ ((S \ N.red 0).card : ℝ) + ((N.red 0).card : ℝ) := by
      exact_mod_cast hcardNat
    rw [le_div_iff₀ hnR] at hSweight
    change ζ - δ ≤ _
    rw [Concrete.Pebbling.weight, le_div_iff₀ hnR]
    linarith
  have hgain' : ∀ x ∈ Icc R.a R.p, x + R.g ≤ β x - δ := by
    intro x hx
    rw [hrange] at hx
    have := hgain x hx
    change x + (β ((m : ℝ) / n) - δ - (m : ℝ) / n) ≤ _
    linarith
  have hlevels' : R.ρ + R.g + max (R.p - R.w) R.C + ((z : ℝ) - 1) * R.C < R.g * ℓ := by
    rw [hcost]; exact hlevels
  have hpath := B.latency (E := R) hN.n_pos hgain' le_rfl hGexp hDR htm hq
    rfl rfl hz hlevels' (S \ N.red 0) hS' hSred hweight
  obtain ⟨u, v, hv, Q, _, hlast, hlength⟩ := hpath
  refine ⟨v, (Finset.mem_sdiff.mp hv).1, Q.nodes, Q.nonempty, Q.chain,
    Q.unpebbled', ?_, hlength⟩
  rw [List.getLast?_eq_some_getLast Q.nonempty]
  exact congrArg some hlast

/-- The same latency theorem on one uniform Chung port permutation, simultaneously
for all admissible positions and challenge sets `S`. -/
theorem chung8_pebbling_latency_whp {ℓ n : ℕ} (lambda : ℕ) (u v : ℝ)
    [ChungSecurityConditions n lambda u v]
    (β : ℝ → ℝ) (απ π : ℝ) (m s z : ℕ) (δ ρ ζ : ℝ) :
    let σ := (s : ℝ) / n
    let g := β ((m : ℝ) / n) - δ - (m : ℝ) / n
    let I := Icc (min (ζ - δ) (β ((m : ℝ) / n) - δ) - ρ) ((m : ℝ) / n)
    let q := min (Nat.ceil (απ * n))
      (Nat.ceil (απ * n) + m + 1 - (Nat.ceil (π * n) + s))
    Nat.ceil (π * n) ≤ m → 1 ≤ q → 1 ≤ z → 0 < g →
    ρ < min (ζ - δ) (β ((m : ℝ) / n) - δ) → σ ∈ I → I ⊆ Icc u v →
    MonotoneOn β I → (∀ x ∈ I, g ≤ β x - δ - x) →
    2 * g ≤ β σ - δ - min (ζ - δ) (β ((m : ℝ) / n) - δ) + ρ →
    (∀ x ∈ I, β x ≤ chung8Beta x) →
    ρ + g + max ((m : ℝ) / n - (ζ - δ)) (g + β ((m : ℝ) / n) - β σ) +
      ((z : ℝ) - 1) * (g + β ((m : ℝ) / n) - β σ) < g * ℓ →
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent ℓ n απ δ π ρ ζ
        (Nat.ceil (απ * n) + ((z : ℝ) - 1) * q))
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  dsimp only
  intro htm hq hz hg hentry hσ hI hmono hgain hsource hdom hlevels
  apply chung8_of_expands_whp lambda u v
  intro W hW
  apply pebbling_latency W β απ π m s z δ ρ ζ htm hq hz hg hentry hσ hmono hgain hsource
  · intro X hX
    have hn : 0 < n := ChungSecurityConditions.n_pos (lambda := lambda) (a := u) (b := v)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hXn : X.card ≤ n := by simpa using Finset.card_le_univ X
    have hprofile := hW X (hI hX).1 (hI hX).2
    rw [chung8FailureProfile, if_pos hXn] at hprofile
    have hceil : Nat.ceil (chung8Beta ((X.card : ℝ) / n) * n) ≤ (W.neighborhood X).card := by omega
    exact (mul_le_mul_of_nonneg_right (hdom _ hX) hnR.le).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast hceil))
  · exact hlevels

/-- Eighteen layers give more than `0.2n` latency at the Filecoin parameters,
including finite-width rounding and the explicit Chung security assumption. -/
theorem chung8_pebbling_latency_18 (n lambda : ℕ) (hn : 10000 ≤ n)
    [ChungSecurityConditions n lambda (1 / 100) (24 / 25)] :
    HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent 18 n (1 / 5) (189 / 5000) (4 / 5) (4 / 5) (9 / 10)
        (41 / 200 * n)) ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let m := Nat.ceil ((4 : ℝ) / 5 * n)
  let d := Nat.ceil ((1 : ℝ) / 5 * n)
  let s := Nat.ceil ((39 : ℝ) / 200 * n)
  let σ := (s : ℝ) / n
  let β := ChungCurve.filecoinBeta
  let g := β ((m : ℝ) / n) - 189 / 5000 - (m : ℝ) / n
  have hmlo : (4 : ℝ) / 5 * n ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < 4 / 5 * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdlo : (1 : ℝ) / 5 * n ≤ d := Nat.le_ceil _
  have hslo : (39 : ℝ) / 200 * n ≤ s := Nat.le_ceil _
  have hshi : (s : ℝ) < 39 / 200 * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm : (m : ℝ) / n ∈ Icc ((4 : ℝ) / 5) (8001 / 10000) := by
    constructor
    · exact (le_div_iff₀ hnpos).mpr hmlo
    · apply (div_le_iff₀ hnpos).mpr; nlinarith
  have hσ : σ ∈ Icc ((39 : ℝ) / 200) (1951 / 10000) := by
    dsimp [σ]; constructor
    · exact (le_div_iff₀ hnpos).mpr hslo
    · apply (div_le_iff₀ hnpos).mpr; nlinarith
  have hsd : s ≤ d := Nat.ceil_mono (by nlinarith : (39 : ℝ) / 200 * n ≤ 1 / 5 * n)
  have hspos : 1 ≤ s := by
    have : (0 : ℝ) < s := by linarith
    exact_mod_cast this
  have hqeq : min d (d + m + 1 - (m + s)) = d + 1 - s := by omega
  have hq : 1 ≤ min d (d + m + 1 - (m + s)) := by rw [hqeq]; omega
  have hg : g ∈ Icc ((111 : ℝ) / 1000) (11131 / 100000) := by
    dsimp [g, β]
    rw [ChungCurve.filecoinBeta_affine_11 hm.1 (by linarith [hm.2])]
    constructor <;> linarith [hm.1, hm.2]
  have hmin : min ((9 : ℝ) / 10 - 189 / 5000)
      (β ((m : ℝ) / n) - 189 / 5000) = 4311 / 5000 := by
    have hfree : (m : ℝ) / n + g = β ((m : ℝ) / n) - 189 / 5000 := by dsimp [g]; ring
    rw [min_eq_left (by linarith [hm.1, hg.1])]; norm_num
  have hsource : (4806 : ℝ) / 10000 ≤ β σ - 189 / 5000 :=
    UniformGain.filecoin_source_0195.trans
      (sub_le_sub_right (ChungCurve.filecoinBeta_strictMono.monotone hσ.1) _)
  have hdifference : g + β ((m : ℝ) / n) - β σ ≤ (54212 : ℝ) / 100000 := by
    have hfree : β ((m : ℝ) / n) - 189 / 5000 = (m : ℝ) / n + g := by dsimp [g]; ring
    linarith [hm.2, hg.2]
  have hmax : max ((m : ℝ) / n - ((9 : ℝ) / 10 - 189 / 5000))
      (g + β ((m : ℝ) / n) - β σ) = g + β ((m : ℝ) / n) - β σ := by
    apply max_eq_right
    have hmono : β σ ≤ β ((m : ℝ) / n) :=
      ChungCurve.filecoinBeta_strictMono.monotone (by linarith [hσ.2, hm.1])
    linarith [hm.2, hg.1]
  have hgeneric : HoldsWithFailureAtMost (ChungInterlayer.uniformLaw n)
      (PebblingGame.LatencyEvent 18 n (1 / 5) (189 / 5000) (4 / 5) (4 / 5) (9 / 10)
        (d + (((2 : ℕ) : ℝ) - 1) * (min d (d + m + 1 - (m + s)))))
      ((2 : ℝ≥0∞)⁻¹ ^ lambda) := by
    apply chung8_pebbling_latency_whp lambda (1 / 100) (24 / 25)
      β (1 / 5) (4 / 5) m s 2 (189 / 5000) (4 / 5) (9 / 10)
    · exact le_rfl
    · exact hq
    · norm_num
    · change 0 < g; linarith [hg.1]
    · rw [hmin]; norm_num
    · change σ ∈ Icc (min _ _ - _) ((m : ℝ) / n)
      rw [hmin]
      constructor <;> linarith [hσ.1, hσ.2, hm.1]
    · intro x hx
      rw [hmin] at hx
      constructor <;> linarith [hx.1, hx.2, hm.2]
    · exact ChungCurve.filecoinBeta_strictMono.monotone.monotoneOn _
    · intro x hx
      rw [hmin] at hx
      apply UniformGain.filecoin_gain_at_threshold hm
      exact ⟨by linarith [hx.1], hx.2⟩
    · change 2 * g ≤ β σ - 189 / 5000 - min _ _ + 4 / 5
      rw [hmin]; linarith [hg.2]
    · intro x hx
      rw [hmin] at hx
      exact filecoinBeta_le_chung8Beta (by linarith [hx.1]) (by linarith [hx.2, hm.2])
    · change (4 : ℝ) / 5 + g + max _ (g + β ((m : ℝ) / n) - β σ) +
        (2 - 1) * (g + β ((m : ℝ) / n) - β σ) < g * 18
      rw [hmax]; nlinarith [hg.1, hg.2]
  have hlength : (41 : ℝ) / 200 * n ≤
      d + (((2 : ℕ) : ℝ) - 1) * (min d (d + m + 1 - (m + s))) := by
    rw [hqeq, Nat.cast_sub (by omega : s ≤ d + 1)]
    push_cast
    nlinarith
  rw [HoldsWithFailureAtMost] at hgeneric ⊢
  refine hgeneric.trans (probabilityOf_mono _ ?_)
  intro W hW G hGαπ hGδ hGπ hGρ hGζ hG S hS hSweight
  obtain ⟨v, hv, Q, hQ, hc, hu, he, hl⟩ := hW G hGαπ hGδ hGπ hGρ hGζ hG S hS hSweight
  exact ⟨v, hv, Q, hQ, hc, hu, he, hlength.trans hl⟩

end ProofOfSpaceStatement

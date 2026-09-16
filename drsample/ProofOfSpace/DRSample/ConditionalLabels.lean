import ProofOfSpace.DRSample.DiscreteLaw
import ProofOfSpace.DRSample.GeneralMultiscale

/-! The paper's conditional-height hypothesis, allowing arbitrary discrete
joint distributions and unbounded positive integer labels. -/
namespace ProofOfSpace.DRSample
open Finset Classical ProofOfSpaceStatement
variable {n : ℕ}

noncomputable def heightMass (S : Finset (Fin n)) (j : Fin n) (past : Fin n → ℕ)
    (k : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => i ∉ S ∧ i < j ∧ k ≤ past i), (1 : ℝ) / (j.val - i.val : ℕ)

theorem heightMass_nonneg (S : Finset (Fin n)) (j : Fin n) (past : Fin n → ℕ) (k : ℕ) :
    0 ≤ heightMass S j past k := sum_nonneg fun _ _ => by positivity

theorem heightMass_le (S : Finset (Fin n)) (j : Fin n) (past : Fin n → ℕ) (k : ℕ) :
    heightMass S j past k ≤ n := by
  calc _ ≤ ∑ i ∈ univ.filter (fun i => i ∉ S ∧ i < j ∧ k ≤ past i), (1 : ℝ) := by
          apply sum_le_sum
          intro i hi
          have hij := (mem_filter.mp hi).2.2.1
          have hd : (1 : ℝ) ≤ (j.val - i.val : ℕ) := by exact_mod_cast (show 1 ≤ j.val - i.val by omega)
          simpa using one_div_le_one_div_of_le (by norm_num) hd
    _ ≤ n := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (show (univ.filter (fun i : Fin n => i ∉ S ∧ i < j ∧ k ≤ past i)).card ≤ n from
        (card_le_card (filter_subset _ univ)).trans_eq (by simp))

theorem heightMass_zero_of_large (S : Finset (Fin n)) (j : Fin n) (past : Fin n → ℕ)
    {k : ℕ} (hk : univ.sup past < k) : heightMass S j past k = 0 := by
  apply sum_eq_zero
  intro i hi
  have hle := Finset.le_sup (f := past) (mem_univ i)
  have hge := (mem_filter.mp hi).2.2.2
  omega

/-- The maximal integer threshold transfers a height tail to a mass tail. -/
theorem heightMass_tail (q : DiscreteLaw (LabelArray n)) (S : Finset (Fin n))
    (j : Fin n) (past : Fin n → ℕ) {lambda : ℝ} (hlambda : 0 < lambda)
    (hpositive : ∀ h, q.weight h ≠ 0 → 0 < h S j)
    (hheight : ∀ k : ℕ, 0 < k → q.probability (fun h => h S j ≤ k) ≤
      Real.exp (-lambda * heightMass S j past k)) {t : ℝ} (ht : 0 < t) :
    q.probability (fun h => t ≤ heightMass S j past (h S j)) ≤ Real.exp (-lambda * t) := by
  let bad := (range (univ.sup past + 1)).filter fun k => 0 < k ∧ t ≤ heightMass S j past k
  have hin (h : LabelArray n) (hw : q.weight h ≠ 0)
      (hm : t ≤ heightMass S j past (h S j)) : h S j ∈ bad := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, hpositive h hw, hm⟩
    by_contra! hh
    have hz := heightMass_zero_of_large S j past (by omega : univ.sup past < h S j)
    linarith
  rcases bad.eq_empty_or_nonempty with he | hne
  · have hp : q.probability (fun h => t ≤ heightMass S j past (h S j)) ≤ q.probability (fun _ => False) := by
      apply q.probability_mono_on_weight
      intro h hw hm
      simpa [he] using hin h hw hm
    simp [DiscreteLaw.probability] at hp
    exact hp.trans (Real.exp_pos _).le
  · obtain ⟨k, hk, hmax⟩ := bad.exists_max_image id hne
    have hkpos := (mem_filter.mp hk).2.1
    have hkmass := (mem_filter.mp hk).2.2
    calc _ ≤ q.probability (fun h => h S j ≤ k) :=
          q.probability_mono_on_weight (fun h hw hm => hmax _ (hin h hw hm))
      _ ≤ Real.exp (-lambda * heightMass S j past k) := hheight k hkpos
      _ ≤ Real.exp (-lambda * t) := Real.exp_le_exp.mpr (by nlinarith)

abbrev LabelHistory (S : Finset (Fin n)) (j : Fin n) :=
  {i : Fin n // i ∉ S ∧ i < j} → ℕ

def labelHistory (S : Finset (Fin n)) (j : Fin n) (h : Fin n → ℕ) : LabelHistory S j :=
  fun i => h i.val

noncomputable def extendHistory (S : Finset (Fin n)) (j : Fin n) (b : LabelHistory S j) : Fin n → ℕ :=
  fun i => if hi : i ∉ S ∧ i < j then b ⟨i, hi⟩ else 0

theorem history_eq_iff (S : Finset (Fin n)) (j : Fin n) (b : LabelHistory S j) (h : LabelArray n) :
    labelHistory S j (h S) = b ↔ EarlierLabels S j (extendHistory S j b) h := by
  constructor
  · intro he i hi hij
    have hh := congrFun he ⟨i, hi, hij⟩
    simpa [labelHistory, extendHistory, hi, hij] using hh
  · intro he
    funext i
    simpa [labelHistory, extendHistory, i.property] using he i i.property.1 i.property.2

theorem heightMass_history (S : Finset (Fin n)) (j : Fin n) (past h : Fin n → ℕ)
    (heq : ∀ i, i ∉ S → i < j → h i = past i) (k : ℕ) :
    heightMass S j h k = heightMass S j past k := by
  unfold heightMass
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  by_cases hi : i ∉ S ∧ i < j
  · simp [hi.1, hi.2, heq i hi.1 hi.2]
  · tauto

/-- A fixed history satisfies the same factor-two exponential moment bound. -/
theorem conditional_label_moment (p : PMF (LabelArray n)) {lambda : ℝ} (hlambda : 0 < lambda)
    (hpositive : ∀ h ∈ p.support, ∀ S j, j ∉ S → 0 < h S j)
    (hheight : ConditionalHeightBound p lambda) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (b : LabelHistory S j) :
    (∑' h, if labelHistory S j (h S) = b then
      (DiscreteLaw.ofPMF p).weight h * Real.exp (lambda / 2 * heightMass S j (h S) (h S j)) else 0) ≤
      2 * (DiscreteLaw.ofPMF p).probability (fun h => labelHistory S j (h S) = b) := by
  let q := DiscreteLaw.ofPMF p
  let Q := fun h : LabelArray n => labelHistory S j (h S) = b
  let past := extendHistory S j b
  have hQ : ∀ h, Q h ↔ EarlierLabels S j past h := history_eq_iff S j b
  have hpQ : q.probability Q = labelProbability p (EarlierLabels S j past) := by
    rw [DiscreteLaw.probability_ofPMF]
    congr 2
    ext h
    exact hQ h
  rcases eq_or_lt_of_le (q.probability_nonneg Q) with hz | hpos
  · have hz' := hz.symm
    have hh : (∑' h, if Q h then q.weight h * Real.exp (lambda / 2 * heightMass S j (h S) (h S j)) else 0) = 0 := by
      have hzterm (h : LabelArray n) : (if Q h then q.weight h * Real.exp (lambda / 2 * heightMass S j (h S) (h S j)) else 0) = 0 := by
        by_cases hh : Q h
        · simp [hh, q.weight_eq_zero_of_probability_eq_zero Q hz' hh]
        · simp [hh]
      simp only [hzterm, tsum_zero]
    change _ ≤ 2 * q.probability Q
    rw [hz', mul_zero]
    exact hh.le
  · let r := q.condition Q hpos
    have hwt (h : LabelArray n) (hw : r.weight h ≠ 0) : Q h ∧ h ∈ p.support := by
      have hq : Q h := by
        by_contra hn
        exact hw (by simp [r, DiscreteLaw.condition, hn])
      refine ⟨hq, ?_⟩
      change p h ≠ 0
      intro hz
      apply hw
      simp [r, DiscreteLaw.condition, q, DiscreteLaw.ofPMF, hz]
    have htail (k : ℕ) (hk : 0 < k) : r.probability (fun h => h S j ≤ k) ≤
        Real.exp (-lambda * heightMass S j past k) := by
      rw [DiscreteLaw.probability_condition, div_le_iff₀ hpos]
      have hh := hheight S j hj past (hpQ ▸ hpos) k hk
      rw [← hpQ] at hh
      have hevent : q.probability (fun h => Q h ∧ h S j ≤ k) =
          labelProbability p (fun h => EarlierLabels S j past h ∧ h S j ≤ k) := by
        rw [DiscreteLaw.probability_ofPMF]
        congr 2
        ext h
        exact and_congr_left fun _ => hQ h
      rw [hevent]
      exact hh
    have hm := r.expectation_exp_le_two_of_tail (fun h => heightMass S j past (h S j)) lambda hlambda
      (fun h => heightMass_nonneg S j past (h S j))
      (fun t ht => heightMass_tail r S j past hlambda
        (fun h hw => hpositive h (hwt h hw).2 S j hj) htail ht)
    have heq : r.expectation (fun h => Real.exp (lambda / 2 * heightMass S j (h S) (h S j))) =
        r.expectation (fun h => Real.exp (lambda / 2 * heightMass S j past (h S j))) := by
      apply tsum_congr
      intro h
      by_cases hw : r.weight h = 0
      · simp [hw]
      · dsimp only
        rw [heightMass_history S j past (h S) ((hQ h).mp (hwt h hw).1)]
    change (∑' h, if Q h then q.weight h * _ else 0) ≤ 2 * q.probability Q
    have ha := q.atom_expectation Q (fun h => Real.exp (lambda / 2 * heightMass S j (h S) (h S j))) hpos
    have hb : q.probability Q * r.expectation (fun h => Real.exp (lambda / 2 * heightMass S j (h S) (h S j))) ≤
        2 * q.probability Q := by
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_left hm hpos.le]
    calc
      _ = q.probability Q * r.expectation (fun h => Real.exp (lambda / 2 * heightMass S j (h S) (h S j))) := by
        change _ = q.probability Q * (q.condition Q hpos).expectation _
        rw [← ha]
        apply tsum_congr
        intro h
        by_cases hh : Q h <;> simp [hh]
      _ ≤ _ := hb

noncomputable def labelPrefix (S : Finset (Fin n)) (h : Fin n → ℕ) (t : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j => j.val < t ∧ j ∉ S), heightMass S j h (h j)

theorem labelPrefix_nonneg (S : Finset (Fin n)) (h : Fin n → ℕ) (t : ℕ) :
    0 ≤ labelPrefix S h t := sum_nonneg fun j _ => heightMass_nonneg S j h (h j)

theorem labelPrefix_le (S : Finset (Fin n)) (h : Fin n → ℕ) (t : ℕ) :
    labelPrefix S h t ≤ (n : ℝ) * n := by
  calc _ ≤ ∑ j ∈ univ.filter (fun j => j.val < t ∧ j ∉ S), (n : ℝ) :=
          sum_le_sum fun j _ => heightMass_le S j h (h j)
    _ ≤ (n : ℝ) * n := by
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (univ.filter (fun j : Fin n => j.val < t ∧ j ∉ S)).card ≤ n from
        (card_le_card (filter_subset _ univ)).trans_eq (by simp))

theorem labelPrefix_agree (S : Finset (Fin n)) (h g : Fin n → ℕ) (t : ℕ)
    (heq : ∀ i, i ∉ S → i.val < t → h i = g i) : labelPrefix S h t = labelPrefix S g t := by
  apply sum_congr rfl
  intro j hj
  obtain ⟨hjt, hjS⟩ := (mem_filter.mp hj).2
  rw [heq j hjS hjt]
  exact heightMass_history S j g h (fun i hi hij => heq i hi (by exact lt_trans hij hjt)) _

theorem labelPrefix_history (S : Finset (Fin n)) (j : Fin n) (h : Fin n → ℕ) :
    labelPrefix S (extendHistory S j (labelHistory S j h)) j.val = labelPrefix S h j.val := by
  apply labelPrefix_agree
  intro i hi hij
  simp [extendHistory, labelHistory, hi, show i < j from hij]

theorem prefix_filter_succ (S : Finset (Fin n)) {t : ℕ} (ht : t < n) :
    univ.filter (fun j : Fin n => j.val < t + 1 ∧ j ∉ S) =
      if (⟨t, ht⟩ : Fin n) ∈ S then univ.filter (fun j => j.val < t ∧ j ∉ S)
      else insert ⟨t, ht⟩ (univ.filter (fun j => j.val < t ∧ j ∉ S)) := by
  split_ifs with hS
  · ext j
    simp only [mem_filter, mem_univ, true_and]
    have he : j.val = t → j ∈ S := fun hh => (show j = ⟨t, ht⟩ from Fin.ext hh).symm ▸ hS
    constructor <;> rintro ⟨hjt, hjS⟩
    · have hne : j.val ≠ t := fun hh => hjS (he hh)
      exact ⟨by omega, hjS⟩
    · exact ⟨by omega, hjS⟩
  · ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    constructor
    · rintro ⟨hjt, hjS⟩
      by_cases he : j.val = t
      · exact Or.inl he
      · exact Or.inr ⟨by omega, hjS⟩
    · rintro (he | ⟨hjt, hjS⟩)
      · have hj : j = ⟨t, ht⟩ := Fin.ext he
        subst j
        exact ⟨by omega, hS⟩
      · exact ⟨by omega, hjS⟩

theorem labelPrefix_succ (S : Finset (Fin n)) (h : Fin n → ℕ) {t : ℕ} (ht : t < n) :
    labelPrefix S h (t + 1) = labelPrefix S h t +
      if (⟨t, ht⟩ : Fin n) ∈ S then 0 else heightMass S ⟨t, ht⟩ h (h ⟨t, ht⟩) := by
  unfold labelPrefix
  rw [prefix_filter_succ S ht]
  split_ifs with hS
  · simp
  · rw [sum_insert (by simp)]
    ring

theorem labelPrefix_summable (p : DiscreteLaw (LabelArray n)) (S : Finset (Fin n))
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (t : ℕ) :
    Summable (fun h => p.weight h * Real.exp (lambda / 2 * labelPrefix S (h S) t)) :=
  p.summable_bounded (fun _ => (Real.exp_pos _).le)
    (fun h => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (labelPrefix_le S (h S) t) (by positivity)))

theorem labelPrefix_moment (p : PMF (LabelArray n)) {lambda : ℝ} (hlambda : 0 < lambda)
    (hpositive : ∀ h ∈ p.support, ∀ S j, j ∉ S → 0 < h S j)
    (hheight : ConditionalHeightBound p lambda) (S : Finset (Fin n)) (t : ℕ) (ht : t ≤ n) :
    (DiscreteLaw.ofPMF p).expectation (fun h => Real.exp (lambda / 2 * labelPrefix S (h S) t)) ≤
      2 ^ (univ.filter (fun j : Fin n => j.val < t ∧ j ∉ S)).card := by
  induction t with
  | zero => simp [labelPrefix, DiscreteLaw.expectation, DiscreteLaw.total]
  | succ t ih =>
    have htn : t < n := by omega
    have ih := ih (by omega)
    let j : Fin n := ⟨t, htn⟩
    rw [prefix_filter_succ S htn]
    simp_rw [labelPrefix_succ S _ htn]
    by_cases hj : j ∈ S
    · simpa [show (⟨t, htn⟩ : Fin n) ∈ S from hj] using ih
    · simp only [show ¬ (⟨t, htn⟩ : Fin n) ∈ S from hj, if_false]
      rw [card_insert_of_notMem (by simp [j]), pow_succ]
      let key := fun h : LabelArray n => labelHistory S j (h S)
      let F := fun b : LabelHistory S j => Real.exp (lambda / 2 * labelPrefix S (extendHistory S j b) t)
      let g := fun h : LabelArray n => Real.exp (lambda / 2 * heightMass S j (h S) (h S j))
      have hF (h : LabelArray n) : F (key h) = Real.exp (lambda / 2 * labelPrefix S (h S) t) := by
        exact congrArg (fun x => Real.exp (lambda / 2 * x)) (labelPrefix_history S j (h S))
      have hprod (h : LabelArray n) : F (key h) * g h =
          Real.exp (lambda / 2 * labelPrefix S (h S) (t + 1)) := by
        rw [hF, ← Real.exp_add, labelPrefix_succ S _ htn, if_neg hj]
        congr 1
        ring
      have hsum := (labelPrefix_summable (DiscreteLaw.ofPMF p) S hlambda.le (t + 1)).congr
        (fun h => congrArg ((DiscreteLaw.ofPMF p).weight h * ·) (hprod h).symm)
      have hprev := (labelPrefix_summable (DiscreteLaw.ofPMF p) S hlambda.le t).congr
        (fun h => congrArg ((DiscreteLaw.ofPMF p).weight h * ·) (hF h).symm)
      have hstep := (DiscreteLaw.ofPMF p).expectation_mul_le key F g 2 (fun _ => (Real.exp_pos _).le)
        hsum hprev (fun b => by simpa only [key, g] using conditional_label_moment p hlambda hpositive hheight S j hj b)
      simp_rw [hprod, hF] at hstep
      have hstep := hstep.trans (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2))
      simpa only [labelPrefix_succ S _ htn, if_neg (show (⟨t, htn⟩ : Fin n) ∉ S from hj), mul_comm] using hstep

noncomputable def naturalLabels (h : Fin n → ℕ) : ℕ → ℕ :=
  fun i => if hi : i < n then h ⟨i, hi⟩ else 0

@[simp] theorem naturalLabels_fin (h : Fin n → ℕ) (i : Fin n) :
    naturalLabels h i.val = h i := by simp [naturalLabels, i.isLt]

theorem survivors_image (S : Finset (Fin n)) :
    (univ.filter (fun i => i ∉ S)).image Fin.val = range n \ natDeleted S := by
  ext i
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_sdiff, mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isLt, by simpa using hv⟩
  · rintro ⟨hi, hS⟩
    exact ⟨⟨i, hi⟩, (mem_natDeleted S ⟨i, hi⟩).not.mp hS, rfl⟩

theorem labelPrefix_mass (S : Finset (Fin n)) (h : Fin n → ℕ) :
    labelPrefix S h n = forbiddenMass (range n \ natDeleted S) (naturalLabels h) := by
  have hf : univ.filter (fun j : Fin n => j.val < n ∧ j ∉ S) = univ.filter (fun j => j ∉ S) := by
    ext j
    simp [j.isLt]
  rw [labelPrefix, hf, forbiddenMass, ← survivors_image, sum_image (Fin.val_injective.injOn)]
  apply sum_congr rfl
  intro j hj
  rw [sum_image (Fin.val_injective.injOn)]
  simp only [heightMass, sum_filter, pairMass, naturalLabels_fin]
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∉ S <;> by_cases hij : i < j <;> by_cases hh : h j ≤ h i <;>
    simp [hi, hij, hh, show (i.val < j.val) ↔ i < j from Iff.rfl]

end ProofOfSpace.DRSample

namespace ProofOfSpaceStatement
open Finset Classical ProofOfSpace.DRSample

/-- `thm:multiscale`: arbitrary joint positive integer labels satisfying the
conditional-height bound, uniformly over all deletion sets. -/
theorem conditional_multiscale {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ lambda : ℝ, 0 < lambda →
      ∀ p : PMF (LabelArray n),
      (∀ h ∈ p.support, ∀ S j, j ∉ S → 0 < h S j) → ConditionalHeightBound p lambda →
      labelProbability p (fun h => ∀ S : Finset (Fin n), (S.card : ℝ) ≤ α * n →
        (n : ℝ) / c * Real.exp (-c / lambda) ≤
          ((univ.filter (fun j => j ∉ S)).sup (h S) : ℕ)) ≥
        1 - Real.exp (-(2 - Real.log 3) * n) := by
  obtain ⟨c, hc, hlabels⟩ := shallow_labels_fraction hα hα1
  refine ⟨4 * c, by positivity, ?_⟩
  intro n hn lambda hlambda p hpositive hheight
  let q := DiscreteLaw.ofPMF p
  have hmoment (S : Finset (Fin n)) : q.expectation (fun h => Real.exp (lambda / 2 * labelPrefix S (h S) n)) ≤
      2 ^ (n - S.card) := by
    have hh := labelPrefix_moment p hlambda hpositive hheight S n le_rfl
    have heq : univ.filter (fun j : Fin n => j.val < n ∧ j ∉ S) = univ \ S := by
      ext j
      simp [j.isLt]
    have hcard : (univ.filter (fun j : Fin n => j.val < n ∧ j ∉ S)).card = n - S.card := by
      rw [heq, card_sdiff]
      simp
    rwa [hcard] at hh
  have hmass := q.uniform_mass_bound n lambda hlambda (fun S h => labelPrefix S (h S) n)
    (fun S => labelPrefix_summable q S hlambda.le n) hmoment
  unfold labelProbability
  rw [← DiscreteLaw.probability_ofPMF]
  apply hmass.trans
  apply q.probability_mono_on_weight
  intro h hw hbound S hS
  have hsupport : h ∈ p.support := by
    change p h ≠ 0
    intro hz
    exact hw (by simp [q, DiscreteLaw.ofPMF, hz])
  let d := (univ.filter (fun j : Fin n => j ∉ S)).sup (h S)
  have hsmall : ((natDeleted S).card : ℝ) ≤ α * n := by simpa using hS
  have hh : ∀ i ∈ range n \ natDeleted S, 1 ≤ naturalLabels (h S) i ∧ naturalLabels (h S) i ≤ d := by
    intro i hi
    have hin := mem_range.mp (mem_sdiff.mp hi).1
    let v : Fin n := ⟨i, hin⟩
    have hv : v ∉ S := (mem_natDeleted S v).not.mp (mem_sdiff.mp hi).2
    have heq : naturalLabels (h S) i = h S v := naturalLabels_fin (h S) v
    rw [heq]
    exact ⟨hpositive h hsupport S v hv, Finset.le_sup (mem_filter.mpr ⟨mem_univ v, hv⟩)⟩
  have hshallow := hlabels n d hn (natDeleted S) (natDeleted_subset S) hsmall (naturalLabels (h S)) hh
  rw [← labelPrefix_mass] at hshallow
  apply le_trans ?_ hshallow
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : -(4 * c) / lambda ≤ -c * labelPrefix S (h S) n / n := by
    apply (div_le_div_iff₀ hlambda hn0).mpr
    have hb := (le_div_iff₀ hlambda).mp (hbound S)
    nlinarith [mul_le_mul_of_nonneg_left hb hc.le]
  apply mul_le_mul _ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  apply div_le_div_of_nonneg_left hn0.le hc
  linarith

end ProofOfSpaceStatement

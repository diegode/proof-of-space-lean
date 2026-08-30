/-
# Blockable and expandable levels, and the fertile–expandable search

This file formalizes the search behind `first-source lemma` of this development.

`search_bound` is the reusable core.  It runs the development's search, forward in depth — one
level at an infertile level, a whole blocked range at a fertile blockable level — and
returns the two capacities the development adds: the number `I` of single-level skips (each at
a distinct infertile depth) and the number `Q` of levels inside blocked ranges (whose
*disjoint* spends exceed `Q g`).  Both `first-source lemma` and
`fertile-continuation lemma` are instances; they differ only in how `I` is bounded.
-/
import ProofOfSpace.Footprint

namespace ProofOfSpace

open Finset

variable {S : Setting}

/-- `expandability condition`: depth `t` is `g`-*expandable* when, for every window of `i` levels
immediately below it, the black-pebble spend is at most `(i+1) g`. -/
def Expandable (B : Budget S) (g : ℝ) (t : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → ∑ m ∈ Finset.range i, B.spend (t + m + 1) ≤ ((i : ℝ) + 1) * g

/-- `expandability condition`: depth `t` is `g`-*blockable* when some window immediately below it
carries more than `g` pebbles per level on average. -/
def Blockable (B : Budget S) (g : ℝ) (t : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ((k : ℝ) + 1) * g < ∑ m ∈ Finset.range k, B.spend (t + m + 1)

theorem not_expandable_iff_blockable (B : Budget S) (g : ℝ) (t : ℕ) :
    ¬ Expandable B g t ↔ Blockable B g t := by
  constructor
  · intro h
    by_contra hb
    exact h fun i hi => by
      by_contra hlt
      exact hb ⟨i, hi, not_le.mp hlt⟩
  · rintro ⟨k, hk1, hk2⟩ hexp
    exact absurd (hexp k hk1) (not_le.mpr hk2)

/-- The length of the blocked range witnessed at a blockable depth. -/
noncomputable def blockLen (B : Budget S) (g : ℝ) (t : ℕ) : ℕ :=
  open Classical in
  if h : Blockable B g t then h.choose else 1

theorem blockLen_spec {B : Budget S} {g : ℝ} {t : ℕ} (h : Blockable B g t) :
    1 ≤ blockLen B g t ∧
      ((blockLen B g t : ℝ) + 1) * g <
        ∑ m ∈ Finset.range (blockLen B g t), B.spend (t + m + 1) := by
  classical
  simp only [blockLen, dif_pos h]
  exact h.choose_spec

/-! ### The search -/

section Search

variable (B : Budget S) (g : ℝ) (Fert : ℕ → Prop) [DecidablePred Fert] (t : ℕ)

/-- Position of the search after `j` steps. -/
noncomputable def searchPos : ℕ → ℕ
  | 0 => t
  | j + 1 =>
      let p := searchPos j
      if Fert p then p + blockLen B g p + 1 else p + 1

/-- Number of single-level (infertile) skips among the first `j` steps. -/
noncomputable def searchI : ℕ → ℕ
  | 0 => 0
  | j + 1 => if Fert (searchPos B g Fert t j) then searchI j else searchI j + 1

/-- Total number of levels inside blocked ranges among the first `j` steps. -/
noncomputable def searchQ : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      let p := searchPos B g Fert t j
      if Fert p then searchQ j + blockLen B g p + 1 else searchQ j

variable {B g Fert t}

theorem searchPos_zero : searchPos B g Fert t 0 = t := rfl

theorem searchPos_succ (j : ℕ) :
    searchPos B g Fert t (j + 1) =
      if Fert (searchPos B g Fert t j) then
        searchPos B g Fert t j + blockLen B g (searchPos B g Fert t j) + 1
      else searchPos B g Fert t j + 1 := rfl

theorem searchI_succ (j : ℕ) :
    searchI B g Fert t (j + 1) =
      if Fert (searchPos B g Fert t j) then searchI B g Fert t j
      else searchI B g Fert t j + 1 := rfl

theorem searchQ_succ (j : ℕ) :
    searchQ B g Fert t (j + 1) =
      if Fert (searchPos B g Fert t j) then
        searchQ B g Fert t j + blockLen B g (searchPos B g Fert t j) + 1
      else searchQ B g Fert t j := rfl

/-- The search position is the sum of the two capacities consumed so far. -/
theorem searchPos_eq (j : ℕ) :
    searchPos B g Fert t j = t + searchI B g Fert t j + searchQ B g Fert t j := by
  induction j with
  | zero => simp [searchPos_zero, searchI, searchQ]
  | succ j ih =>
      rw [searchPos_succ, searchI_succ, searchQ_succ]
      by_cases h : Fert (searchPos B g Fert t j) <;> simp only [h, if_true, if_false] <;> omega

theorem searchPos_lt_succ (j : ℕ) : searchPos B g Fert t j < searchPos B g Fert t (j + 1) := by
  rw [searchPos_succ]
  by_cases h : Fert (searchPos B g Fert t j) <;> simp only [h, if_true, if_false] <;> omega

theorem searchPos_mono : Monotone (searchPos B g Fert t) := by
  refine monotone_nat_of_le_succ fun j => ?_
  exact (searchPos_lt_succ j).le

theorem le_searchPos (j : ℕ) : t + j ≤ searchPos B g Fert t j := by
  induction j with
  | zero => simp [searchPos_zero]
  | succ j ih => have := searchPos_lt_succ (B := B) (g := g) (Fert := Fert) (t := t) j; omega

theorem base_le_searchPos (j : ℕ) : t ≤ searchPos B g Fert t j := by
  have := le_searchPos (B := B) (g := g) (Fert := Fert) (t := t) j; omega

/-- The spend accumulated strictly below the base by the first `j` steps. -/
noncomputable def searchSpend (j : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico (t + 1) (searchPos B g Fert t j), B.spend d

theorem searchSpend_mono {i j : ℕ} (hij : i ≤ j) :
    searchSpend (B := B) (g := g) (Fert := Fert) (t := t) i ≤
      searchSpend (B := B) (g := g) (Fert := Fert) (t := t) j := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => B.spend_nonneg d
  intro d hd
  simp only [Finset.mem_Ico] at hd ⊢
  exact ⟨hd.1, lt_of_lt_of_le hd.2 (searchPos_mono hij)⟩

/-- The blocked-range capacity is paid for by disjoint spends.

The hypothesis is imposed only at the *search positions* strictly before the stopping
index `J`; this is what allows the same lemma to serve both `first-source lemma`, where the
search is stopped by a level budget, and `fertile-continuation lemma`, where it is stopped by the
first fertile expandable level it meets. -/
theorem searchQ_spend {J : ℕ}
    (hbad : ∀ j, j < J →
      ¬(Fert (searchPos B g Fert t j) ∧ Expandable B g (searchPos B g Fert t j))) :
    ∀ j ≤ J,
      ((searchQ B g Fert t j : ℝ) * g
          ≤ searchSpend (B := B) (g := g) (Fert := Fert) (t := t) j) ∧
      (0 < searchQ B g Fert t j →
        (searchQ B g Fert t j : ℝ) * g
          < searchSpend (B := B) (g := g) (Fert := Fert) (t := t) j) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · simp only [searchQ, Nat.cast_zero, zero_mul]
        exact Finset.sum_nonneg fun d _ => B.spend_nonneg d
      · simp [searchQ]
  | succ j ih =>
      intro hj
      have hjJ : j < J := by omega
      have ihj := ih (by omega)
      set p := searchPos B g Fert t j with hp
      by_cases hF : Fert p
      · -- fertile, hence blockable: the block pays for its own levels
        have hpt : t ≤ p := base_le_searchPos j
        have hblock : Blockable B g p :=
          (not_expandable_iff_blockable B g p).mp fun hexp => hbad j hjJ ⟨hF, hexp⟩
        obtain ⟨hk1, hkspend⟩ := blockLen_spec hblock
        set k := blockLen B g p with hk
        have hshift : ∑ m ∈ Finset.range k, B.spend (p + m + 1)
            = ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d := B.sum_shift p k
        have hdisj : Disjoint (Finset.Ico (t + 1) p) (Finset.Ico (p + 1) (p + k + 1)) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          simp only [Finset.mem_Ico] at ha hb
          omega
        have hsubset : (Finset.Ico (t + 1) p) ∪ (Finset.Ico (p + 1) (p + k + 1))
            ⊆ Finset.Ico (t + 1) (p + k + 1) := by
          intro a ha
          simp only [Finset.mem_union, Finset.mem_Ico] at ha ⊢
          omega
        have hss : searchSpend (B := B) (g := g) (Fert := Fert) (t := t) j
            = ∑ d ∈ Finset.Ico (t + 1) p, B.spend d := by
          simp only [searchSpend, ← hp]
        have hsplit : searchSpend (B := B) (g := g) (Fert := Fert) (t := t) j
              + ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d
            ≤ ∑ d ∈ Finset.Ico (t + 1) (p + k + 1), B.spend d := by
          rw [hss, ← Finset.sum_union hdisj]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun d _ _ => B.spend_nonneg d
        have hnext : searchPos B g Fert t (j + 1) = p + k + 1 := by
          rw [searchPos_succ]; simp only [← hp, hF, if_true, ← hk]
        have hQnext : searchQ B g Fert t (j + 1) = searchQ B g Fert t j + k + 1 := by
          rw [searchQ_succ]; simp only [← hp, hF, if_true, ← hk]
        have hspendnext : searchSpend (B := B) (g := g) (Fert := Fert) (t := t) (j + 1)
            = ∑ d ∈ Finset.Ico (t + 1) (p + k + 1), B.spend d := by
          simp only [searchSpend, hnext]
        have hstrict : (searchQ B g Fert t (j + 1) : ℝ) * g <
            searchSpend (B := B) (g := g) (Fert := Fert) (t := t) (j + 1) := by
          rw [hQnext, hspendnext]
          push_cast
          have h1 := ihj.1
          have h2 : ((k : ℝ) + 1) * g < ∑ d ∈ Finset.Ico (p + 1) (p + k + 1), B.spend d := by
            rw [← hshift]; exact hkspend
          nlinarith [h1, h2, hsplit]
        exact ⟨hstrict.le, fun _ => hstrict⟩
      · -- infertile: nothing is charged, and the accumulated spend cannot decrease
        have hnext : searchPos B g Fert t (j + 1) = p + 1 := by
          rw [searchPos_succ]; simp only [← hp, hF, if_false]
        have hQnext : searchQ B g Fert t (j + 1) = searchQ B g Fert t j := by
          rw [searchQ_succ]; simp only [← hp, hF, if_false]
        have hmono := searchSpend_mono (B := B) (g := g) (Fert := Fert) (t := t)
          (Nat.le_succ j)
        rw [hQnext]
        exact ⟨le_trans ihj.1 hmono, fun h => lt_of_lt_of_le (ihj.2 h) hmono⟩

/-- Each single-level skip happens at a distinct infertile depth. -/
theorem searchI_card (j : ℕ) :
    searchI B g Fert t j ≤
      ((Finset.Ico t (searchPos B g Fert t j)).filter (fun d => ¬ Fert d)).card := by
  induction j with
  | zero => simp [searchI]
  | succ j ih =>
      set p := searchPos B g Fert t j with hp
      by_cases hF : Fert p
      · have hI : searchI B g Fert t (j + 1) = searchI B g Fert t j := by
          rw [searchI_succ]; simp only [← hp, hF, if_true]
        have hsub : (Finset.Ico t p).filter (fun d => ¬ Fert d)
            ⊆ (Finset.Ico t (searchPos B g Fert t (j + 1))).filter (fun d => ¬ Fert d) := by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_Ico] at hd ⊢
          exact ⟨⟨hd.1.1, lt_of_lt_of_le hd.1.2 (searchPos_mono (Nat.le_succ j))⟩, hd.2⟩
        rw [hI]
        exact le_trans ih (Finset.card_le_card hsub)
      · have hI : searchI B g Fert t (j + 1) = searchI B g Fert t j + 1 := by
          rw [searchI_succ]; simp only [← hp, hF, if_false]
        have hnext : searchPos B g Fert t (j + 1) = p + 1 := by
          rw [searchPos_succ]; simp only [← hp, hF, if_false]
        have hpt : t ≤ p := base_le_searchPos j
        have hins : (Finset.Ico t (p + 1)).filter (fun d => ¬ Fert d)
            = insert p ((Finset.Ico t p).filter (fun d => ¬ Fert d)) := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            rcases Nat.lt_or_ge d p with h | h
            · exact Or.inr ⟨⟨h1, h⟩, h3⟩
            · exact Or.inl (by omega)
          · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
            · exact ⟨⟨hpt, by omega⟩, hF⟩
            · exact ⟨⟨h1, by omega⟩, h3⟩
        have hnotmem : p ∉ (Finset.Ico t p).filter (fun d => ¬ Fert d) := by
          simp only [Finset.mem_filter, Finset.mem_Ico]
          omega
        rw [hI, hnext, hins, Finset.card_insert_of_notMem hnotmem]
        omega

/-- Refinement of `searchI_card` that charges the final step explicitly: every single-level
skip among the first `j + 1` steps happens at a depth at most `searchPos j`.

This is what lets the infertile count be bounded by a window that stops *before* the
search's last jump.  A search may overshoot its stopping bound by a whole blocked range,
and
in the general regime the footprint-bound hypotheses are unpebbled only up to that bound. -/
theorem searchI_card_succ (j : ℕ) :
    searchI B g Fert t (j + 1) ≤
      ((Finset.Ico t (searchPos B g Fert t j + 1)).filter (fun d => ¬ Fert d)).card := by
  set p := searchPos B g Fert t j with hp
  by_cases hF : Fert p
  · have hI : searchI B g Fert t (j + 1) = searchI B g Fert t j := by
      rw [searchI_succ]; simp only [← hp, hF, if_true]
    rw [hI]
    refine le_trans (searchI_card j) (Finset.card_le_card ?_)
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ico, ← hp] at hd ⊢
    exact ⟨⟨hd.1.1, by omega⟩, hd.2⟩
  · have hnext : searchPos B g Fert t (j + 1) = p + 1 := by
      rw [searchPos_succ]; simp only [← hp, hF, if_false]
    rw [← hnext]
    exact searchI_card (j + 1)

end Search

/--
**The fertile–expandable search** (`first-source lemma`).

If no depth in the window `[t, t+D]` is simultaneously fertile and `g`-expandable, then
the window is covered by `I` infertile depths and `Q` levels of *disjoint* blocked ranges,
with `D < I + Q`.  The whole search lies in `[t, P)` and its blocked spend is charged to
`[t+1, P)`.
-/
theorem search_bound {B : Budget S} {g : ℝ} (Fert : ℕ → Prop) [DecidablePred Fert] (t D : ℕ)
    (hbad : ∀ p, t ≤ p → p ≤ t + D → ¬(Fert p ∧ Expandable B g p)) :
    ∃ I Q P : ℕ, t + D < P ∧ D < I + Q ∧ P = t + I + Q ∧
      I ≤ ((Finset.Ico t P).filter (fun d => ¬ Fert d)).card ∧
      (0 < Q → (Q : ℝ) * g < ∑ d ∈ Finset.Ico (t + 1) P, B.spend d) := by
  classical
  have hex : ∃ j, t + D < searchPos B g Fert t j :=
    ⟨D + 1, lt_of_lt_of_le (by omega)
      (le_searchPos (B := B) (g := g) (Fert := Fert) (t := t) (D + 1))⟩
  set J := Nat.find hex with hJdef
  have hJspec : t + D < searchPos B g Fert t J := Nat.find_spec hex
  have hJmin : ∀ j, j < J → searchPos B g Fert t j ≤ t + D := by
    intro j hj
    have := Nat.find_min hex hj
    omega
  have hbad' : ∀ j, j < J →
      ¬(Fert (searchPos B g Fert t j) ∧ Expandable B g (searchPos B g Fert t j)) := by
    intro j hj
    exact hbad _ (base_le_searchPos j) (hJmin j hj)
  obtain ⟨hQle, hQlt⟩ := searchQ_spend hbad' J (le_refl J)
  refine ⟨searchI B g Fert t J, searchQ B g Fert t J, searchPos B g Fert t J, hJspec, ?_,
    searchPos_eq J, searchI_card J, ?_⟩
  · have := searchPos_eq (B := B) (g := g) (Fert := Fert) (t := t) J
    omega
  · intro h
    exact hQlt h

end ProofOfSpace

/-
# The reference-trajectory potential

This file defines a potential from an arbitrary finite **reference chain**

  `x 0 ≤ x 1 ≤ … ≤ x m`,   `x (k+1) ≤ β_δ (x k)`,   `x (k+1) - x k ≥ ĝ`,

and its piecewise-linear potential `refPot`, normalized so that
`refPot (x k) = k`.  The natural chain is the `β_δ` orbit of the tracking floor,
`x 0 = π̂`, `x (k+1) = β_δ (x k)`, run until it passes `π`; its bucket widths are the
gains `gain_δ (x k)`, which are at least `ĝ` exactly on `[π̂, π]` (`tracking-gain bound`),
so the width condition is automatic there and *fails* immediately above `π`.  That is
why a chain stops one step past `π` and the potential saturates at `m`.

The three properties the ledger consumes are the three `growthPot` supplies, and they
are proved from *concavity of `β_δ` alone* — no derivatives, no mean value theorem:

* `refPot_mono` — monotone;
* `refPot_lipschitz` — `1/ĝ`-Lipschitz, so one unit of black-pebble spend costs at
  most `1/ĝ` units of potential.  This is where the width condition is used, and it is
  the reason the chain may not continue above `π`;
* `refPot_step` — one free level advances the potential by one, up to the saturation
  value `m`: `min (refPot v + 1) m ≤ refPot (β_δ v)`.  The saturation is not slack —
  above `π` the footprint converges to `α_δ^max` and no potential with a finite range
  can keep gaining.

`refPot_step` factors through `bucket_shift`, the statement that the `k`-th bucket
coordinate of `v` is dominated by the `(k+1)`-st bucket coordinate of `β_δ v`.  That is
exactly the chord inequality for a concave function on `[x k, x (k+1)]`; `betaD_chord`
is the same inequality with the far endpoint left free, which is what the top bucket
needs, there being no next chain point above `x m`.

`refPot_eq_zero`, `refPot_eq_m` and `refPot_eq_of_mem` say the obvious thing — the
potential is `0` below the chain, `m` above it, and affine inside each bucket.  They are
what turns a `LedgerCert` for a concrete chain into a finite case analysis.
-/
import ProofOfSpace.Growth

namespace ProofOfSpace

open Set Finset

variable {S : Setting} {B : Budget S} {T : Tracking S}

/-! ### Clamping to the unit interval -/

private theorem clamp_mono {a b : ℝ} (hab : a ≤ b) :
    max 0 (min 1 a) ≤ max 0 (min 1 b) :=
  max_le_max le_rfl (min_le_min le_rfl hab)

private theorem clamp_nonneg (a : ℝ) : 0 ≤ max 0 (min 1 a) := le_max_left _ _

private theorem clamp_le_one (a : ℝ) : max 0 (min 1 a) ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem clamp_eq_one {a : ℝ} (ha : 1 ≤ a) : max 0 (min 1 a) = 1 := by
  rw [min_eq_left ha, max_eq_right zero_le_one]

private theorem clamp_eq_zero {a : ℝ} (ha : a ≤ 0) : max 0 (min 1 a) = 0 :=
  max_eq_left (le_trans (min_le_right _ _) ha)

/-- The unit clamp is `1`-Lipschitz. -/
private theorem clamp_diff {a b : ℝ} (hab : b ≤ a) :
    max 0 (min 1 a) - max 0 (min 1 b) ≤ a - b := by
  have hmin : min 1 a - min 1 b ≤ a - b := by
    rcases le_total a 1 with h1 | h1 <;> rcases le_total b 1 with h2 | h2
    · rw [min_eq_right h1, min_eq_right h2]
    · rw [min_eq_right h1, min_eq_left h2]; linarith
    · rw [min_eq_left h1, min_eq_right h2]; linarith
    · rw [min_eq_left h1, min_eq_left h2]; linarith
  rcases le_total (min 1 b) 0 with h | h
  · rw [max_eq_left h]
    have hb : b ≤ 0 := by
      by_contra hc
      push Not at hc
      exact absurd h (not_le.mpr (lt_min (by norm_num) hc))
    rcases le_total a 0 with ha | ha
    · rw [max_eq_left (le_trans (min_le_right _ _) ha)]; linarith
    · have : max 0 (min 1 a) ≤ a := max_le ha (min_le_right _ _)
      linarith
  · rw [max_eq_right h, max_eq_right (le_trans h (min_le_min le_rfl hab))]
    exact hmin

/-! ### Reference chains -/

/--
**A reference chain for the tracking gain.**

`x 0 … x m` climbs from at most the tracking floor to at least `π`, each step landing no
higher than one free level of the footprint recurrence would (`step`) and no shorter than
`ĝ` (`width`).  The `β_δ` orbit of `π̂` is the intended instance, and the Chung-8
specialization uses exactly that; nothing below assumes it.
-/
structure RefChain (S : Setting) (T : Tracking S) where
  /-- Number of buckets. -/
  m : ℕ
  /-- The chain points. -/
  x : ℕ → ℝ
  m_pos : 0 < m
  /-- The chain starts at or below the tracking floor. -/
  base : x 0 ≤ T.lam
  /-- Every bucket is at least `ĝ` wide: this is what makes `refPot` `1/ĝ`-Lipschitz. -/
  width : ∀ k, k < m → T.ghat ≤ x (k + 1) - x k
  /-- Every step is achievable by one free level. -/
  step : ∀ k, k < m → x (k + 1) ≤ S.betaD (x k)
  /-- The chain stays inside the unit interval, where `β_δ` is concave. -/
  mem : ∀ k, k ≤ m → x k ∈ Icc (0 : ℝ) 1
  /-- The chain reaches `π`. -/
  top : S.pi ≤ x m

namespace RefChain

variable (C : RefChain S T)

theorem width_pos {k : ℕ} (hk : k < C.m) : 0 < C.x (k + 1) - C.x k :=
  lt_of_lt_of_le T.ghat_pos (C.width k hk)

theorem x_le_succ {k : ℕ} (hk : k < C.m) : C.x k ≤ C.x (k + 1) := by
  have := C.width_pos hk
  linarith

theorem x_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ C.m) : C.x j ≤ C.x k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by omega) (by omega)) (C.x_le_succ (by omega))

/-! ### The potential -/

/-- The `k`-th bucket coordinate of `v`: the fraction of `[x k, x (k+1)]` below `v`. -/
noncomputable def bucket (k : ℕ) (v : ℝ) : ℝ :=
  max 0 (min 1 ((v - C.x k) / (C.x (k + 1) - C.x k)))

/-- The reference-trajectory potential, normalized by `refPot (x j) = j`. -/
noncomputable def refPot (v : ℝ) : ℝ := ∑ k ∈ Finset.range C.m, C.bucket k v

/-- The potential truncated to the first `j` buckets; the induction variable of the
Lipschitz proof. -/
noncomputable def refPotUpTo (j : ℕ) (v : ℝ) : ℝ := ∑ k ∈ Finset.range j, C.bucket k v

@[simp] theorem refPotUpTo_zero (v : ℝ) : C.refPotUpTo 0 v = 0 := by
  simp [refPotUpTo]

theorem refPotUpTo_succ (j : ℕ) (v : ℝ) :
    C.refPotUpTo (j + 1) v = C.refPotUpTo j v + C.bucket j v := by
  simp [refPotUpTo, Finset.sum_range_succ]

theorem refPotUpTo_m (v : ℝ) : C.refPotUpTo C.m v = C.refPot v := rfl

theorem bucket_nonneg (k : ℕ) (v : ℝ) : 0 ≤ C.bucket k v := clamp_nonneg _

theorem bucket_le_one (k : ℕ) (v : ℝ) : C.bucket k v ≤ 1 := clamp_le_one _

theorem bucket_mono {k : ℕ} (hk : k < C.m) {u v : ℝ} (huv : u ≤ v) :
    C.bucket k u ≤ C.bucket k v := by
  refine clamp_mono ?_
  rw [div_le_div_iff_of_pos_right (C.width_pos hk)]
  linarith

theorem bucket_eq_one {k : ℕ} (hk : k < C.m) {v : ℝ} (hv : C.x (k + 1) ≤ v) :
    C.bucket k v = 1 := by
  refine clamp_eq_one ?_
  rw [le_div_iff₀ (C.width_pos hk)]
  linarith

theorem bucket_eq_zero {k : ℕ} (hk : k < C.m) {v : ℝ} (hv : v ≤ C.x k) :
    C.bucket k v = 0 := by
  refine clamp_eq_zero ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (C.width_pos hk).le

theorem refPot_mono {u v : ℝ} (huv : u ≤ v) : C.refPot u ≤ C.refPot v :=
  Finset.sum_le_sum fun _k hk => C.bucket_mono (Finset.mem_range.mp hk) huv

theorem refPot_nonneg (v : ℝ) : 0 ≤ C.refPot v :=
  Finset.sum_nonneg fun k _ => C.bucket_nonneg k v

theorem refPot_le_m (v : ℝ) : C.refPot v ≤ (C.m : ℝ) := by
  calc C.refPot v ≤ ∑ _k ∈ Finset.range C.m, (1 : ℝ) :=
        Finset.sum_le_sum fun _k _ => C.bucket_le_one _k v
    _ = (C.m : ℝ) := by simp

/-- Above `x j` the first `j` buckets are all full. -/
theorem refPotUpTo_eq {j : ℕ} (hj : j ≤ C.m) {v : ℝ} (hv : C.x j ≤ v) :
    C.refPotUpTo j v = (j : ℝ) := by
  have hall : ∀ k ∈ Finset.range j, C.bucket k v = 1 := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact C.bucket_eq_one (by omega) (le_trans (C.x_mono (by omega) hj) hv)
  rw [refPotUpTo, Finset.sum_congr rfl hall]
  simp

theorem refPot_x {j : ℕ} (hj : j ≤ C.m) : C.refPot (C.x j) = (j : ℝ) := by
  have hlow : C.refPotUpTo j (C.x j) = (j : ℝ) := C.refPotUpTo_eq hj le_rfl
  have hhigh : ∀ k ∈ Finset.Ico j C.m, C.bucket k (C.x j) = 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact C.bucket_eq_zero hk.2 (C.x_mono hk.1 (by omega))
  have hsplit : C.refPot (C.x j)
      = C.refPotUpTo j (C.x j) + ∑ k ∈ Finset.Ico j C.m, C.bucket k (C.x j) := by
    rw [refPot, refPotUpTo, ← Finset.sum_range_add_sum_Ico _ hj]
  rw [hsplit, hlow, Finset.sum_congr rfl hhigh]
  simp

/-- **`refPot` is `1/ĝ`-Lipschitz.**  The buckets are disjoint and each is at least `ĝ`
wide, so an interval of length `u - v` meets them in pieces of total length `u - v`. -/
theorem refPotUpTo_lipschitz :
    ∀ j, j ≤ C.m → ∀ {u v : ℝ}, v ≤ u →
      C.refPotUpTo j u - C.refPotUpTo j v ≤ (u - v) / T.ghat := by
  intro j
  induction j with
  | zero =>
      intro _ u v huv
      simpa using div_nonneg (by linarith) T.ghat_pos.le
  | succ j ih =>
      intro hj u v huv
      have hjm : j < C.m := by omega
      have hbucket : ∀ {a b : ℝ}, b ≤ a →
          C.bucket j a - C.bucket j b ≤ (a - b) / T.ghat := by
        intro a b hba
        have hw := C.width_pos hjm
        have hstep : C.bucket j a - C.bucket j b
            ≤ (a - C.x j) / (C.x (j + 1) - C.x j)
              - (b - C.x j) / (C.x (j + 1) - C.x j) :=
          clamp_diff ((div_le_div_iff_of_pos_right hw).mpr (by linarith))
        have hcomb : (a - C.x j) / (C.x (j + 1) - C.x j)
            - (b - C.x j) / (C.x (j + 1) - C.x j)
            = (a - b) / (C.x (j + 1) - C.x j) := by
          field_simp
          ring
        rw [hcomb] at hstep
        exact hstep.trans
          (div_le_div_of_nonneg_left (by linarith) T.ghat_pos (C.width j hjm))
      rw [C.refPotUpTo_succ, C.refPotUpTo_succ]
      rcases le_total u (C.x j) with hu | hu
      · rw [C.bucket_eq_zero hjm hu, C.bucket_eq_zero hjm (huv.trans hu)]
        have := ih (by omega) huv
        linarith
      rcases le_total (C.x j) v with hv | hv
      · rw [C.refPotUpTo_eq (by omega) hv, C.refPotUpTo_eq (by omega) (hv.trans huv)]
        have := hbucket huv
        linarith
      · have hmid : C.refPotUpTo j u = (j : ℝ) := C.refPotUpTo_eq (by omega) hu
        have hxj : C.refPotUpTo j (C.x j) = (j : ℝ) := C.refPotUpTo_eq (by omega) le_rfl
        have h1 : C.refPotUpTo j (C.x j) - C.refPotUpTo j v ≤ (C.x j - v) / T.ghat :=
          ih (by omega) hv
        have h2 : C.bucket j u - C.bucket j (C.x j) ≤ (u - C.x j) / T.ghat := hbucket hu
        rw [C.bucket_eq_zero hjm le_rfl] at h2
        rw [C.bucket_eq_zero hjm hv]
        have hadd : (C.x j - v) / T.ghat + (u - C.x j) / T.ghat = (u - v) / T.ghat := by
          field_simp
          ring
        rw [hxj] at h1
        rw [hmid]
        linarith

theorem refPot_lipschitz {u v : ℝ} (huv : v ≤ u) :
    C.refPot u - C.refPot v ≤ (u - v) / T.ghat :=
  C.refPotUpTo_lipschitz C.m le_rfl huv

/-! ### Evaluating the potential

`refPot` is the piecewise-linear interpolation of `x k ↦ k`, and the three lemmas below
are the three pieces of that description: it is `0` below the chain, `m` above it, and
affine inside each bucket.  A `LedgerCert` for a concrete chain is discharged by case
analysis on which bucket a value lies in, and these are what turn each case into an
inequality between affine expressions.
-/

/-- Below the chain the potential vanishes. -/
theorem refPot_eq_zero {v : ℝ} (hv : v ≤ C.x 0) : C.refPot v = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  exact C.bucket_eq_zero (Finset.mem_range.mp hk)
    (hv.trans (C.x_mono (Nat.zero_le k) (le_of_lt (Finset.mem_range.mp hk))))

/-- Above the chain the potential saturates at `m`. -/
theorem refPot_eq_m {v : ℝ} (hv : C.x C.m ≤ v) : C.refPot v = (C.m : ℝ) :=
  C.refPotUpTo_eq le_rfl hv

/-- **Inside a bucket the potential is affine.**  This is the normalization
`refPot (x j) = j` in its local form. -/
theorem refPot_eq_of_mem {j : ℕ} (hj : j < C.m) {v : ℝ}
    (hlo : C.x j ≤ v) (hhi : v ≤ C.x (j + 1)) :
    C.refPot v = (j : ℝ) + (v - C.x j) / (C.x (j + 1) - C.x j) := by
  have hw := C.width_pos hj
  have hlow : C.refPotUpTo j v = (j : ℝ) := C.refPotUpTo_eq (by omega) hlo
  have hhigh : ∀ k ∈ Finset.Ico (j + 1) C.m, C.bucket k v = 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact C.bucket_eq_zero hk.2 (hhi.trans (C.x_mono hk.1 (by omega)))
  have hsplit : C.refPot v
      = C.refPotUpTo (j + 1) v + ∑ k ∈ Finset.Ico (j + 1) C.m, C.bucket k v := by
    rw [refPot, refPotUpTo, ← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ C.m)]
  have hmid : C.bucket j v = (v - C.x j) / (C.x (j + 1) - C.x j) := by
    have hr0 : 0 ≤ (v - C.x j) / (C.x (j + 1) - C.x j) :=
      div_nonneg (by linarith) hw.le
    have hr1 : (v - C.x j) / (C.x (j + 1) - C.x j) ≤ 1 := by
      rw [div_le_one hw]; linarith
    simp only [bucket, min_eq_right hr1, max_eq_right hr0]
  rw [hsplit, C.refPotUpTo_succ, hlow, hmid, Finset.sum_congr rfl hhigh]
  simp

end RefChain

/-! ### One free level -/

/-- `β_δ` is concave, being `β` minus a constant. -/
theorem betaD_concaveOn (S : Setting) : ConcaveOn ℝ (Icc (0 : ℝ) 1) S.betaD := by
  have h : S.betaD = S.β - fun _ : ℝ => S.δ := by
    funext x
    change S.β x - S.δ = _
    simp
  rw [h]
  exact S.β_concaveOn.sub (convexOn_const S.δ (convex_Icc 0 1))

namespace RefChain

variable (C : RefChain S T)

/--
**The chord bound for one free level.**

On the `k`-th bucket, concavity of `β_δ` prices one free level by the chord through
`(x k, x (k+1))` and `(x (k+1), xtop)`, for any `xtop` that the step from `x (k+1)` can
reach.  `bucket_shift` below is the case `xtop = x (k+2)`; the `t1` certificate of
`PotentialLedger.lean` needs the case `k + 1 = m`, where there is no next chain point and
`xtop` is supplied numerically.
-/
theorem betaD_chord {k : ℕ} (hk : k < C.m) {xtop : ℝ}
    (htop : xtop ≤ S.betaD (C.x (k + 1))) {v : ℝ}
    (hlo : C.x k ≤ v) (hhi : v ≤ C.x (k + 1)) :
    C.x (k + 1) + ((v - C.x k) / (C.x (k + 1) - C.x k)) * (xtop - C.x (k + 1))
      ≤ S.betaD v := by
  have hw := C.width_pos hk
  have hxk : C.x k ∈ Icc (0 : ℝ) 1 := C.mem k (by omega)
  have hxk1 : C.x (k + 1) ∈ Icc (0 : ℝ) 1 := C.mem (k + 1) (by omega)
  set t := (v - C.x k) / (C.x (k + 1) - C.x k) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hw.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hw]; linarith
  have hvconv : (1 - t) * C.x k + t * C.x (k + 1) = v := by
    rw [ht]; field_simp; ring
  have hconv := (betaD_concaveOn S).2 hxk hxk1
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hconv
  rw [hvconv] at hconv
  have e1 : (1 - t) * C.x (k + 1) ≤ (1 - t) * S.betaD (C.x k) :=
    mul_le_mul_of_nonneg_left (C.step k hk) (by linarith)
  have e2 : t * xtop ≤ t * S.betaD (C.x (k + 1)) :=
    mul_le_mul_of_nonneg_left htop ht0
  nlinarith

/--
**The bucket shift.**  One free level moves the `k`-th bucket coordinate into the
`(k+1)`-st.  This is the chord inequality for the concave `β_δ` on `[x k, x (k+1)]`,
combined with `x (k+1) ≤ β_δ (x k)` and `x (k+2) ≤ β_δ (x (k+1))`.
-/
theorem bucket_shift {k : ℕ} (hk : k + 1 < C.m) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    C.bucket k v ≤ C.bucket (k + 1) (S.betaD v) := by
  have hkm : k < C.m := by omega
  have hwk := C.width_pos hkm
  have hxk : C.x k ∈ Icc (0 : ℝ) 1 := C.mem k (by omega)
  have hxk1 : C.x (k + 1) ∈ Icc (0 : ℝ) 1 := C.mem (k + 1) (by omega)
  rcases le_total v (C.x k) with hle | hge
  · rw [C.bucket_eq_zero hkm hle]
    exact C.bucket_nonneg _ _
  rcases le_total (C.x (k + 1)) v with hge1 | hlt1
  · rw [C.bucket_eq_one hkm hge1]
    refine le_of_eq (C.bucket_eq_one (by omega) ?_).symm
    refine le_trans (C.step (k + 1) (by omega)) ?_
    rcases eq_or_lt_of_le hge1 with heq | hlt
    · exact le_of_eq (by rw [heq])
    · exact (S.betaD_strictMonoOn hxk1 hv hlt).le
  · set t := (v - C.x k) / (C.x (k + 1) - C.x k) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hwk.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hwk]; linarith
    have hvconv : (1 - t) * C.x k + t * C.x (k + 1) = v := by
      rw [ht]
      field_simp
      ring
    have hconv := (betaD_concaveOn S).2 hxk hxk1
      (show (0 : ℝ) ≤ 1 - t by linarith) ht0 (by ring)
    simp only [smul_eq_mul] at hconv
    rw [hvconv] at hconv
    have e1 : (1 - t) * C.x (k + 1) ≤ (1 - t) * S.betaD (C.x k) :=
      mul_le_mul_of_nonneg_left (C.step k hkm) (by linarith)
    have e2 : t * C.x (k + 2) ≤ t * S.betaD (C.x (k + 1)) :=
      mul_le_mul_of_nonneg_left (C.step (k + 1) (by omega)) ht0
    have hid : (1 - t) * C.x (k + 1) + t * C.x (k + 2)
        = C.x (k + 1) + t * (C.x (k + 2) - C.x (k + 1)) := by ring
    have hlow : C.x (k + 1) + t * (C.x (k + 2) - C.x (k + 1)) ≤ S.betaD v := by
      rw [← hid]; linarith
    refine clamp_mono ?_
    rw [le_div_iff₀ (C.width_pos (show k + 1 < C.m by omega))]
    linarith

/--
**One free level advances the potential by one**, up to saturation at `m`.

The saturation is genuine: the chain cannot be extended above `π`, because the bucket
widths there are the gains `gain_δ`, which fall below `ĝ`.
-/
theorem refPot_step {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hbase : C.x 0 ≤ v) :
    min (C.refPot v + 1) (C.m : ℝ) ≤ C.refPot (S.betaD v) := by
  obtain ⟨p, hp⟩ : ∃ p, C.m = p + 1 := ⟨C.m - 1, by have := C.m_pos; omega⟩
  have hx0 : C.x 0 ∈ Icc (0 : ℝ) 1 := C.mem 0 (by omega)
  have hmonoβ : S.betaD (C.x 0) ≤ S.betaD v := by
    rcases eq_or_lt_of_le hbase with heq | hlt
    · exact le_of_eq (by rw [heq])
    · exact (S.betaD_strictMonoOn hx0 hv hlt).le
  have hhead : C.bucket 0 (S.betaD v) = 1 :=
    C.bucket_eq_one C.m_pos (le_trans (C.step 0 C.m_pos) hmonoβ)
  have hshift : ∑ j ∈ Finset.range p, C.bucket j v
      ≤ ∑ j ∈ Finset.range p, C.bucket (j + 1) (S.betaD v) :=
    Finset.sum_le_sum fun j hj =>
      C.bucket_shift (by rw [hp]; exact Nat.succ_lt_succ (Finset.mem_range.mp hj)) hv
  have hsplitβ : C.refPot (S.betaD v)
      = (∑ j ∈ Finset.range p, C.bucket (j + 1) (S.betaD v))
        + C.bucket 0 (S.betaD v) := by
    rw [refPot, hp, Finset.sum_range_succ']
  have hsplitv : C.refPot v
      = (∑ j ∈ Finset.range p, C.bucket j v) + C.bucket p v := by
    rw [refPot, hp, Finset.sum_range_succ]
  have hkey : C.refPot v + 1 - C.bucket p v ≤ C.refPot (S.betaD v) := by
    rw [hsplitβ, hhead, hsplitv]
    linarith
  rcases eq_or_lt_of_le (C.bucket_nonneg p v) with hzero | hpos
  · refine le_trans (min_le_left _ _) ?_
    rw [← hzero] at hkey
    linarith
  · have hvx : C.x p ≤ v := by
      by_contra hcon
      push Not at hcon
      rw [C.bucket_eq_zero (by omega) hcon.le] at hpos
      exact lt_irrefl 0 hpos
    have hfull : (∑ j ∈ Finset.range p, C.bucket j v) = (p : ℝ) :=
      C.refPotUpTo_eq (by omega) hvx
    have hval : C.refPot v = (p : ℝ) + C.bucket p v := by
      rw [hsplitv, hfull]
    have hm : (C.m : ℝ) = (p : ℝ) + 1 := by rw [hp]; push_cast; ring
    refine le_trans (min_le_right _ _) ?_
    rw [hm]
    rw [hval] at hkey
    linarith

end RefChain

end ProofOfSpace

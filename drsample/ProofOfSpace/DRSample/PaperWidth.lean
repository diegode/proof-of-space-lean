import ProofOfSpace.DRSample.PaperDefinitions

namespace ProofOfSpaceStatement
open Finset

/-- The width obstruction used in `cor:balanced-robustness-optimality`. -/
theorem block_width_lt {n e b : ℕ} (hn : 0 < n) (he : 0 < e) (hb : 0 < b)
    {edge : Fin n → Fin n → Prop} {d : ℝ}
    (hrobust : GraphBlockDepthRobust edge e d b) : (b : ℝ) < (n : ℝ) / e := by
  classical
  have hproduct : e * b < n := by
    by_contra! hcover
    let endpoint (i : Fin e) : Fin n :=
      ⟨min (n - 1) ((i.val + 1) * b - 1), lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
    let T := univ.image endpoint
    have hcard : T.card ≤ e := by
      exact (card_image_le).trans (by simp)
    have hdeleted (u : Fin n) : ∃ v ∈ T, u ≤ v ∧ v.val < u.val + b := by
      have hi : u.val / b < e := (Nat.div_lt_iff_lt_mul hb).mpr (by nlinarith [u.isLt])
      let i : Fin e := ⟨u.val / b, hi⟩
      refine ⟨endpoint i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, ?_, ?_⟩
      · change u.val ≤ min (n - 1) ((u.val / b + 1) * b - 1)
        have hmod := Nat.mod_lt u.val hb
        have hsplit := Nat.mod_add_div u.val b
        apply le_min (by omega)
        have hpos : 0 < (u.val / b + 1) * b := by positivity
        have hs := Nat.sub_add_cancel (show 1 ≤ (u.val / b + 1) * b by omega)
        nlinarith
      · change min (n - 1) ((u.val / b + 1) * b - 1) < u.val + b
        have hm := Nat.div_mul_le_self u.val b
        have hlo := min_le_right (n - 1) ((u.val / b + 1) * b - 1)
        have hpos : 0 < (u.val / b + 1) * b := by positivity
        have hs := Nat.sub_add_cancel (show 1 ≤ (u.val / b + 1) * b by omega)
        nlinarith
    obtain ⟨path, hne, _, havoid, _⟩ := hrobust T hcard
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil path hne
    obtain ⟨v, hv, huv⟩ := hdeleted u
    exact havoid u hu v hv huv
  apply (lt_div_iff₀ (by exact_mod_cast he : (0 : ℝ) < e)).mpr
  exact_mod_cast (by simpa [mul_comm] using hproduct)

end ProofOfSpaceStatement

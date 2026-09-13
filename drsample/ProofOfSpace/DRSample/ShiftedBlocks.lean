import ProofOfSpace.DRSample.TriangularGeometry

/-! # Averaging interval deletions over every partition shift -/
namespace ProofOfSpace.DRSample
open Finset Classical

/-- Over all shifts, one endpoint interval meets at most `B+b-1` full blocks.
Counting block starts makes the argument independent of prefix/suffix rounding. -/
theorem sum_shiftedDiscarded_le {n B b : ℕ} (hB : 0 < B) (hb : 0 < b)
    (M : Fin B → ℕ) (T : Finset (Fin n)) :
    (∑ t : Fin B, (shiftedDiscarded t.val B (M t) (blockDeleted b T)).card) ≤
      T.card * (B + b - 1) := by
  let hits : Finset (Sigma fun t : Fin B => Fin (M t)) :=
    univ.sigma fun t => shiftedDiscarded t.val B (M t) (blockDeleted b T)
  have hw (x : {x // x ∈ hits}) : ∃ v : Fin n, v ∈ T ∧
      x.val.1.val + x.val.2.val * B ≤ v.val ∧
      v.val - (x.val.1.val + x.val.2.val * B) < B + b - 1 := by
    have hx := (mem_sigma.mp x.property).2
    obtain ⟨u, hu, hlo, hhi⟩ := (mem_filter.mp hx).2
    obtain ⟨v, hv, huv, hvb⟩ := mem_blockDeleted.mp hu
    refine ⟨v, hv, by omega, ?_⟩
    have hvle : u.val ≤ v.val := huv
    have ht := x.val.1.isLt
    rw [Nat.add_mul, Nat.one_mul] at hhi
    omega
  let endpoint (x : {x // x ∈ hits}) : Fin n := Classical.choose (hw x)
  have hep (x : {x // x ∈ hits}) := Classical.choose_spec (hw x)
  let f (x : {x // x ∈ hits}) : {v // v ∈ T} × Fin (B + b - 1) :=
    (⟨endpoint x, (hep x).1⟩,
      ⟨(endpoint x).val - (x.val.1.val + x.val.2.val * B), (hep x).2.2⟩)
  have hinj : Function.Injective f := by
    intro x y h
    have hv : endpoint x = endpoint y := congrArg (fun z => z.1.val) h
    have hoff : (endpoint x).val - (x.val.1.val + x.val.2.val * B) =
        (endpoint y).val - (y.val.1.val + y.val.2.val * B) := congrArg (fun z => z.2.val) h
    have hx := (hep x).2.1
    have hy := (hep y).2.1
    change x.val.1.val + x.val.2.val * B ≤ (endpoint x).val at hx
    change y.val.1.val + y.val.2.val * B ≤ (endpoint y).val at hy
    rw [hv] at hoff hx
    have hstart : x.val.1.val + x.val.2.val * B = y.val.1.val + y.val.2.val * B := by omega
    have hmod := congrArg (fun z => z % B) hstart
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.val.1.isLt,
      Nat.mod_eq_of_lt y.val.1.isLt] at hmod
    have ht : x.val.1 = y.val.1 := Fin.ext hmod
    have hi : x.val.2.val = y.val.2.val := by
      have he := congrArg Fin.val ht
      rw [he] at hstart
      nlinarith
    apply Subtype.ext
    exact Sigma.ext ht ((Fin.heq_ext_iff (congrArg M ht)).mpr hi)
  have hc := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hc
  simpa only [hits, card_sigma] using hc

theorem exists_shiftedDiscarded_le_average {n B b : ℕ} (hB : 0 < B) (hb : 0 < b)
    (M : Fin B → ℕ) (T : Finset (Fin n)) :
    ∃ t : Fin B, ((shiftedDiscarded t.val B (M t) (blockDeleted b T)).card : ℝ) ≤
      (T.card : ℝ) * (B + b - 1 : ℕ) / B := by
  have hsum := sum_shiftedDiscarded_le hB hb M T
  have hsumR : (∑ t : Fin B,
      ((shiftedDiscarded t.val B (M t) (blockDeleted b T)).card : ℝ)) ≤
      ∑ _ : Fin B, (T.card : ℝ) * (B + b - 1 : ℕ) / B := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hB.ne')]
    exact_mod_cast hsum
  have hne : (univ : Finset (Fin B)).Nonempty := ⟨⟨0, hB⟩, mem_univ _⟩
  obtain ⟨t, _, ht⟩ := exists_le_of_sum_le hne hsumR
  exact ⟨t, ht⟩

end ProofOfSpace.DRSample

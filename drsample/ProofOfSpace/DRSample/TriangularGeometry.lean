import ProofOfSpace.DRSample.HeightLine

/-! # Triangular ports in a shifted partition of blocks of size `20 a`

Each eligible crossing gains at least `9 a` vertices between block centers.
This is the deterministic path-lifting argument used in the paper.
-/
namespace ProofOfSpace.DRSample
open Finset Classical

def shiftedDiscarded {n : ℕ} (t B M : ℕ) (D : Finset (Fin n)) : Finset (Fin M) :=
  univ.filter fun i => ∃ v ∈ D, t + i.val * B ≤ v.val ∧ v.val < t + (i.val + 1) * B

theorem shifted_intact {n t B M : ℕ} {D : Finset (Fin n)} {i : Fin M}
    (hi : i ∉ shiftedDiscarded t B M D) {v : Fin n}
    (hlo : t + i.val * B ≤ v.val) (hhi : v.val < t + (i.val + 1) * B) : v ∉ D := by
  intro hv
  exact hi (mem_filter.mpr ⟨mem_univ _, v, hv, hlo, hhi⟩)

def triangleCenter {n t a M : ℕ} (ha : 0 < a) (hn : t + M * (20 * a) ≤ n)
    (i : Fin M) : Fin n :=
  ⟨t + i.val * (20 * a) + 10 * a, by
    have h := Nat.mul_le_mul_right (20 * a) (show i.val + 1 ≤ M from i.isLt)
    nlinarith⟩

def TrianglePortEdge {n M : ℕ} (G : OrderedGraph n) (t a : ℕ) (i j : Fin M) : Prop :=
  ∃ u v : Fin n, G.edge u v ∧
    t + i.val * (20 * a) + 10 * a ≤ u.val ∧
    u.val < t + (i.val + 1) * (20 * a) ∧
    t + j.val * (20 * a) ≤ v.val ∧
    v.val ≤ t + j.val * (20 * a) + 10 * a ∧
    i.val * (20 * a) + 9 * a + v.val ≤ u.val + j.val * (20 * a)

theorem triangleCenter_height {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (G : OrderedGraph n) (hl : HasLine G)
    (D : Finset (Fin n)) (i : Fin M) (hi : i ∉ shiftedDiscarded t (20 * a) M D) :
    9 * a ≤ height G D (triangleCenter ha hn i) := by
  have hstart : t + i.val * (20 * a) < n := by
    have := (triangleCenter ha hn i).isLt
    dsimp [triangleCenter] at this
    omega
  let u : Fin n := ⟨t + i.val * (20 * a), hstart⟩
  have h := height_along_line G hl D u (triangleCenter ha hn i)
    (by change t + i.val * (20 * a) ≤ t + i.val * (20 * a) + 10 * a; omega) (by
      intro v hv0 hv1
      apply shifted_intact hi hv0
      change v.val ≤ t + i.val * (20 * a) + 10 * a at hv1
      nlinarith)
  dsimp [triangleCenter, u] at h ⊢
  omega

theorem triangleCenter_height_step {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (G : OrderedGraph n) (hl : HasLine G)
    (D : Finset (Fin n)) (i j : Fin M)
    (hi : i ∉ shiftedDiscarded t (20 * a) M D)
    (hj : j ∉ shiftedDiscarded t (20 * a) M D)
    (he : TrianglePortEdge G t a i j) :
    height G D (triangleCenter ha hn i) + 9 * a ≤
      height G D (triangleCenter ha hn j) := by
  obtain ⟨u, v, huv, hu0, hu1, hv0, hv1, hsum⟩ := he
  have hfirst := height_along_line G hl D (triangleCenter ha hn i) u hu0 (by
    intro w hw0 hw1
    apply shifted_intact hi (by change t + i.val * (20 * a) + 10 * a ≤ w.val at hw0; omega)
      (lt_of_le_of_lt (show w.val ≤ u.val from hw1) hu1))
  have hvD : v ∉ D := shifted_intact hj hv0 (by nlinarith)
  have hcross := height_lt_of_edge hvD huv
  have hlast := height_along_line G hl D v (triangleCenter ha hn j) hv1 (by
    intro w hw0 hw1
    apply shifted_intact hj (hv0.trans hw0)
    change w.val ≤ t + j.val * (20 * a) + 10 * a at hw1
    nlinarith)
  dsimp [triangleCenter] at hfirst hlast ⊢
  omega

theorem lift_triangle_path {n t a M : ℕ} (ha : 0 < a)
    (hn : t + M * (20 * a) ≤ n) (G : OrderedGraph n) (H : OrderedGraph M)
    (hl : HasLine G) (he : ∀ i j, H.edge i j → TrianglePortEdge G t a i j)
    (D : Finset (Fin n)) {d : ℝ} (hd : 0 < d)
    (hpath : HasPath H (shiftedDiscarded t (20 * a) M D) d) :
    HasPath G D ((9 * a : ℕ) * d) := by
  obtain ⟨P, hne, hc, havoid, hlen⟩ := hpath
  cases P with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    obtain ⟨v, hv, hvbound⟩ := chain_weight_bound
      (fun i => height G D (triangleCenter ha hn i)) (9 * a) x xs hc (by
        intro i hi j hj hij
        exact triangleCenter_height_step ha hn G hl D i j (havoid i hi) (havoid j hj) (he i j hij))
    have hx := triangleCenter_height ha hn G hl D x (havoid x (by simp))
    have hnat : 9 * a * (x :: xs).length ≤ height G D (triangleCenter ha hn v) := by
      simp only [List.length_cons]
      nlinarith
    apply hasPath_of_le_depth (by positivity : 0 < ((9 * a : ℕ) : ℝ) * d)
    calc ((9 * a : ℕ) : ℝ) * d ≤ ((9 * a : ℕ) : ℝ) * (x :: xs).length :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ ≤ height G D (triangleCenter ha hn v) := by exact_mod_cast hnat
      _ ≤ depth G D := by exact_mod_cast height_le_depth G D _

end ProofOfSpace.DRSample

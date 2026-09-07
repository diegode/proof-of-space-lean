import ProofOfSpace.DRSample.RowGraph
import ProofOfSpace.DRSample.Samplers

/-! # Explicit finite block-depth robustness bounds for the sampled graph -/
namespace ProofOfSpace.DRSample
open Finset Classical

theorem FiniteLaw.probability_product_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : FiniteLaw α) (q : FiniteLaw β) (Q : α → Prop) :
    (p.product q).probability (fun s => Q s.1) = p.probability Q := by
  unfold probability product
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  by_cases ha : Q a
  · simp [ha, ← mul_sum, q.total]
  · simp [ha]

/-- The last sampled row supplies the incomplete suffix. Extra choices past
vertex `n-1` are ignored. Every genuine vertex has its prescribed incoming law. -/
noncomputable def graphLaw {n : ℕ} (m : ℕ) (p : ℕ → FiniteLaw (Finset (Fin n))) :
    FiniteLaw (SampleSpace (Fin m → Finset (Fin n)) (n / m + 1)) :=
  independentSamples (rowLaw m p) (n / m + 1)

theorem finite_block_robustness {n m e b : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n)
    (hb : b ≤ m) (he : 2 * e ≤ (n / m) / 48)
    (p : ℕ → FiniteLaw (Finset (Fin n)))
    (havoid : ∀ v < n, ∀ A : Finset (Fin n),
      (p v).probability (fun parents => Disjoint parents A) ≤
        Real.exp (-(1 / (4 * Real.logb 2 n)) * ∑ i ∈ A, harmonicAt n v i)) :
    (graphLaw m p).probability (fun s =>
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) e
        (((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * Real.logb 2 n / (3 * m)))) b) ≥
      1 - Real.exp (-(2 - Real.log 3) * (n / m : ℕ)) := by
  have hm0 : 0 < m := by omega
  have hM : 0 < n / m := Nat.div_pos hmn hm0
  have hn : (n / m) * m ≤ n := Nat.div_mul_le_self _ _
  have hlog : 0 < Real.logb 2 n := lt_of_lt_of_le (by norm_num)
    (logb_two_ge_one (show 2 ≤ n by omega))
  have hlambda : 0 < (m : ℝ) / (128 * Real.logb 2 n) := by positivity
  have hmeta := multiscale_mapped hM (rowLaw m p) (metaParents (by omega) hn) hlambda
    (fun j hj A => metaParents_avoidance_explicit hm hn hj hlog p havoid A)
  have hfinite : (graphLaw m p).probability (fun s =>
      DepthRobust (exposedGraph (n / m) (mapSamples (metaParents (by omega) hn) (n / m) s.1))
        ((n / m) / 48) (((3 : ℝ) * (n / m : ℕ) / 4) *
          Real.exp (-64 / (3 * (m / (128 * Real.logb 2 n)))))) ≥
        1 - Real.exp (-(2 - Real.log 3) * (n / m : ℕ)) := by
    exact hmeta.trans_eq (FiniteLaw.probability_product_fst
      (independentSamples (rowLaw m p) (n / m)) (rowLaw m p (n / m)) _).symm
  apply hfinite.trans
  apply FiniteLaw.probability_mono
  intro s hs
  have htransfer := blockDepthRobust_of_meta (rowGraph hm0 (n / m) s.1)
    (exposedGraph (n / m) (mapSamples (metaParents (by omega) hn) (n / m) s.1))
    (rowGraph_hasLine hm0 s.1) (by omega) hn hb (by positivity)
    (mapped_meta_edge_port (by omega) hn s.1) he hs
  have hdepth : (m : ℝ) / 3 * (((3 : ℝ) * (n / m : ℕ) / 4) *
      Real.exp (-64 / (3 * (m / (128 * Real.logb 2 n))))) =
      ((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * Real.logb 2 n / (3 * m))) := by
    have hexp : -64 / (3 * ((m : ℝ) / (128 * Real.logb 2 n))) =
        -(8192 * Real.logb 2 n / (3 * m)) := by field_simp; ring
    rw [hexp]
    ring
  rw [hdepth] at htransfer
  exact htransfer.mono_graph (fun _ _ h => rowGraph_mono hm0 s.1 s.2 h)

theorem drsample_finite {n m : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n) :
    (graphLaw m (drIncomingLaw (by omega))).probability (fun s =>
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) ((n / m) / 96)
        (((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * Real.logb 2 n / (3 * m)))) m) ≥
      1 - Real.exp (-(2 - Real.log 3) * (n / m : ℕ)) := by
  exact finite_block_robustness hm hmn le_rfl (by omega) _
    (fun _ hv A => drIncomingLaw_avoidance (by omega) hv A)

theorem filecoin_bucket6_finite {n m : ℕ} (hm : 12 ≤ m) (hmn : m ≤ n) :
    (graphLaw m (filecoinIncomingLaw (by omega))).probability (fun s =>
      BlockDepthRobust (rowGraph (by omega) (n / m + 1) s) ((n / m) / 96)
        (((m : ℝ) * (n / m : ℕ) / 4) * Real.exp (-(8192 * Real.logb 2 n / (3 * m)))) m) ≥
      1 - Real.exp (-(2 - Real.log 3) * (n / m : ℕ)) := by
  exact finite_block_robustness hm hmn le_rfl (by omega) _
    (fun _ hv A => filecoinIncomingLaw_avoidance (by omega) hv A)

end ProofOfSpace.DRSample

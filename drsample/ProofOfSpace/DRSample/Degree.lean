import ProofOfSpace.DRSample.MultiSamplerRegistry

namespace ProofOfSpaceStatement
open Finset Classical ProofOfSpace.DRSample

/-- The graph with `r` parent draws has maximum indegree at most `r+1`. -/
theorem multiSample_indegree {n r : ℕ} (parents : Fin n → Fin r → Fin n) (v : Fin n) :
    (univ.filter fun u => multiSampleEdge parents u v).card ≤ r + 1 := by
  apply (card_le_card (show (univ.filter fun u => multiSampleEdge parents u v) ⊆
      sampledParents v.val (parents v) from ?_)).trans (sampledParents_card v.val (parents v))
  intro u hu
  rcases (mem_filter.mp hu).2.2 with hl | ⟨j, hj⟩
  · exact mem_sampledParents_line (parents v) u hl
  · exact mem_union_left _ (mem_image.mpr ⟨j, mem_univ _, hj⟩)

end ProofOfSpaceStatement

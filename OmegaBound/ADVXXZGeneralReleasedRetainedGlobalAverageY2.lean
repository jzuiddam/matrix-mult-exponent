import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalAverageY2KernelData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Exact entropy normalization of the 81-word released global average.
theorem released_global_average_y_nats_r2 :
    (1 : ℝ) / 6 * Entropy.H Finset.univ
        (globalAverage physicalGlobalSpec.toPaper 2
          (physicalGlobalSpec.toPaper.perm 2 .Y)) =
      releasedGlobalAverageYNatsR2 := by
  unfold Entropy.H
  rw [released_chunk4_sum_y0]
  simp_rw [released_globalAverageY_value_r2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [releasedGlobalAverageYProbQ2,
    releasedGlobalAverageYProbQList2, releasedGlobalAverageYNatsR2]
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_average_y_nats_r2

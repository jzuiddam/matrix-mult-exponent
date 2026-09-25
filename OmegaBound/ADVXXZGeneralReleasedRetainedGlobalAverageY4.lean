import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalAverageY4KernelData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Exact entropy normalization of the 81-word released global average.
theorem released_global_average_y_nats_r4 :
    (1 : ℝ) / 6 * Entropy.H Finset.univ
        (globalAverage physicalGlobalSpec.toPaper 4
          (physicalGlobalSpec.toPaper.perm 4 .Y)) =
      releasedGlobalAverageYNatsR4 := by
  unfold Entropy.H
  rw [released_chunk4_sum_y0]
  simp_rw [released_globalAverageY_value_r4]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [releasedGlobalAverageYProbQ4,
    releasedGlobalAverageYProbQList4, releasedGlobalAverageYNatsR4]
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_average_y_nats_r4

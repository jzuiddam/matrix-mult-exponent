import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalAverageZ5KernelData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Exact entropy normalization of the 81-word released global average.
theorem released_global_average_z_nats_r5 :
    (1 : ℝ) / 6 * Entropy.H Finset.univ
        (globalAverage physicalGlobalSpec.toPaper 5
          (physicalGlobalSpec.toPaper.perm 5 .Z)) =
      releasedGlobalAverageZNatsR5 := by
  unfold Entropy.H
  rw [released_chunk4_sum_y0]
  simp_rw [released_globalAverageZ_value_r5]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [releasedGlobalAverageZProbQ5,
    releasedGlobalAverageZProbQList5, releasedGlobalAverageZNatsR5]
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_average_z_nats_r5

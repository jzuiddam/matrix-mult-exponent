import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalAverageZ4KernelData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Exact entropy normalization of the 81-word released global average.
theorem released_global_average_z_nats_r4 :
    (1 : ℝ) / 6 * Entropy.H Finset.univ
        (globalAverage physicalGlobalSpec.toPaper 4
          (physicalGlobalSpec.toPaper.perm 4 .Z)) =
      releasedGlobalAverageZNatsR4 := by
  unfold Entropy.H
  rw [released_chunk4_sum_y0]
  simp_rw [released_globalAverageZ_value_r4]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [releasedGlobalAverageZProbQ4,
    releasedGlobalAverageZProbQList4, releasedGlobalAverageZNatsR4]
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_average_z_nats_r4

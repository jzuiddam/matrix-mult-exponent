import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalAverageY0KernelData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
theorem released_global_average_y_nats_r0 :
    (1 : ℝ) / 6 * Entropy.H Finset.univ
        (globalAverage physicalGlobalSpec.toPaper 0
          (physicalGlobalSpec.toPaper.perm 0 .Y)) =
      releasedGlobalAverageYNatsR0 := by
  unfold Entropy.H
  rw [released_chunk4_sum_y0]
  simp_rw [released_globalAverageY_value_r0]
  change (1 : ℝ) / 6 * ∑ i : Fin 81, Real.negMulLog
      (((releasedGlobalAverageYProbQ0 (releasedGlobalAverageYSortEquiv0 i) : ℚ) : ℝ)) = _
  rw [Equiv.sum_comp releasedGlobalAverageYSortEquiv0
    (fun i : Fin 81 ↦ Real.negMulLog
      (((releasedGlobalAverageYProbQ0 i : ℚ) : ℝ)))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [releasedGlobalAverageYProbQ0, releasedGlobalAverageYProbQList0,
    releasedGlobalAverageYNatsR0]
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_average_y_nats_r0

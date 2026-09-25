import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalNats
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

theorem released_global_z_value_r4 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_12_1 =
      (1 : ℝ) / 6 *
        (Entropy.H Finset.univ
            (globalAverage physicalGlobalSpec.toPaper 4
              (physicalGlobalSpec.toPaper.perm 4 .Z)) -
          releasedGlobalLambdaNatsYZ physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) := by
  rw [mul_sub, released_global_average_z_nats_r4,
    released_globalLambdaNats_rows, released_global_lambda_weighted_nats_r4]
  exact released_global_z_retained_decomposition_r4

theorem released_global_z_lower_r4 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_12_1 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 4 *
        (entropy
            (globalAverage physicalGlobalSpec.toPaper 4
              (physicalGlobalSpec.toPaper.perm 4 .Z)) -
          globalLambda physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) := by
  rw [released_global_z_value_r4]
  calc
    (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 4
                (physicalGlobalSpec.toPaper.perm 4 .Z)) -
            releasedGlobalLambdaNatsYZ physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) =
        Real.log 2 * ((1 : ℝ) / 6) *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 4
                (physicalGlobalSpec.toPaper.perm 4 .Z)) -
            globalLambda physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) := by
      change (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 4
                (physicalGlobalSpec.toPaper.perm 4 .Z)) -
            globalLambdaNats physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) = _
      rw [← log_two_mul_entropy, ← log_two_mul_globalLambda]
      ring
    _ = Real.log 2 * physicalGlobalSpec.A.probR 4 *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 4
                (physicalGlobalSpec.toPaper.perm 4 .Z)) -
            globalLambda physicalGlobalSpec.toPaper 4
            (physicalGlobalSpec.toPaper.perm 4 .X)
            (physicalGlobalSpec.toPaper.perm 4 .Y)
            (physicalGlobalSpec.toPaper.perm 4 .Z)) := by
      rw [released_physical_global_region_weight]
  exact le_rfl

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_z_value_r4
#print axioms OmegaBound.ADVXXZGeneral.released_global_z_lower_r4

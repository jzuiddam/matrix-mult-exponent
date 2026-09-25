import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalNats
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

theorem released_global_y_value_r5 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_13_1 =
      (1 : ℝ) / 6 *
        (Entropy.H Finset.univ
            (globalAverage physicalGlobalSpec.toPaper 5
              (physicalGlobalSpec.toPaper.perm 5 .Y)) -
          releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) := by
  rw [mul_sub, released_global_average_y_nats_r5,
    released_globalEtaNats_rows, released_global_eta_weighted_nats_r5]
  exact released_global_y_retained_decomposition_r5

theorem released_global_y_lower_r5 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_13_1 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 5 *
        (entropy
            (globalAverage physicalGlobalSpec.toPaper 5
              (physicalGlobalSpec.toPaper.perm 5 .Y)) -
          globalEta physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) := by
  rw [released_global_y_value_r5]
  calc
    (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 5
                (physicalGlobalSpec.toPaper.perm 5 .Y)) -
            releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) =
        Real.log 2 * ((1 : ℝ) / 6) *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 5
                (physicalGlobalSpec.toPaper.perm 5 .Y)) -
            globalEta physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) := by
      change (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 5
                (physicalGlobalSpec.toPaper.perm 5 .Y)) -
            globalEtaNats physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) = _
      rw [← log_two_mul_entropy, ← log_two_mul_globalEta]
      ring
    _ = Real.log 2 * physicalGlobalSpec.A.probR 5 *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 5
                (physicalGlobalSpec.toPaper.perm 5 .Y)) -
            globalEta physicalGlobalSpec.toPaper 5
            (physicalGlobalSpec.toPaper.perm 5 .X)
            (physicalGlobalSpec.toPaper.perm 5 .Y)
            (physicalGlobalSpec.toPaper.perm 5 .Z)) := by
      rw [released_physical_global_region_weight]
  exact le_rfl

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_y_value_r5
#print axioms OmegaBound.ADVXXZGeneral.released_global_y_lower_r5

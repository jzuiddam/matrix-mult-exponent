import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalNats
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

theorem released_global_y_value_r1 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_9_2 =
      (1 : ℝ) / 6 *
        (Entropy.H Finset.univ
            (globalAverage physicalGlobalSpec.toPaper 1
              (physicalGlobalSpec.toPaper.perm 1 .Y)) -
          releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) := by
  rw [mul_sub, released_global_average_y_nats_r1,
    released_globalEtaNats_rows, released_global_eta_weighted_nats_r1]
  exact released_global_y_retained_decomposition_r1

theorem released_global_y_lower_r1 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_9_2 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 1 *
        (entropy
            (globalAverage physicalGlobalSpec.toPaper 1
              (physicalGlobalSpec.toPaper.perm 1 .Y)) -
          globalEta physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) := by
  rw [released_global_y_value_r1]
  calc
    (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 1
                (physicalGlobalSpec.toPaper.perm 1 .Y)) -
            releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) =
        Real.log 2 * ((1 : ℝ) / 6) *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 1
                (physicalGlobalSpec.toPaper.perm 1 .Y)) -
            globalEta physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) := by
      change (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 1
                (physicalGlobalSpec.toPaper.perm 1 .Y)) -
            globalEtaNats physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) = _
      rw [← log_two_mul_entropy, ← log_two_mul_globalEta]
      ring
    _ = Real.log 2 * physicalGlobalSpec.A.probR 1 *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 1
                (physicalGlobalSpec.toPaper.perm 1 .Y)) -
            globalEta physicalGlobalSpec.toPaper 1
            (physicalGlobalSpec.toPaper.perm 1 .X)
            (physicalGlobalSpec.toPaper.perm 1 .Y)
            (physicalGlobalSpec.toPaper.perm 1 .Z)) := by
      rw [released_physical_global_region_weight]
  exact le_rfl

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_y_value_r1
#print axioms OmegaBound.ADVXXZGeneral.released_global_y_lower_r1

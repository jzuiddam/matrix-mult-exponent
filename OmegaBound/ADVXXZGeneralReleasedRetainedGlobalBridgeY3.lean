import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalNats
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

theorem released_global_y_value_r3 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_11_2 =
      (1 : ℝ) / 6 *
        (Entropy.H Finset.univ
            (globalAverage physicalGlobalSpec.toPaper 3
              (physicalGlobalSpec.toPaper.perm 3 .Y)) -
          releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) := by
  rw [mul_sub, released_global_average_y_nats_r3,
    released_globalEtaNats_rows, released_global_eta_weighted_nats_r3]
  exact released_global_y_retained_decomposition_r3

theorem released_global_y_lower_r3 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_11_2 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 3 *
        (entropy
            (globalAverage physicalGlobalSpec.toPaper 3
              (physicalGlobalSpec.toPaper.perm 3 .Y)) -
          globalEta physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) := by
  rw [released_global_y_value_r3]
  calc
    (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 3
                (physicalGlobalSpec.toPaper.perm 3 .Y)) -
            releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) =
        Real.log 2 * ((1 : ℝ) / 6) *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 3
                (physicalGlobalSpec.toPaper.perm 3 .Y)) -
            globalEta physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) := by
      change (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 3
                (physicalGlobalSpec.toPaper.perm 3 .Y)) -
            globalEtaNats physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) = _
      rw [← log_two_mul_entropy, ← log_two_mul_globalEta]
      ring
    _ = Real.log 2 * physicalGlobalSpec.A.probR 3 *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 3
                (physicalGlobalSpec.toPaper.perm 3 .Y)) -
            globalEta physicalGlobalSpec.toPaper 3
            (physicalGlobalSpec.toPaper.perm 3 .X)
            (physicalGlobalSpec.toPaper.perm 3 .Y)
            (physicalGlobalSpec.toPaper.perm 3 .Z)) := by
      rw [released_physical_global_region_weight]
  exact le_rfl

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_y_value_r3
#print axioms OmegaBound.ADVXXZGeneral.released_global_y_lower_r3

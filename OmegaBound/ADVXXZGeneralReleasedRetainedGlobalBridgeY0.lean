import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalNats
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

theorem released_global_y_value_r0 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_8_1 =
      (1 : ℝ) / 6 *
        (Entropy.H Finset.univ
            (globalAverage physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .Y)) -
          releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 0
            (physicalGlobalSpec.toPaper.perm 0 .X)
            (physicalGlobalSpec.toPaper.perm 0 .Y)
            (physicalGlobalSpec.toPaper.perm 0 .Z)) := by
  rw [mul_sub, released_global_average_y_nats_r0,
    released_globalEtaNats_rows, released_global_eta_weighted_nats_r0]
  exact released_global_y_retained_decomposition_r0

theorem released_global_y_lower_r0 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_8_1 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 0 *
        (entropy
            (globalAverage physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .Y)) -
          globalEta physicalGlobalSpec.toPaper 0
            (physicalGlobalSpec.toPaper.perm 0 .X)
            (physicalGlobalSpec.toPaper.perm 0 .Y)
            (physicalGlobalSpec.toPaper.perm 0 .Z)) := by
  rw [released_global_y_value_r0]
  calc
    (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 0
                (physicalGlobalSpec.toPaper.perm 0 .Y)) -
            releasedGlobalEtaNatsYZ physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .X)
              (physicalGlobalSpec.toPaper.perm 0 .Y)
              (physicalGlobalSpec.toPaper.perm 0 .Z)) =
        Real.log 2 * ((1 : ℝ) / 6) *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 0
                (physicalGlobalSpec.toPaper.perm 0 .Y)) -
            globalEta physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .X)
              (physicalGlobalSpec.toPaper.perm 0 .Y)
              (physicalGlobalSpec.toPaper.perm 0 .Z)) := by
      change (1 : ℝ) / 6 *
          (Entropy.H Finset.univ
              (globalAverage physicalGlobalSpec.toPaper 0
                (physicalGlobalSpec.toPaper.perm 0 .Y)) -
            globalEtaNats physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .X)
              (physicalGlobalSpec.toPaper.perm 0 .Y)
              (physicalGlobalSpec.toPaper.perm 0 .Z)) = _
      rw [← log_two_mul_entropy, ← log_two_mul_globalEta]
      ring
    _ = Real.log 2 * physicalGlobalSpec.A.probR 0 *
          (entropy
              (globalAverage physicalGlobalSpec.toPaper 0
                (physicalGlobalSpec.toPaper.perm 0 .Y)) -
            globalEta physicalGlobalSpec.toPaper 0
              (physicalGlobalSpec.toPaper.perm 0 .X)
              (physicalGlobalSpec.toPaper.perm 0 .Y)
              (physicalGlobalSpec.toPaper.perm 0 .Z)) := by
      rw [released_physical_global_region_weight]
  exact le_rfl

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_y_value_r0
#print axioms OmegaBound.ADVXXZGeneral.released_global_y_lower_r0

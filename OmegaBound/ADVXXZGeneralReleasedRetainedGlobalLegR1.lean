import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ1

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r1 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 1) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 1).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r1 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_9_0 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 1 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 1)
            (physicalGlobalSpec.toPaper.perm 1 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 1)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 1) released_global_alpha_probability_r1
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 1 .X)
    releasedGlobalLambdaSumR1 releasedGlobalLambdaMarginR1
  rw [← released_global_x_dual_eq_r1] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 9 lies below the weighted paper minimum for global region 1. -/
theorem released_global_region_rate_lower_r1 :
    OmegaBound.ADVXXZCert.R9 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 1 *
        globalRegionRate physicalGlobalSpec.toPaper 1 := by
  have hrow := OmegaBound.ADVXXZCert.R9_le_actualRetainedCapacity_9
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_9, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 1 OmegaBound.ADVXXZCert.R9
    (hrow.1.trans released_global_x_lower_local_r1)
    ((hrow.2.trans (min_le_right _ _)).trans released_global_y_lower_r1)
    ((hrow.2.trans (min_le_left _ _)).trans released_global_z_lower_r1)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r1

import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ0

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r0 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 0) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 0).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r0 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_8_0 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 0 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 0)
            (physicalGlobalSpec.toPaper.perm 0 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 0)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 0) released_global_alpha_probability_r0
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 0 .X)
    releasedGlobalLambdaSumR0 releasedGlobalLambdaMarginR0
  rw [← released_global_x_dual_eq_r0] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 8 lies below the weighted paper minimum for global region 0. -/
theorem released_global_region_rate_lower_r0 :
    OmegaBound.ADVXXZCert.R8 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 0 *
        globalRegionRate physicalGlobalSpec.toPaper 0 := by
  have hrow := OmegaBound.ADVXXZCert.R8_le_actualRetainedCapacity_8
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_8, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 0 OmegaBound.ADVXXZCert.R8
    (hrow.1.trans released_global_x_lower_local_r0)
    ((hrow.2.trans (min_le_left _ _)).trans released_global_y_lower_r0)
    ((hrow.2.trans (min_le_right _ _)).trans released_global_z_lower_r0)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r0

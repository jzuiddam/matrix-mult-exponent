import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ2

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r2 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 2) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 2).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r2 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_10_1 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 2 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 2)
            (physicalGlobalSpec.toPaper.perm 2 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 2)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 2) released_global_alpha_probability_r2
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 2 .X)
    releasedGlobalLambdaSumR2 releasedGlobalLambdaMarginR2
  rw [← released_global_x_dual_eq_r2] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 10 lies below the weighted paper minimum for global region 2. -/
theorem released_global_region_rate_lower_r2 :
    OmegaBound.ADVXXZCert.R10 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 2 *
        globalRegionRate physicalGlobalSpec.toPaper 2 := by
  have hrow := OmegaBound.ADVXXZCert.R10_le_actualRetainedCapacity_10
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_10, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 2 OmegaBound.ADVXXZCert.R10
    ((hrow.2.trans (min_le_left _ _)).trans released_global_x_lower_local_r2)
    (hrow.1.trans released_global_y_lower_r2)
    ((hrow.2.trans (min_le_right _ _)).trans released_global_z_lower_r2)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r2

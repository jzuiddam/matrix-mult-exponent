import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ4

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r4 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 4) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 4).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r4 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_12_2 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 4 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 4)
            (physicalGlobalSpec.toPaper.perm 4 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 4)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 4) released_global_alpha_probability_r4
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 4 .X)
    releasedGlobalLambdaSumR4 releasedGlobalLambdaMarginR4
  rw [← released_global_x_dual_eq_r4] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 12 lies below the weighted paper minimum for global region 4. -/
theorem released_global_region_rate_lower_r4 :
    OmegaBound.ADVXXZCert.R12 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 4 *
        globalRegionRate physicalGlobalSpec.toPaper 4 := by
  have hrow := OmegaBound.ADVXXZCert.R12_le_actualRetainedCapacity_12
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_12, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 4 OmegaBound.ADVXXZCert.R12
    ((hrow.2.trans (min_le_right _ _)).trans released_global_x_lower_local_r4)
    (hrow.1.trans released_global_y_lower_r4)
    ((hrow.2.trans (min_le_left _ _)).trans released_global_z_lower_r4)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r4

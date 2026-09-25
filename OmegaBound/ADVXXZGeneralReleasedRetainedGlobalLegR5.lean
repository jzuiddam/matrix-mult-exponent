import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ5

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r5 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 5) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 5).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r5 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_13_2 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 5 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 5)
            (physicalGlobalSpec.toPaper.perm 5 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 5)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 5) released_global_alpha_probability_r5
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 5 .X)
    releasedGlobalLambdaSumR5 releasedGlobalLambdaMarginR5
  rw [← released_global_x_dual_eq_r5] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 13 lies below the weighted paper minimum for global region 5. -/
theorem released_global_region_rate_lower_r5 :
    OmegaBound.ADVXXZCert.R13 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 5 *
        globalRegionRate physicalGlobalSpec.toPaper 5 := by
  have hrow := OmegaBound.ADVXXZCert.R13_le_actualRetainedCapacity_13
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_13, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 5 OmegaBound.ADVXXZCert.R13
    ((hrow.2.trans (min_le_right _ _)).trans released_global_x_lower_local_r5)
    ((hrow.2.trans (min_le_left _ _)).trans released_global_y_lower_r5)
    (hrow.1.trans released_global_z_lower_r5)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r5

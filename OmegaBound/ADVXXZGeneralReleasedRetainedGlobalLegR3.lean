import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalRegionMin
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeX3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeY3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalBridgeZ3

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

private theorem released_global_alpha_probability_r3 :
    IsProbability (physicalGlobalSpec.toPaper.alpha 3) := by
  change IsProbability
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist 3).probR
  exact ⟨RatDist.probR_nonneg _, RatDist.sum_probR _⟩

private theorem released_global_x_lower_local_r3 :
    OmegaBound.ADVXXZCert.actualRetainedCapacity_11_1 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 3 *
        (entropy (marginal (physicalGlobalSpec.toPaper.alpha 3)
            (physicalGlobalSpec.toPaper.perm 3 .X)) -
          penalty (physicalGlobalSpec.toPaper.alpha 3)) := by
  have h := global_x_fenchel_value_le
    (physicalGlobalSpec.toPaper.alpha 3) released_global_alpha_probability_r3
    ((1 : ℝ) / 6) (by norm_num) (physicalGlobalSpec.toPaper.perm 3 .X)
    releasedGlobalLambdaSumR3 releasedGlobalLambdaMarginR3
  rw [← released_global_x_dual_eq_r3] at h
  simpa only [released_physical_global_region_weight] using h

/-- Released row 11 lies below the weighted paper minimum for global region 3. -/
theorem released_global_region_rate_lower_r3 :
    OmegaBound.ADVXXZCert.R11 ≤
      Real.log 2 * physicalGlobalSpec.A.probR 3 *
        globalRegionRate physicalGlobalSpec.toPaper 3 := by
  have hrow := OmegaBound.ADVXXZCert.R11_le_actualRetainedCapacity_11
  rw [OmegaBound.ADVXXZCert.actualRetainedCapacity_11, le_min_iff] at hrow
  exact released_global_region_lower_of_xyz 3 OmegaBound.ADVXXZCert.R11
    ((hrow.2.trans (min_le_left _ _)).trans released_global_x_lower_local_r3)
    ((hrow.2.trans (min_le_right _ _)).trans released_global_y_lower_r3)
    (hrow.1.trans released_global_z_lower_r3)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_rate_lower_r3

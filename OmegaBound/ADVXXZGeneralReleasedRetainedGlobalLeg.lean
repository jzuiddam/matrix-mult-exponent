import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLegR5
import OmegaBound.ADVXXZGeneralReleasedRetainedLegs

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The six released physical-global rows fit below the paper global rate. -/
theorem released_global_retained_leg : S_released_global_retained_leg := by
  have h01 := add_le_add released_global_region_rate_lower_r0
    released_global_region_rate_lower_r1
  have h012 := add_le_add h01 released_global_region_rate_lower_r2
  have h0123 := add_le_add h012 released_global_region_rate_lower_r3
  have h01234 := add_le_add h0123 released_global_region_rate_lower_r4
  have h012345 := add_le_add h01234 released_global_region_rate_lower_r5
  unfold S_released_global_retained_leg gRate
  rw [Fin.sum_univ_six]
  calc
    _ ≤ _ := h012345
    _ = _ := by ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_retained_leg

import OmegaBound.ADVXXZGeneralRowsRegion0Close30
import OmegaBound.ADVXXZGeneralRowsRegion1Close30
import OmegaBound.ADVXXZGeneralRowsRegion2Close30
import OmegaBound.ADVXXZGeneralRowsRegion3Close30
import OmegaBound.ADVXXZGeneralRowsRegion4Close30
import OmegaBound.ADVXXZGeneralRowsRegion5Close30
import OmegaBound.ADVXXZGeneralRowsLevel3LegAlgebra30
import PLATFORM.Statements.«V17_I_Rows.10»

/-!
# The level-3 retained leg (frozen `V17_I_Rows.10`)

The six regional closes (each `R_{r+2} ≤ log 2 · constituentRegionRate releasedConstituentSpec.toPaper r / D²`,
certified cell by cell over 126 parents × 3 sides) combine algebraically into the frozen leg.
-/

namespace OmegaBound.ADVXXZGeneral

/-- Frozen `V17_I_Rows.10`: the level-3 leg of the released retained fit. -/
theorem released_level3_retained_leg : S_released_level3_retained_leg :=
  level3_leg_of_regional_closes
    R2_le_constituentRegionRateR0_30 R3_le_constituentRegionRateR1_30
    R4_le_constituentRegionRateR2_30 R5_le_constituentRegionRateR3_30
    R6_le_constituentRegionRateR4_30 R7_le_constituentRegionRateR5_30

example : P2M.V17_I_Rows.S_V17_I_Rows_10 := released_level3_retained_leg

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_level3_retained_leg

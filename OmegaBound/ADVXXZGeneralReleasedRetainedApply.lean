import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLeg
import OmegaBound.ADVXXZGeneralReleasedRetainedResidualGlue
import OmegaBound.ADVXXZGeneralReleasedRetainedSharpFit
import PLATFORM.Statements.«V17_I_Apply.4»

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

/-- The three retained legs give the frozen retained residual. -/
theorem residual_of_level3_leg
    (h3 : S_released_level3_retained_leg) :
    P2M.V17_I_Apply.S_V17_I_Apply_4 := by
  change S_released_retained_residual
  exact residual_of_legs released_level2_retained_leg h3 released_global_retained_leg

/-- A released level-3 retained leg completes the frozen numerical fit. -/
theorem apply1_of_level3_leg
    (h3 : S_released_level3_retained_leg) : S_V17_I_Apply_1 := by
  apply apply1_of_retained_lower_sharp
  have hres := residual_of_level3_leg h3
  change OmegaBound.CertArith.Ecert ≤
    derivedRetainedRate releasedOrdinaryCertificatePhysical at hres
  linarith

example : S_released_level3_retained_leg →
    P2M.V17_I_Apply.S_V17_I_Apply_4 := residual_of_level3_leg

example : S_released_level3_retained_leg → S_V17_I_Apply_1 :=
  apply1_of_level3_leg

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.residual_of_level3_leg
#print axioms OmegaBound.ADVXXZGeneral.apply1_of_level3_leg

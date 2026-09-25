import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorDerivedRetained
import OmegaBound.ADVXXZCertClose

/-!
# Statement shapes for the released retained-rate residual

The level-2 leg is stated in `ADVXXZGeneralReleasedRetainedLevel2Leg`; this module states the
level-3, global, and combined-residual shapes.
-/

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

/-- The six released level-3 retained rows. -/
def S_released_level3_retained_leg : Prop :=
  (OmegaBound.ADVXXZCert.R2 + OmegaBound.ADVXXZCert.R3 + OmegaBound.ADVXXZCert.R4 +
      OmegaBound.ADVXXZCert.R5 + OmegaBound.ADVXXZCert.R6 + OmegaBound.ADVXXZCert.R7) ≤
    cRate releasedConstituentSpec * (constituentBaseTotal releasedParent : ℝ) /
      (releasedCertificate.D : ℝ) ^ 2

/-- The six released physical-global retained rows. -/
def S_released_global_retained_leg : Prop :=
  (OmegaBound.ADVXXZCert.R8 + OmegaBound.ADVXXZCert.R9 + OmegaBound.ADVXXZCert.R10 +
      OmegaBound.ADVXXZCert.R11 + OmegaBound.ADVXXZCert.R12 +
      OmegaBound.ADVXXZCert.R13) ≤ gRate physicalGlobalSpec

/-- The complete retained-rate residual needed by `V17_I_Apply.1`. -/
def S_released_retained_residual : Prop :=
  OmegaBound.CertArith.Ecert ≤
    derivedRetainedRate releasedOrdinaryCertificatePhysical

end OmegaBound.ADVXXZGeneral

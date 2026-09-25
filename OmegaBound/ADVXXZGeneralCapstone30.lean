import OmegaBound.ADVXXZGeneralRowsLevel3Leg30
import OmegaBound.ADVXXZGeneralReleasedRetainedApply
import OmegaBound.ADVXXZGeneralIterateStagesUnconditional
import OmegaBound.ADVXXZGeneralClosureConditional

/-!
# The capstone

`omegaMM F < 2371339/10^6` for every field (`omegaMM_lt_target_allFields`, statement `T8_F.1`) and
over `ℚ` (`ADVXXZFinal.omegaMM_lt_target114`, statement `T8.1`). The level-3 retained leg
`released_level3_retained_leg` gives the released numerical fit `released_numerical_fit`
(`V17_I_Apply.1`, via `ADVXXZGeneralReleasedRetainedApply`); with the general certificate bound
`certificate_bound` (`V17_N_Closure.1`) and the admissibility of the released instance
`releasedOrdinaryCertificatePhysical` (`released_ordinary_physical_admissible`) it gives
`omegaMM F ≤ tauCert` (`V17_I_Apply.2`, `omegaMM_le_tauCert_allFields_of`), and
`tauCert < 2371339/10^6` (`tauCert_lt_target_kernel`) finishes (`omegaMM_lt_target_allFields_of`;
both steps in `ADVXXZGeneralClosureConditional`).
-/

universe u

namespace OmegaBound.ADVXXZGeneral

/-- Frozen `V17_I_Apply.4`: the retained residual of the released fit. -/
theorem released_retained_residual : P2M.V17_I_Apply.S_V17_I_Apply_4 :=
  residual_of_level3_leg released_level3_retained_leg

/-- Frozen `V17_I_Apply.1`: the released numerical fit. -/
theorem released_numerical_fit : S_V17_I_Apply_1 :=
  apply1_of_level3_leg released_level3_retained_leg

/-- Frozen `V17_I_Apply.2`: `omegaMM F ≤ tauCert` for every field. -/
theorem omegaMM_le_tauCert_allFields : S_V17_I_Apply_2.{u} :=
  omegaMM_le_tauCert_allFields_of released_numerical_fit certificate_bound.{u}

/-- Frozen `T8_F.1`: `omegaMM F < 2371339/10^6` for every field. -/
theorem omegaMM_lt_target_allFields : S_T8_F_1.{u} :=
  omegaMM_lt_target_allFields_of omegaMM_le_tauCert_allFields.{u}

end OmegaBound.ADVXXZGeneral

namespace OmegaBound.ADVXXZFinal

/-- Frozen `V17_I_Apply.3`: the rational instance `omegaMM ℚ ≤ tauCert`. -/
theorem omegaMM_le_tauCert114 : S_V17_I_Apply_3 :=
  omegaMM_le_tauCert114_of ADVXXZGeneral.omegaMM_le_tauCert_allFields.{0}

/-- Frozen `T8.1`: `omegaMM ℚ < 2371339/10^6`. -/
theorem omegaMM_lt_target114 : _root_.S_T8_1 :=
  omegaMM_lt_target114_of ADVXXZGeneral.omegaMM_lt_target_allFields.{0}

example : OmegaBound.omegaMM ℚ < (2371339 : ℝ) / 10 ^ 6 := omegaMM_lt_target114

end OmegaBound.ADVXXZFinal

#print axioms OmegaBound.ADVXXZGeneral.released_numerical_fit
#print axioms OmegaBound.ADVXXZGeneral.omegaMM_lt_target_allFields
#print axioms OmegaBound.ADVXXZFinal.omegaMM_lt_target114

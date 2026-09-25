import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows
import OmegaBound.ADVXXZT6Round130fSoundness

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZGeneral
open OmegaBound.ADVXXZT6Round130

namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000

private noncomputable abbrev oldData30 :=
  OmegaBound.ADVXXZT6Round82.releasedCorrectedData

theorem released_role_projection30 (r : Fin 6) (W : Side) :
    OmegaBound.ADVXXZT6Round130f.physicalRole130f r W =
      releasedConstituentSpec.toPaper.perm r W := rfl

theorem released_alpha_projection30 (p : Fin 126) (r : Fin 6) :
    oldData30.alpha p r = releasedConstituentSpec.toPaper.alpha p r := rfl

theorem released_marginal_projection30 (p : Fin 126) (r : Fin 6)
    (W : Side) :
    constituentMarginal oldData30 p r W =
      constituentMarginal releasedConstituentSpec.toPaper p r W := by
  unfold constituentMarginal
  rfl

theorem released_betaRegion_projection30 (p : Fin 126) (r : Fin 6)
    (W : Side) :
    oldData30.betaRegion W p r =
      releasedConstituentSpec.toPaper.betaRegion W p r := rfl

theorem released_eta_nats_projection30 (p : Fin 126) (r : Fin 6)
    (x y z : Side) :
    constituentEtaNats130 oldData30 p r x y z =
      constituentEtaNats130 releasedConstituentSpec.toPaper p r x y z := by
  unfold constituentEtaNats130 constituentAverage symWeight
  rfl

theorem released_lambda_nats_projection30 (p : Fin 126) (r : Fin 6)
    (x y z : Side) :
    constituentLambdaNats130 oldData30 p r x y z =
      constituentLambdaNats130 releasedConstituentSpec.toPaper p r x y z := by
  unfold constituentLambdaNats130 symWeight
  rfl

end OmegaBound.ADVXXZGeneral

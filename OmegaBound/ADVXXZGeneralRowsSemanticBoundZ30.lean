import OmegaBound.ADVXXZGeneralRowsSemanticCore30

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT6Round130
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000

theorem semantic_parent_le_paper_Z30 (dual : DualQ130f) (p : Fin 126)
    (r : Fin 6) :
    (releasedCertificate.D ^ 2 : ℝ) *
        semanticQuantity130f dual p r (roleIndex30 .Z) ≤
      Real.log 2 * paperParent30 p r .Z := by
  let d := releasedConstituentSpec.toPaper
  let weight : ℝ := d.A p r * (releasedParent.baseN p : ℝ)
  have hscale (E : ℝ) :
      (releasedCertificate.D ^ 2 : ℝ) * ((coefficientQ130f r p : ℝ) * E) =
        weight * E :=
    (mul_assoc _ _ _).symm.trans
      (congrArg (fun c : ℝ => c * E) (coefficient_scale30 r p))
  dsimp only [roleIndex30, semanticQuantity130f]
  rw [hscale]
  rw [released_role_projection30, released_betaRegion_projection30,
    released_lambda_nats_projection30]
  change weight *
      (splitEntropyNats130 (d.betaRegion (d.perm r .Z) p r) -
        constituentLambdaNats130 d p r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)) ≤
    Real.log 2 * (weight *
      (splitEntropy (d.betaRegion (d.perm r .Z) p r) -
        constituentLambda d p r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)))
  apply le_of_eq
  rw [← log_two_mul_splitEntropy130, ← log_two_mul_constituentLambda130]
  change weight * _ = _
  ring

end OmegaBound.ADVXXZGeneral

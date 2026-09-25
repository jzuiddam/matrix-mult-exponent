import OmegaBound.ADVXXZT6Round82C5KernelChecked
import OmegaBound.ADVXXZT6Round82Clauses
import OmegaBound.ADVXXZT6Round82RealDisintegration
import OmegaBound.ADVXXZT6Round82SurfaceLogic

/-! # C5 for the released data: the parent-mixture clause -/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round82

open ADVXXZPaper
open ADVXXZCertificateConstituentClosure
open ADVXXZT6Round19
open ADVXXZT6Round79
open ADVXXZT9R16PositiveParents (releasedPositiveInput)

private theorem probR_eq_of_cleared_coordinate
    {i : Type*} [Fintype i] (P Q : ADVXXZ.RatDist i) (x : i)
    (h : P.num x * Q.den = Q.num x * P.den) : P.probR x = Q.probR x := by
  rw [ADVXXZ.RatDist.probR, ADVXXZ.RatDist.probR]
  apply (div_eq_div_iff P.denR_ne_zero Q.denR_ne_zero).2
  exact_mod_cast h

/-- The cleared all-row census is exactly normalized equality with the released parent law. -/
theorem released_parent_identification (W : Side) (t : Fin 126) (sigma : ADVXXZ.Chunk 4) :
    (releasedPositiveInput.beta W t).probR sigma =
      (certificateParentDist W t).probR sigma := by
  cases W with
  | X =>
      change (ADVXXZT2.parBeta t.1 0).probR sigma =
        (certificateParentDist .X t).probR sigma
      exact probR_eq_of_cleared_coordinate _ _ sigma (released_cleared_C5 t .X sigma)
  | Y =>
      change (ADVXXZT2.parBeta t.1 1).probR sigma =
        (certificateParentDist .Y t).probR sigma
      exact probR_eq_of_cleared_coordinate _ _ sigma (released_cleared_C5 t .Y sigma)
  | Z =>
      change (ADVXXZT2.parBeta t.1 2).probR sigma =
        (certificateParentDist .Z t).probR sigma
      exact probR_eq_of_cleared_coordinate _ _ sigma (released_cleared_C5 t .Z sigma)

/-- C5 closes for every parent, every physical side, and all 81 complete words. -/
theorem released_parent_mixture :
    RegionalMixtureClause releasedPositiveInput releasedCorrectedData := by
  intro W t sigma
  calc
    (releasedPositiveInput.beta W t).probR sigma =
        (certificateParentDist W t).probR sigma := released_parent_identification W t sigma
    _ = ∑ r, releasedCorrectedData.A t r *
        (releasedCorrectedData.betaRegion W t r).probR sigma :=
      certificateParentDist_probR W t sigma

end OmegaBound.ADVXXZT6Round82

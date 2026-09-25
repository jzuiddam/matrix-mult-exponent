import OmegaBound.ADVXXZT6Round82RealDisintegration

/-!
# C9 for the real disintegration

C9 at the corrected scale, for the actual released child CSDs and simplex rows.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

open Finset

namespace OmegaBound.ADVXXZT6Round82

open ADVXXZPaper
open ADVXXZCertificateConstituentClosure
open ADVXXZT6Round19
open ADVXXZT6Round79
open ADVXXZT9R16PositiveParents (releasedPositiveInput)

/-- C9 is the same denominator-square lattice discipline as `ADVXXZT6Round79`, written directly
against the released row numerators used by the corrected constructor. -/
theorem released_output_parameters :
    OutputParameterClauseAtScale releasedPositiveInput releasedCorrectedData
      correctedWeightDen := by
  intro x
  simp only [releasedCorrectedData, correctedOutBase, symWeight_eq_add_complement,
    ADVXXZ.RatDist.probR]
  change
    ((releasedPositiveInput.baseN x.1 * (releasedRegionDist x.1).num x.2.1 *
      ((releasedChildRowDist x.1 x.2.1).num (ADVXXZT6Round78.childIndex x.1 x.2.2) +
       (releasedChildRowDist x.1 x.2.1).num
        (ADVXXZT6Round78.childIndex x.1
          (complement releasedPositiveInput x.1 x.2.2))) : Nat) : Real) = _
  simp only [releasedRegionDist, releasedChildRowDist]
  push_cast
  rw [show correctedWeightDen = ADVXXZT2.certDen * ADVXXZT2.certDen by rfl]
  have hD : (ADVXXZT2.certDen : Real) ≠ 0 := by norm_num [ADVXXZT2.certDen]
  field_simp [hD]
  push_cast
  ring

end OmegaBound.ADVXXZT6Round82

import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round26CountingSpine
import OmegaBound.ADVXXZT7Round20ExactSplit

/-!
# The joint denominator of the released certificate

`logical_joint_den_eq_certDen_sq`: the released global joint denominator
`ADVXXZT5.logicalData.joint.den` is `ADVXXZT2.certDen * ADVXXZT2.certDen`, checked on cleared
integers by `decide +kernel`.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Tensor3

namespace OmegaBound.ADVXXZT9R2ScaleAlignment


/-- The released global joint denominator is the square of the common certificate denominator.
This is the cleared-integer lattice relation; no scale-sized object is evaluated. -/
theorem logical_joint_den_eq_certDen_sq :
    ADVXXZT5.logicalData.joint.den = ADVXXZT2.certDen * ADVXXZT2.certDen := by
  decide +kernel

end OmegaBound.ADVXXZT9R2ScaleAlignment

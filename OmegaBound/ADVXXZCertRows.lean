import OmegaBound.ADVXXZBlkChunk
import OmegaBound.ADVXXZCertClose
import OmegaBound.ADVXXZCertMatrix
import OmegaBound.ADVXXZCertificateGlobalData
import OmegaBound.ADVXXZDegenTrans
import OmegaBound.ADVXXZEpsCnt
import OmegaBound.ADVXXZLevel2Closure
import OmegaBound.ADVXXZRegionalCertificateSplitData
import OmegaBound.ADVXXZShufCW
import OmegaBound.ADVXXZEndpointLedger

/-!
# The certificate datum at the endpoint's unreduced width

`dataE` is the fixed no-caller-`beta` certificate datum `ADVXXZEndpointLedger.data`, read as
`GlobalData (2 * 2)`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZCRows

open ADVXXZPaper (GlobalData)

variable {w : ℕ}


/-! ## The certificate datum at the endpoint's unreduced width -/

/-- The committed no-caller-`beta` certificate datum, at the endpoint's `2 * 2`. -/
noncomputable def dataE : GlobalData (2 * 2) := ADVXXZEndpointLedger.data

section RowC


variable {w : ℕ}

end RowC

end ADVXXZCRows
end OmegaBound

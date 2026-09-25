import OmegaBound.ADVXXZCertificateSplitData
import OmegaBound.ADVXXZBlkChunk
import OmegaBound.ADVXXZCertClose
import OmegaBound.ADVXXZCertificateGlobalData
import OmegaBound.ADVXXZDegenTrans
import OmegaBound.ADVXXZEpsCnt
import OmegaBound.ADVXXZLevel2Closure
import OmegaBound.ADVXXZRegionalCertificateSplitData
import OmegaBound.ADVXXZShufCW
import OmegaBound.CertArith
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The fixed complete-split certificate datum

`data` is `ADVXXZCertificateSplitData.certificateGlobalData`: the certificate's global data with
the certificate's own complete-split family as `beta`, so that no caller supplies `beta`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZEndpointLedger


/-- The fixed complete-split certificate datum; no caller supplies `beta`. -/
noncomputable def data : ADVXXZPaper.GlobalData 4 :=
  ADVXXZCertificateSplitData.certificateGlobalData

end ADVXXZEndpointLedger
end OmegaBound

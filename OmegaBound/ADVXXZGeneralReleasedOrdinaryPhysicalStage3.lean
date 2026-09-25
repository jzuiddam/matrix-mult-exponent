import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3Admissible
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem released_ordinary_physical_stage3_admissible :
    ConstituentAdmissibleAt releasedOrdinaryStep3.data
      (releasedOrdinaryCertificatePhysical.D ^ 2) := by
  simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryCertificate] using
    released_ordinary_stage3_step_admissible

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralReleasedOrdinaryPair
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 4000 in
-- The transported record type expands the released stage-two parent and its dependent child type.
theorem released_ordinary_physical_stage2_admissible :
    ConstituentAdmissibleAt releasedOrdinaryStep2.data
      (releasedOrdinaryCertificatePhysical.D ^ 2) := by
  have hb : releasedOrdinaryCertificatePhysical.D ^ 2 = ordinaryD ^ 4 := by
    change (ordinaryD ^ 2) ^ 2 = ordinaryD ^ 4
    ring
  rw [hb]
  exact released_ordinary_stage2_admissible

end OmegaBound.ADVXXZGeneral

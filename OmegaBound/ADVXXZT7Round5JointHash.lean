import OmegaBound.ADVXXZT7SpecialReconstruction

/-!
# The released child-row carrier of the `112` inventory

`Live112Child` is the carrier of released level-2 row ids, and `childRow j` is the enriched
released row at id `j`.

SOURCE: VXXZ24 `analysis_constituent.tex:178-245`.
SOURCE: ADVXXZ24 `constituent.tex:177-230`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 10000

open Finset

namespace OmegaBound
namespace ADVXXZT7Round5JointHash

open ADVXXZT7Enriched

/-- A compact carrier over the released row ids.  Inactive and direct rows have zero positions,
so the dependent sum below contains exactly the 1,104 live `112` rows without elaborating a
large subtype or a filtered-list lookup. -/
abbrev Live112Child := Fin 5508

def childRow (j : Live112Child) : RawEnrichedRow := enrichedRow j

/-! ## Physical labels and compatibility -/

/-! ## Section variables -/

variable [DecidableEq R]

end ADVXXZT7Round5JointHash
end OmegaBound

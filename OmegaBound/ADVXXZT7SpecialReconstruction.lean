import OmegaBound.ADVXXZT7EnrichedTable
import OmegaBound.ADVXXZT2Paired
import OmegaBound.ADVXXZT7SpecialInventory
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Reconstructed complete-split witnesses: the table lookup

The released record stops at `(node, kind, rotation, fraction, mu)`.  `releasedAt_eq_dataById`
identifies the `getD` lookup of the enriched integer extension with the typed released-table
lookup `ADVXXZT7SpecialInventory.dataById`.

SOURCE: ADVXXZ `constituent.tex:115-127` (complete-split witnesses and product law).
SOURCE: VXXZ24 `analysis_constituent.tex:18-41` (the 144 direct matrix leaves).
SOURCE: `TermInfoLv2.m:120-180` (the five pointwise laws and `Rot3c`).
-/

set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT7SpecialReconstruction

open ADVXXZCertSemantic (Level2TermId)
open ADVXXZT7SpecialInventory (baseCopies baseCorners copies dataById occurrenceData naturalDen natural_table_law)
open ADVXXZT7Enriched


/-- The generated `getD` lookup is the typed released-table lookup. -/
theorem releasedAt_eq_dataById (i : Level2TermId) : releasedAt i.1 = dataById i := by
  apply congrArg dataById
  apply Fin.ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]



end ADVXXZT7SpecialReconstruction
end OmegaBound

import OmegaBound.ADVXXZT6Round21TypeCount
import OmegaBound.ADVXXZT7Round5JointHash
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Finset.Prod
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The enriched child rows are addressed by their own node id

`childRow_node`: for every released level-2 row id `j`, the enriched row `childRow j` carries
node id `j`.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option maxRecDepth 24000

open Finset

namespace OmegaBound.ADVXXZT7Round20ExactSplit

open ADVXXZT7Enriched
open ADVXXZT7Round5JointHash
open ADVXXZT7SpecialInventory
open ADVXXZT7SpecialReconstruction


theorem childRow_node (j : Live112Child) : (childRow j).node = j := by
  native_decide +revert

end OmegaBound.ADVXXZT7Round20ExactSplit

import OmegaBound.ADVXXZT2Paired
import OmegaBound.ADVXXZReleasedL2Family

/-!
# Width-two word helpers and the released level-2 record array

`isWord`, `delta` and `half` are the exact rational indicator laws on width-two words, and
`termDataArray` is the released level-2 record table as an `Array`.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

open Finset

namespace OmegaBound
namespace ADVXXZT6

open ADVXXZ (Chunk)
open ADVXXZReleasedTree (ReleasedLevel2TermData releasedLevel2TermDataTable)

/-! ## Exact rational level-2 complete-split laws -/

def isWord (w : Chunk 2) (a b : ℕ) : Bool := w 0 == a && w 1 == b

def delta (a b : ℕ) (w : Chunk 2) : ℚ := if isWord w a b then 1 else 0

def half (a b : ℕ) (w : Chunk 2) : ℚ :=
  if isWord w a b || isWord w b a then 1 / 2 else 0

def termDataArray : Array ReleasedLevel2TermData := releasedLevel2TermDataTable.toArray

end ADVXXZT6
end OmegaBound

import OmegaBound.ADVXXZGeneralRowsSemanticBoundX30
import OmegaBound.ADVXXZGeneralRowsSemanticBoundY30
import OmegaBound.ADVXXZGeneralRowsSemanticBoundZ30
import OmegaBound.ADVXXZT6Round130fEvaluator

/-!
The semantic parent bound `PaperSemanticParentBound30`, assembled side by side from the `X`,
`Y` and `Z` semantic bounds.
-/

open scoped BigOperators
open OmegaBound.ADVXXZPaper OmegaBound.ADVXXZT6Round130e
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

theorem semantic_parent_bound : PaperSemanticParentBound30 := by
  intro dual p r W
  cases W with
  | X => exact semantic_parent_le_paper_X30 dual p r
  | Y => exact semantic_parent_le_paper_Y30 dual p r
  | Z => exact semantic_parent_le_paper_Z30 dual p r

end OmegaBound.ADVXXZGeneral

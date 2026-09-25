import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round61ReleasedCountProbe
import OmegaBound.ADVXXZT6Round82RealDisintegration

set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round130

open OmegaBound.ADVXXZT6DenominatorData

theorem releasedChildRawAt_eq_left130
    (W : OmegaBound.ADVXXZPaper.Side) (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.1).length) :
    OmegaBound.ADVXXZT6Round82.releasedChildRawAt W p r d =
      (OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray.getD
        (OmegaBound.ADVXXZT2.rowOf
          (OmegaBound.ADVXXZT6SplitTargetData.occurrence p r d)).left.1
        OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode).raw
          (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
  let u := (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d
  have hd : OmegaBound.ADVXXZT6Round78.childIndex p u = d :=
    (OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply d
  rw [← hd]
  unfold OmegaBound.ADVXXZT6Round82.releasedChildRawAt
    OmegaBound.ADVXXZT6SplitTargetData.fineRaw
    OmegaBound.ADVXXZT6SplitTargetData.targetNode
    OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
  rw [OmegaBound.ADVXXZT6Round82.kidPat_childIndex, if_pos]
  · rfl
  · have hb := OmegaBound.ADVXXZT6Round78.releasedChildIndexBounds p u
    have hfound := @List.findIdx_getElem _
      (fun v => v == OmegaBound.ADVXXZT6Round78.childTriple p u)
      (OmegaBound.ADVXXZT2.parKids p.1) hb
    have heq :
        (OmegaBound.ADVXXZT2.parKids p.1)[
          OmegaBound.ADVXXZT6Round78.childIndexNat p u]'hb =
            OmegaBound.ADVXXZT6Round78.childTriple p u := by
      simpa [OmegaBound.ADVXXZT6Round78.childIndexNat] using hfound
    simpa [OmegaBound.ADVXXZT6SplitTargetData.patShape,
      OmegaBound.ADVXXZT6Round78.childTriple] using
        (show OmegaBound.ADVXXZT6Round78.childTriple p u ∈
            OmegaBound.ADVXXZT2.parKids p.1 by
          rw [← heq]
          exact List.getElem_mem hb)

end OmegaBound.ADVXXZT6Round130

import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryBase

open OmegaBound.ADVXXZPaper
set_option maxRecDepth 2000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem ordinary_target_boundary_k031_r0_X :
    OrdinaryTargetBoundaryCell .k031 0 .X := by
  intro mu X Y hXY hXZ hYZ i
  fin_cases X <;> fin_cases Y <;> fin_cases i <;>
    simp_all [OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseNum,
      OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseSide,
      OmegaBound.ADVXXZT6Round82.sideIndex, ordinaryMirrorWord]

end OmegaBound.ADVXXZGeneral


import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK022R0X
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK022R1Z
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK022R2Y
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK013R0X
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK013R1Z
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK013R2Y
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK031R0X
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK031R1Z
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK031R2Y
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R0X
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R0Y
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R1X
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R1Z
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R2Y
import OmegaBound.ADVXXZGeneralReleasedOrdinaryBoundaryK004R2Z

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

def ordinaryShapeCoord (W : Side) (s : ℕ × ℕ × ℕ) : ℕ :=
  match W with
  | .X => s.1
  | .Y => s.2.1
  | .Z => s.2.2

theorem ordinary_wordEquiv_reflect (sigma : Chunk 2) :
    OmegaBound.ADVXXZT6SplitTargetData.wordEquiv (reflect sigma) =
      ordinaryMirrorWord
        (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv sigma) := by
  change OmegaBound.ADVXXZT6SplitTargetData.wordId (reflect sigma) =
    ordinaryMirrorWord (OmegaBound.ADVXXZT6SplitTargetData.wordId sigma)
  apply Fin.ext
  simp only [OmegaBound.ADVXXZT6SplitTargetData.wordId, reflect, ordinaryMirrorWord]
  have h0 := (sigma 0).isLt
  have h1 := (sigma 1).isLt
  omega

theorem ordinary_target_boundary_cell_of_zero
    (kind : OmegaBound.ADVXXZLevel2Closure.Kind) (rot : Fin 3)
    (zero : Side)
    (hzero : ordinaryShapeCoord zero
      (OmegaBound.ADVXXZLevel2Closure.shapeAt kind rot) = 0) :
    OrdinaryTargetBoundaryCell kind rot zero := by
  cases kind <;> fin_cases rot <;> cases zero <;>
    simp [ordinaryShapeCoord, OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hzero
  all_goals first
  | exact ordinary_target_boundary_k022_r0_X
  | exact ordinary_target_boundary_k022_r1_Z
  | exact ordinary_target_boundary_k022_r2_Y
  | exact ordinary_target_boundary_k013_r0_X
  | exact ordinary_target_boundary_k013_r1_Z
  | exact ordinary_target_boundary_k013_r2_Y
  | exact ordinary_target_boundary_k031_r0_X
  | exact ordinary_target_boundary_k031_r1_Z
  | exact ordinary_target_boundary_k031_r2_Y
  | exact ordinary_target_boundary_k004_r0_X
  | exact ordinary_target_boundary_k004_r0_Y
  | exact ordinary_target_boundary_k004_r1_X
  | exact ordinary_target_boundary_k004_r1_Z
  | exact ordinary_target_boundary_k004_r2_Y
  | exact ordinary_target_boundary_k004_r2_Z

theorem ordinary_target_raw_boundary
    (d : OmegaBound.ADVXXZT6SplitTargetData.TargetNode) (zero : Side)
    (hzero : ordinaryShapeCoord zero
      (OmegaBound.ADVXXZLevel2Closure.shapeAt d.kind d.rot) = 0)
    (X Y : Side) (hXY : X ≠ Y) (hXZ : X ≠ zero) (hYZ : Y ≠ zero)
    (sigma : Chunk 2)
    (hX : (d.raw (OmegaBound.ADVXXZT6Round82.sideIndex X)).Valid)
    (hY : (d.raw (OmegaBound.ADVXXZT6Round82.sideIndex Y)).Valid) :
    ((d.raw (OmegaBound.ADVXXZT6Round82.sideIndex X)).toDist hX).prob sigma =
      ((d.raw (OmegaBound.ADVXXZT6Round82.sideIndex Y)).toDist hY).prob
        (reflect sigma) := by
  rcases d with ⟨kind, rot, mu⟩
  have hcell := ordinary_target_boundary_cell_of_zero kind rot zero hzero
  have hnum := hcell mu X Y hXY hXZ hYZ
    (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv sigma)
  rw [← ordinary_wordEquiv_reflect sigma] at hnum
  have hquot := congrArg
    (fun n : ℕ => (n : ℚ) /
      (OmegaBound.ADVXXZT6SplitTargetData.targetDen : ℚ)) hnum
  simpa only [OmegaBound.ADVXXZT6SplitTargetData.TargetNode.raw,
    OmegaBound.ADVXXZT6SplitTargetData.RawTarget.toDist,
    RatDist.prob] using hquot

theorem released_ordinary_stage3_child_boundary (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedParent t) :
    BoundaryCompatible u.1
      (fun W => releasedConstituentSpec.betaChild W t r u) := by
  intro zero X Y hXY hXZ hYZ hzero sigma
  let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode
    (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1)
  have hshape := released_child_target_shape t r u
  have hshapeZero : ordinaryShapeCoord zero
      (OmegaBound.ADVXXZLevel2Closure.shapeAt d.kind d.rot) = 0 := by
    cases zero <;> simp only [ordinaryShapeCoord] <;> rw [← hshape] <;>
      simpa [coord] using hzero
  change
    (OmegaBound.ADVXXZT6Round82.certificateBetaChild X t r u).prob sigma =
      (OmegaBound.ADVXXZT6Round82.certificateBetaChild Y t r u).prob
        (reflect sigma)
  simp only [
    OmegaBound.ADVXXZT6Round82.certificateBetaChild,
    OmegaBound.ADVXXZT6Round82.certificateBetaChildAt,
    OmegaBound.ADVXXZT6Round82.releasedChildRawAt,
    OmegaBound.ADVXXZT6SplitTargetData.fineRaw,
    OmegaBound.ADVXXZT6Round82.kidPat_childIndex]
  exact ordinary_target_raw_boundary d zero hshapeZero X Y hXY hXZ hYZ sigma _ _

end OmegaBound.ADVXXZGeneral

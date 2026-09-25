import OmegaBound.ADVXXZT6Round82ChildKernel

open OmegaBound.ADVXXZPaper
set_option maxRecDepth 2000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- Reversal of a base-three encoded width-two word. -/
def ordinaryMirrorWord (i : Fin 9) : Fin 9 :=
  ⟨8 - i.val, by omega⟩

/-- One small symbolic target-row symmetry cell.  The cell fixes the target kind,
rotation, and zero coordinate; it remains uniform in the released `muNum`. -/
def OrdinaryTargetBoundaryCell
    (kind : OmegaBound.ADVXXZLevel2Closure.Kind) (rot : Fin 3)
    (zero : Side) : Prop :=
  ∀ mu (X Y : Side), X ≠ Y → X ≠ zero → Y ≠ zero → ∀ i : Fin 9,
    let d : OmegaBound.ADVXXZT6SplitTargetData.TargetNode := ⟨kind, rot, mu⟩
    d.baseNum (d.baseSide (OmegaBound.ADVXXZT6Round82.sideIndex X)) i =
      d.baseNum (d.baseSide (OmegaBound.ADVXXZT6Round82.sideIndex Y))
        (ordinaryMirrorWord i)

end OmegaBound.ADVXXZGeneral

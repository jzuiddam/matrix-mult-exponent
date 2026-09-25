import OmegaBound.ADVXXZT6SplitTargetIndex
import OmegaBound.ADVXXZT6Round78ReleasedComplement

/-!
# Released child complete-split statement

This is the finite data gate for the real disintegration.  A child shape is read at its
released left occurrence in the committed 5,508-node table.  The side argument is the physical
`X,Y,Z` side, exactly as `TermInfo.m:248-257` reads `complete_split{t}` before concatenating the
left and right child laws.

`ReleasedChildLawFactsAt` covers, at one parent, six constituent regions, admissible child
shapes, three physical sides, and nine width-two words: normalization and the level support
required by C8, read directly from the released complete-split numerators.  The check over all
126 parents is split across the six `native_decide` shards `ADVXXZT6Round82ChildKernel0`–`5`.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round82

open ADVXXZ (Chunk)
open ADVXXZPaper (Side)
open ADVXXZT6SplitTargetData

/-- Paper-side order equals the physical complete-split table order. -/
def sideIndex : Side -> Fin 3
  | .X => 0
  | .Y => 1
  | .Z => 2

/-- The committed raw CSD at one released child-row coordinate. -/
def releasedChildRawAt (W : Side) (t : Fin 126) (r : Fin 6)
    (d : Fin (ADVXXZT2.parKids t.1).length) : RawTarget :=
  fineRaw r t (ADVXXZT6Selection.kidPat t d) (sideIndex W)

/-- Physical coordinate of the released child shape. -/
def releasedChildCoord (W : Side) (t : Fin 126)
    (d : Fin (ADVXXZT2.parKids t.1).length) : Nat :=
  match W with
  | .X => (ADVXXZT6Selection.kidPat t d).1.1
  | .Y => (ADVXXZT6Selection.kidPat t d).1.2.1
  | .Z => (ADVXXZT6Selection.kidPat t d).1.2.2

/-- The statement at one parent, needed to turn every released raw row into a `SplitDist`,
including C8.  Companion modules split the all-parent check into six `native_decide` shards. -/
def ReleasedChildLawFactsAt (t : Fin 126) : Prop :=
  forall W r (d : Fin (ADVXXZT2.parKids t.1).length),
    (releasedChildRawAt W t r d).Valid /\
      forall sigma : Chunk 2,
        (releasedChildRawAt W t r d).nums (wordEquiv sigma) != 0 ->
          ADVXXZ.chunkLvl sigma = releasedChildCoord W t d

instance (t : Fin 126) : Decidable (ReleasedChildLawFactsAt t) := by
  unfold ReleasedChildLawFactsAt releasedChildRawAt releasedChildCoord sideIndex RawTarget.Valid
  infer_instance

end OmegaBound.ADVXXZT6Round82

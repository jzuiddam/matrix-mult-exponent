-- Record types for the released q=5, top-level=3 typed certificate tree.
import OmegaBound.ADVXXZReleasedTreeData
import OmegaBound.ADVXXZReleasedTreeProvenance
import OmegaBound.ADVXXZCertSemantic
import OmegaBound.ADVXXZRetainedAll
import OmegaBound.ADVXXZReleasedL2Family

set_option maxRecDepth 1000000
set_option linter.style.longLine false

/-!
# The released ADVXXZ certificate tree

This module declares the record types of the released-run certificate tree: the dimension,
capacity-row, row-class and level-3 leaf-class enumerations, the 45-entry global shape table
`globalShapeTable`, `SourceCount`, and the `ReleasedTree` structure.
-/

namespace OmegaBound.ADVXXZReleasedTree

open OmegaBound.ADVXXZ
open OmegaBound.ADVXXZCert
open OmegaBound.ADVXXZCertSemantic

inductive Dimension where | x | y | z deriving DecidableEq, Repr

def Dimension.index : Dimension → ℕ | .x => 0 | .y => 1 | .z => 2


inductive CapacityRow where
  | specialL2
  | componentR1 | componentR2 | componentR3 | componentR4 | componentR5 | componentR6
  | globalR1 | globalR2 | globalR3 | globalR4 | globalR5 | globalR6
  | matrix
  deriving DecidableEq, Repr

def CapacityRow.index : CapacityRow → ℕ
  | .specialL2 => 0
  | .componentR1 => 1 | .componentR2 => 2 | .componentR3 => 3
  | .componentR4 => 4 | .componentR5 => 5 | .componentR6 => 6
  | .globalR1 => 7 | .globalR2 => 8 | .globalR3 => 9
  | .globalR4 => 10 | .globalR5 => 11 | .globalR6 => 12
  | .matrix => 13

inductive RowClass where | specialLevel2 | componentLevel3 | global | matrix
  deriving DecidableEq, Repr


/-- One-based released region identity; the special level-2 row is stored in region 1. -/
def CapacityRow.region : CapacityRow → Option (Fin 6)
  | .specialL2 => some ⟨0, by decide⟩
  | .componentR1 => some ⟨0, by decide⟩
  | .componentR2 => some ⟨1, by decide⟩
  | .componentR3 => some ⟨2, by decide⟩
  | .componentR4 => some ⟨3, by decide⟩
  | .componentR5 => some ⟨4, by decide⟩
  | .componentR6 => some ⟨5, by decide⟩
  | .globalR1 => some ⟨0, by decide⟩
  | .globalR2 => some ⟨1, by decide⟩
  | .globalR3 => some ⟨2, by decide⟩
  | .globalR4 => some ⟨3, by decide⟩
  | .globalR5 => some ⟨4, by decide⟩
  | .globalR6 => some ⟨5, by decide⟩
  | .matrix => none

inductive Level3Class where | general | zeroCoordinateLeaf deriving DecidableEq, Repr

def globalShapeTable : List Shape :=
  [(0, 0, 8), (0, 1, 7), (0, 2, 6), (0, 3, 5), (0, 4, 4), (0, 5, 3), (0, 6, 2), (0, 7, 1), (0, 8, 0),
    (1, 0, 7), (1, 1, 6), (1, 2, 5), (1, 3, 4), (1, 4, 3), (1, 5, 2), (1, 6, 1), (1, 7, 0), (2, 0, 6),
    (2, 1, 5), (2, 2, 4), (2, 3, 3), (2, 4, 2), (2, 5, 1), (2, 6, 0), (3, 0, 5), (3, 1, 4), (3, 2, 3),
    (3, 3, 2), (3, 4, 1), (3, 5, 0), (4, 0, 4), (4, 1, 3), (4, 2, 2), (4, 3, 1), (4, 4, 0), (5, 0, 3),
    (5, 1, 2), (5, 2, 1), (5, 3, 0), (6, 0, 2), (6, 1, 1), (6, 2, 0), (7, 0, 1), (7, 1, 0), (8, 0, 0)]

structure SourceCount where
  matSlots : ℕ
  semanticSlots : ℕ
  deriving DecidableEq, Repr

structure ReleasedTree where
  q : ℕ
  topLevel : ℕ
  kappa : ℕ
  globalShapes : List Shape
  level2Shapes : List Shape
  globalTables : List DistSpec
  level3CompleteSplitTables : List DistSpec
  level2CompleteSplitTables : List DistSpec
  level2TermData : List ReleasedLevel2TermData
  level2MatrixRows : Fin 3 → ℝ
  level3MatrixRows : Fin 3 → ℝ
  globalNodes : List GlobalIncidence
  level3Splits : List Level3Incidence
  complements : (spec : DistSpec) → spec.Index → spec.Index
  correctedWeights : (spec : DistSpec) → spec.Index → ℝ
  slotMap : CapacityRow → Dimension → DimensionSlots
  sources : CapacityRow → Dimension → SourceCount
  capacities : CapacityRow → Dimension → ℝ

end OmegaBound.ADVXXZReleasedTree

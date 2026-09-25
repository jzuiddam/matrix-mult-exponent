-- Generated from the development repository's provenance record of the released certificate tree
-- (not part of this release).
-- The release tooling removed unused declarations.
import OmegaBound.ADVXXZCertSemanticBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZReleasedTree

/-- Inclusive, one-based coordinate interval in a released certificate row. -/
structure SlotRange where
  first : ℕ
  last : ℕ
  deriving DecidableEq, Repr

structure DimensionSlots where
  mat : List SlotRange
  semantic : List SlotRange
  deriving DecidableEq, Repr

end OmegaBound.ADVXXZReleasedTree

import OmegaBound.ADVXXZG1Laws

/-!
# G1, part 2: the support and boundary laws over every slot

One `native_decide` evaluation over all `6 * 3 * 45 * 81 = 65610` released
`(region, side, shape, chunk)` slots.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZG1

open ADVXXZ (Chunk)
open ADVXXZHash (Pat)
open ADVXXZPaper (Side)

/-- **EXACT LEVEL SUPPORT AND THE TWO BOUNDARY POINT MASSES, AT EVERY SLOT.**  For each of the
six regions, each of the three legs, each of the `45` level-3 nodes and each of the `81` level-1
words: the entry is nonzero exactly when the word's level is the leg's own coordinate of the
node, and at the two extreme levels the table is the point mass at `0⃗`, resp. `2⃗`. -/
theorem g1_support :
    ∀ (r : Fin 6) (S : Side) (u : Pat (2 * 4)) (c : Chunk 4), SuppOK r S u c := by
  native_decide

end ADVXXZG1
end OmegaBound

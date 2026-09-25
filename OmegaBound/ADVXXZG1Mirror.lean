import OmegaBound.ADVXXZG1Laws

/-!
# G1, part 3: the three complement/reflection laws at their typed indices

One `native_decide` evaluation over all `6 * 45 * 81 = 21870` `(region, shape, word)` triples.  Each of the
three laws of `rmk:assumptions_on_complete_split_dist` is guarded by its own typed index, so the
`j = 0`, `i = 0` and `k = 0` laws are each visited at exactly the `6 * 9 * 81 = 4374` slots where
they are asserted.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZG1

open ADVXXZ (Chunk)
open ADVXXZHash (Pat)

/-- **THE MIRROR/COMPLEMENT LAWS HOLD AT EVERY TYPED INDEX, IN EVERY REGION.** -/
theorem g1_mirror : ∀ (r : Fin 6) (u : Pat (2 * 4)) (c : Chunk 4), MirrorOK r u c := by
  native_decide

end ADVXXZG1
end OmegaBound

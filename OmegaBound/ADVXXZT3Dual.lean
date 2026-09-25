import OmegaBound.ADVXXZT1IncRange

/-!
# Side indexing and the level-3 pattern type

`paperSide` reads the `Fin 3` side index of `ADVXXZHash.lev` as a paper `Side`, and
`univ_nonempty` records that the level-3 patterns `Pat (2 * 4)` form a nonempty type.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT3

open ADVXXZHash (Pat)

/-- The `Fin 3` side index of `ADVXXZHash.lev`, as a paper `Side`. -/
def paperSide : Fin 3 → ADVXXZPaper.Side := ![.X, .Y, .Z]

theorem univ_nonempty : (Finset.univ : Finset (Pat (2 * 4))).Nonempty :=
  ⟨Classical.arbitrary _, Finset.mem_univ _⟩

end ADVXXZT3
end OmegaBound

import OmegaBound.ADVXXZG2Fix
import OmegaBound.ADVXXZReAnchor

/-!
# G2, part 6: the half levels of a released level-3 word

`leftHalfLvl` and `rightHalfLvl` are the levels of the left half (positions `0`, `1`) and of the
right half (positions `2`, `3`) of a level-3 word `Chunk 4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZG2

open ADVXXZ (Chunk)

/-- The level of the left half of a released level-3 word: positions `0` and `1`. -/
def leftHalfLvl (c : Chunk 4) : ℕ := (c 0).val + (c 1).val

/-- The level of the right half: positions `2` and `3`. -/
def rightHalfLvl (c : Chunk 4) : ℕ := (c 2).val + (c 3).val

end ADVXXZG2
end OmegaBound

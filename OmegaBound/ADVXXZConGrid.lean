import OmegaBound.ADVXXZHashPat
import OmegaBound.ADVXXZSplitIface
import OmegaBound.CW90Hash
import Mathlib.Data.List.GetD

/-!
# The three level-1 words of a coordinate pattern

A coordinate pattern `pat : Fin w → Pat (2 * 1)` assigns one level-1 triple to each of the `w`
coordinates of a level-`ℓ` variable.  `ADVXXZCon.patX`, `patY` and `patZ` read off its `X`-, `Y`-
and `Z`-words, the level-1 words `(i_p)_p`, `(j_p)_p` and `(k_p)_p`.
-/

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZCon

open ADVXXZ (Chunk iface SplitDist ApproxConsistent restricts_of_sub)
open ADVXXZHash (Pat Ix Jy Kz)

/-! ## The three level-1 words of a coordinate pattern -/

/-- The `X`-word of a coordinate pattern: the level-1 word `(i_p)_p`. -/
def patX {w : ℕ} (pat : Fin w → Pat (2 * 1)) : Chunk w := fun p => Ix (pat p)

/-- The `Y`-word of a coordinate pattern. -/
def patY {w : ℕ} (pat : Fin w → Pat (2 * 1)) : Chunk w := fun p => Jy (pat p)

/-- The `Z`-word of a coordinate pattern. -/
def patZ {w : ℕ} (pat : Fin w → Pat (2 * 1)) : Chunk w := fun p => Kz (pat p)

end ADVXXZCon

end OmegaBound

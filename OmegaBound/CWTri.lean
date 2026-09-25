import OmegaBound.ASISum
import OmegaBound.BorderRank

/-!
# The triangle indicator

`CW.triInd x y z = [x.2 = y.1] · [y.2 = z.1] · [z.2 = x.1]` for leg coordinates `x : P × Q`,
`y : Q × R`, `z : R × P`: the entry of the matrix multiplication tensor `⟨|P|,|Q|,|R|⟩`.  It
defines the direct sums `CW90Eight.dsT`.
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW

/-! ## Triangle presentations -/

/-- The triangle indicator of a triple of leg coordinates.  This is the entry of the
matrix multiplication tensor `⟨|P|,|Q|,|R|⟩` at `((p,q),(q',r'),(r,p'))`. -/
def triInd {P Q R : Type} [DecidableEq P] [DecidableEq Q] [DecidableEq R]
    (x : P × Q) (y : Q × R) (z : R × P) : ℚ :=
  (if x.2 = y.1 then (1 : ℚ) else 0) * (if y.2 = z.1 then (1 : ℚ) else 0) *
    (if z.2 = x.1 then (1 : ℚ) else 0)

namespace Tri

variable {X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' : Type}
variable [DecidableEq P] [DecidableEq Q] [DecidableEq R]
variable [DecidableEq P'] [DecidableEq Q'] [DecidableEq R']

end Tri

section Merge

variable {Xr Yr Zr P P' Q R : Type}
variable [DecidableEq P] [DecidableEq P'] [DecidableEq Q] [DecidableEq R]

end Merge

end CW

end OmegaBound

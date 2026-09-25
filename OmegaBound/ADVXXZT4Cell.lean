import OmegaBound.ADVXXZT3Dual

/-!
# The `45` released rows are the `45` level-3 shapes

`shapeAt` inverts the released row index `ADVXXZCertRegionalSemantic.shapeIndex` (a bijection by
`ADVXXZT1.shapeIndex_bijective`), and `shapeIndex_shapeAt` is the corresponding round trip.
-/

set_option maxHeartbeats 1000000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZT4

open ADVXXZHash (Pat)

/-! ## §2  The released exponent vector on the `45` level-3 cells -/

/-- The shape at released row `c`.  `ADVXXZCertRegionalSemantic.shapeIndex` is a bijection
(`ADVXXZT1.shapeIndex_bijective`), so the `45` released rows *are* the `45` level-3 shapes. -/
noncomputable def shapeAt : Fin 45 → Pat (2 * 4) :=
  (Equiv.ofBijective _ ADVXXZT1.shapeIndex_bijective).symm


theorem shapeIndex_shapeAt (c : Fin 45) :
    ADVXXZCertRegionalSemantic.shapeIndex (shapeAt c) = c :=
  (Equiv.ofBijective _ ADVXXZT1.shapeIndex_bijective).apply_symm_apply c

end ADVXXZT4
end OmegaBound

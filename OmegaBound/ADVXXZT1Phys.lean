import OmegaBound.ADVXXZG1Parent

/-!
# The released row index and the role transport are bijections

`shapeIndex_bijective`: the released row index `ADVXXZCertRegionalSemantic.shapeIndex` is a
bijection from the level-3 patterns onto the `45` released rows.  `physRow_bijective`: in each of
the six regions, the transport `ADVXXZG1.physRow` between the physical (MATLAB dimension order)
reading of a regional shape simplex and its logical paper-role reading is a permutation of the
`45` rows.  Both are checked by `native_decide`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT1

open ADVXXZHash (Pat)
open ADVXXZG1 (physRow)
open ADVXXZCertRegionalSemantic (shapeIndex)

/-! ## §1  The two transports are bijections -/

/-- The released row index is a bijection of the `45` level-3 nodes. -/
theorem shapeIndex_bijective : Function.Bijective (shapeIndex : Pat (2 * 4) → Fin 45) := by
  refine ⟨?_, ?_⟩
  · intro a b; revert a b; native_decide
  · intro n; revert n; native_decide

/-- **THE ROLE TRANSPORT IS A PERMUTATION OF THE `45` ROWS**, in every region.  This is why
re-pairing the shape simplex through `physRow` cannot move the total grid mass. -/
theorem physRow_bijective (r : Fin 6) : Function.Bijective (physRow r) := by
  refine ⟨?_, ?_⟩
  · intro a b; revert a b; revert r; native_decide
  · intro n; revert n; revert r; native_decide

end ADVXXZT1
end OmegaBound

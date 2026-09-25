import OmegaBound.ADVXXZT6Round19PaperContract
import OmegaBound.ADVXXZT6SplitTargetIndex

/-!
# The released parent partition

The finite, all-parent partition which precedes hashing in `constituent.tex:166-190` and VXXZ24
`analysis_constituent.tex:197-216`.  `partOfOn` is the fibre of an arbitrary finite carrier over a
partition label, and `releasedParentPart r m p` is the fibre of parent `p` in the released
region-`r` carrier `RegionPos r m`; its natural cardinality is the committed integer multiplicity.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT6Round21

open ADVXXZT6Selection (RegionPos)

/-! ## A partition count on an arbitrary finite carrier -/

section ArbitraryCarrier

variable {σ Λ κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype Λ] [DecidableEq Λ] [Fintype κ] [DecidableEq κ]


/-- The fibre of an arbitrary finite carrier over one partition label. -/
def partOfOn (lab : σ -> Λ) (l : Λ) : Finset σ :=
  Finset.univ.filter fun z => lab z = l

end ArbitraryCarrier

/-! ## The released parent partition -/

/-- The parent partition used by the released type class. -/
def releasedParentPart (r : Fin 6) (m : Nat) (p : Fin 126) : Finset (RegionPos r m) :=
  partOfOn (fun z : RegionPos r m => z.1) p

end ADVXXZT6Round21
end OmegaBound

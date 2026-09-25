import OmegaBound.ADVXXZT6Round26CountingSpine

/-!
# The exact released parent coefficient

`releasedParentCoefficient r p` is the parent coefficient `A_{t,r} n_t / n`, read from the
committed integer carrier; `releasedParentCoefficient_eq_rat` identifies it with a given
rational.
-/

set_option maxRecDepth 100000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound.ADVXXZT6Round61

open ADVXXZT6Round21 (releasedParentPart)

/-- The exact released parent coefficient `A_{t,r} n_t / n`, again read from the committed
integer carrier rather than an evaluator decimal. -/
noncomputable def releasedParentCoefficient (r : Fin 6) (p : Fin 126) : Real :=
  ((releasedParentPart r 1 p).card : Real) /
    ((ADVXXZT2.certDen : Real) ^ 4)


theorem releasedParentCoefficient_eq_rat
    (c : ℚ) (r : Fin 6) (p : Fin 126)
    (h : c = (releasedParentPart r 1 p).card /
      ((ADVXXZT2.certDen : ℚ) ^ 4)) :
    releasedParentCoefficient r p = (c : Real) := by
  unfold releasedParentCoefficient
  have hR := congrArg (fun x : ℚ => (x : Real)) h.symm
  push_cast at hR
  exact hR


end OmegaBound.ADVXXZT6Round61

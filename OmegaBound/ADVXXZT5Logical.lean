import OmegaBound.ADVXXZT4Cell

/-!
# The coherent logical six-region datum

`ADVXXZRA.dataR` has a physical `joint` field and already-logical regional split tables, so the
two fields must not be zipped directly.  This module reindexes the joint distribution through the
released `Dims` permutation, exactly once, and transports the shape simplex to logical
addresses; `logicalData` is the resulting datum.
-/

set_option linter.style.longLine false

open Finset

namespace OmegaBound
namespace ADVXXZT5

open ADVXXZ (RatDist)
open ADVXXZPaper (GlobalData Shape)

/-- The released shape address equivalence. -/
noncomputable def releasedShapeEquiv : Shape 4 ≃ Fin 45 :=
  Equiv.ofBijective ADVXXZCertRegionalSemantic.shapeIndex ADVXXZT1.shapeIndex_bijective

/-- Region `r`'s `Dims` permutation on released shape rows. -/
noncomputable def physicalRowEquiv (r : Fin 6) : Fin 45 ≃ Fin 45 :=
  Equiv.ofBijective (ADVXXZG1.physRow r) (ADVXXZT1.physRow_bijective r)

/-- The physical carrier of a logical paper-role shape. -/
noncomputable def physicalShapeEquiv (r : Fin 6) : Shape 4 ≃ Shape 4 :=
  releasedShapeEquiv.trans ((physicalRowEquiv r).trans releasedShapeEquiv.symm)


/-- The dependent six-region permutation `(r,u_logical) ↦ (r,u_physical)`. -/
noncomputable def logicalGlobalEquiv : (Fin 6 × Shape 4) ≃ (Fin 6 × Shape 4) where
  toFun ru := (ru.1, physicalShapeEquiv ru.1 ru.2)
  invFun ru := (ru.1, (physicalShapeEquiv ru.1).symm ru.2)
  left_inv ru := by simp
  right_inv ru := by simp

/-- `dataR.joint`, viewed at logical regional-interface addresses. -/
noncomputable def logicalJoint : RatDist (Fin 6 × Shape 4) :=
  ADVXXZCertificateGlobalData.RatDist.reindex logicalGlobalEquiv ADVXXZRA.dataR.joint

/-- The transported logical shape simplex. -/
noncomputable def logicalAlpha (r : Fin 6) (u : Shape 4) : ℝ :=
  ADVXXZRA.dataR.alpha r (physicalShapeEquiv r u)

/-- A structure barrier used to define the exact logical regional rates without recursion. -/
noncomputable def logicalSkeleton : GlobalData 4 where
  A := ADVXXZRA.dataR.A
  alpha := logicalAlpha
  beta := ADVXXZRA.dataR.beta
  E := fun _ => 0
  perm := ADVXXZRA.dataR.perm
  joint := logicalJoint

/-- **THE RECONCILED RELEASED GLOBAL DATUM.**

Both the joint cell and its regional residual tables use logical paper-role addresses. -/
noncomputable def logicalData : GlobalData 4 :=
  { logicalSkeleton with E := fun r => ADVXXZPaper.globalRegionRate logicalSkeleton r }

end ADVXXZT5
end OmegaBound

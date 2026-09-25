import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical
import OmegaBound.ADVXXZGeneralReleasedOrdinaryAdmissible
import OmegaBound.ADVXXZT2Paired

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- The transported logical table row has the level of the original physical coordinate. -/
theorem physical_coord_transport (W : Side) (r : Fin 6) (u : Shape 4) :
    OmegaBound.ADVXXZG1.rowLvl
        (OmegaBound.ADVXXZG1.roleAt r (physicalSideIndex W))
        (OmegaBound.ADVXXZT2.logRow r
          (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex u)) =
      coord W u := by
  have h := OmegaBound.ADVXXZT2.rowLvl_logRow r
    (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex u) (physicalSideIndex W)
  have hs := OmegaBound.ADVXXZG1.rowShape_shapeIndex u
  cases W <;>
    simpa [physicalSideIndex, OmegaBound.ADVXXZT2.legs, coord, hs] using h

/-- Reading logical roles through their physical indices is again a permutation of the sides. -/
def physicalRole (r : Fin 6) (W : Side) : Side :=
  OmegaBound.ADVXXZG1.roleAt r (physicalSideIndex W)

theorem physicalRole_injective (r : Fin 6) : Function.Injective (physicalRole r) := by
  intro W V
  revert W V
  fin_cases r <;> decide +kernel

/-- The row-indexed logical beta tables obey the boundary reflection law at every logical row. -/
theorem betaIdx_boundary (r : Fin 6) (n : Fin 45) (Z X Y : Side)
    (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hZ : OmegaBound.ADVXXZG1.rowLvl Z n = 0) (sigma : Chunk 4) :
    (OmegaBound.ADVXXZG1.betaIdx r X n).prob sigma =
      (OmegaBound.ADVXXZG1.betaIdx r Y n).prob (reflect sigma) := by
  obtain ⟨u, hu⟩ := OmegaBound.ADVXXZT1.shapeIndex_bijective.2 n
  subst n
  have hZu : coord Z u = 0 := by
    simpa [OmegaBound.ADVXXZG1.rowLvl_shapeIndex,
      OmegaBound.ADVXXZG1.lvlOf_eq_coord] using hZ
  have h := released_global_boundary r u Z X Y hXY hXZ hYZ hZu sigma
  simpa [releasedGlobalSpec, OmegaBound.ADVXXZRA.regionalBeta,
    OmegaBound.ADVXXZG1.betaIdx_shapeIndex] using h

theorem physical_global_joint_eq (r : Fin 6) (u : Shape 4) :
    physicalGlobalSpec.joint.prob (r, u) =
      physicalGlobalSpec.A.prob r * (physicalGlobalSpec.alpha r).prob u := by
  simpa [physicalGlobalSpec, releasedGlobalSpec] using released_global_joint_eq r u

theorem physical_global_support (W : Side) (r : Fin 6) (u : Shape 4) :
    Supported (physicalGlobalSpec.beta W r u) (coord W u) := by
  intro sigma hsigma
  have h := (OmegaBound.ADVXXZT2.betaIdx_support r (physicalRole r W)
    (OmegaBound.ADVXXZT2.logRow r
      (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex u)) sigma).mp hsigma
  simpa [physicalRole, physical_coord_transport] using h

theorem physical_global_boundary (r : Fin 6) (u : Shape 4) :
    BoundaryCompatible u (fun W => physicalGlobalSpec.beta W r u) := by
  intro Z X Y hXY hXZ hYZ hZ sigma
  apply betaIdx_boundary r
    (OmegaBound.ADVXXZT2.logRow r
      (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex u))
    (physicalRole r Z) (physicalRole r X) (physicalRole r Y)
  · exact fun h => hXY (physicalRole_injective r h)
  · exact fun h => hXZ (physicalRole_injective r h)
  · exact fun h => hYZ (physicalRole_injective r h)
  · simpa [physicalRole, physical_coord_transport] using hZ

theorem physical_global_admissible : GlobalAdmissible physicalGlobalSpec where
  roles := releasedPerm_enumerates
  joint_eq := physical_global_joint_eq
  support := physical_global_support
  boundary := physical_global_boundary

end OmegaBound.ADVXXZGeneral

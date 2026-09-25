import OmegaBound.ADVXXZGeneralReleasedInventoryTransportCore
import OmegaBound.ADVXXZGeneralCertScaleV22

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxHeartbeats 2000000 in
-- Normalizing the nested dependent inventory transport exceeds the default heartbeat budget.
/-- The plain global output carrier is exactly the occurrence-preserving `G` inventory tensor.
The inventory masses are `D^4 * joint`; `outerN = D^4*m` is discharged by the floor/cast
normalisation in this wrapper. -/
theorem globalOutputZ_G_transport (C : Certificate) (m : ℕ) (ε : ℚ) :
    OrdinaryTensorTransport
      (inventoryTensorZ C.q (G C) m ε)
      (globalOutputZ C.q C.global (outerN C m) ε) := by
  let e := (Fintype.equivFin (Fin 6 × Shape C.width)).symm
  simpa [G, scaleInventory, globalInventory, globalOutputZ, outerN, e,
      List.map_map, Function.comp_def, mul_assoc, mul_left_comm, mul_comm,
      Nat.cast_mul, Nat.cast_pow] using
    (finRange_inventory_plain_transport C.q m ε
      (fun i => (C.D : ℚ) ^ 4 * C.global.joint.prob (e i))
      (fun i => (e i).2)
      (fun W i => C.global.beta W (e i).1 (e i).2))

end OmegaBound.ADVXXZGeneral
end

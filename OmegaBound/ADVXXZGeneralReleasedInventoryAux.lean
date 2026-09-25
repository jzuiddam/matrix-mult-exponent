import OmegaBound.ADVXXZGeneralInventory
import OmegaBound.ADVXXZT6Round130fDualR0
import OmegaBound.ADVXXZT6Round130fDualR1
import OmegaBound.ADVXXZT6Round130fDualR2
import OmegaBound.ADVXXZT6Round130fDualR3
import OmegaBound.ADVXXZT6Round130fDualR4
import OmegaBound.ADVXXZT6Round130fDualR5
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical
import OmegaBound.ADVXXZGeneralTensorAux

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

abbrev ordinaryLevel2 : Stage 3 := ⟨2, by omega⟩
abbrev ordinaryLevel3 : Stage 3 := ⟨3, by omega⟩


def OrdinaryTensorTransport (U V : ITensor) : Prop :=
  ∃ (eX : U.X ≃ V.X) (eY : U.Y ≃ V.Y) (eZ : U.Z ≃ V.Z),
    ∀ x y z, U.tensor x y z = V.tensor (eX x) (eY y) (eZ z)

end OmegaBound.ADVXXZGeneral
end

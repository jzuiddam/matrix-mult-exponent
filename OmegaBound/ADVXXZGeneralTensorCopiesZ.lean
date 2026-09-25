import OmegaBound.ADVXXZGeneralTensor

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def copiesZ (k : ℕ) (T : ITensor) : ITensor :=
  { X := Fin k × T.X
    Y := Fin k × T.Y
    Z := Fin k × T.Z
    tensor := OmegaBound.ADVXXZHoles.famDS Finset.univ (fun _ : Fin k => T.tensor) }

end OmegaBound.ADVXXZGeneral
end

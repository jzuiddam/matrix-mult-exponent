import OmegaBound.ADVXXZGeneralCertComplete
import OmegaBound.ADVXXZGeneralCertInventory
import OmegaBound.ADVXXZGeneralTensorAux
import OmegaBound.ADVXXZGeneralStageCore

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def IntegralNumericalProduction (C : Certificate) (f : NumericalFamily) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m → ∃ N : ℕ,
    PolyDegeneratesAt ℤ N
      (copiesZ (f.Q ε m) (topZ C.q C.width (outerN C m))).tensor
      (copiesZ (f.V ε m) (matMulZ (f.a ε m) (f.b ε m) (f.c ε m))).tensor

end OmegaBound.ADVXXZGeneral
end

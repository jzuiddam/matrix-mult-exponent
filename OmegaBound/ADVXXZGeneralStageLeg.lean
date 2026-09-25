import OmegaBound.ADVXXZGeneralTensor

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The physical tensor leg selected by a side. -/
def ITensor.leg (T : ITensor) : Side → Type
  | .X => T.X
  | .Y => T.Y
  | .Z => T.Z

end OmegaBound.ADVXXZGeneral
end

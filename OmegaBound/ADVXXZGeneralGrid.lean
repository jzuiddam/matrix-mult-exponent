import OmegaBound.ADVXXZGeneralCertCore

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def ConstituentGridDimension {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) : ℕ :=
  3 * ∑ _x : ConstituentTerm p, Fintype.card (Chunk w)

def gridDimension {w : ℕ} (g : GlobalSpec w) : ℕ :=
  3 * 6 * Fintype.card (Shape w) * Fintype.card (Chunk w)

end OmegaBound.ADVXXZGeneral
end

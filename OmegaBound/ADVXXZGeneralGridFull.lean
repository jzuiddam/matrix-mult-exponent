import OmegaBound.ADVXXZGeneralCertComplete

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def FullGrid {w : ℕ} (g : GlobalSpec w) (n : ℕ) (ε : ℚ) :=
  {ξ : ExactGrid g n // ∀ W r u,
    let k := (n*g.joint.prob (r,u)).floor.toNat
    0 < k → ∀ σ, |(ξ.count W r u σ : ℚ)/k - (g.beta W r u).prob σ| ≤ ε}

end OmegaBound.ADVXXZGeneral
end

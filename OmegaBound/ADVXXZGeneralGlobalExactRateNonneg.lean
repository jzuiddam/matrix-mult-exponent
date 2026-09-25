import OmegaBound.ADVXXZGeneralGlobalExactRateYZ

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section

/-- Every regional rate of every literal exact grid is nonnegative.
    The X branch is the maximum-entropy penalty bound; the Y and Z branches are entropy
    concavity for the paper's grouped mixtures. -/
theorem globalRegionRate_nonneg27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) :
    0 ≤ globalRegionRate (globalExactGridData27 g xi) r := by
  unfold globalRegionRate
  dsimp only [globalExactGridData27, GlobalSpec.toPaper]
  exact le_min (globalRegionRate_x_nonneg27 g xi r)
    (le_min (globalRegionRate_eta_nonneg27 g xi r)
      (globalRegionRate_lambda_nonneg27 g xi r))

end
end OmegaBound.ADVXXZGeneral
end

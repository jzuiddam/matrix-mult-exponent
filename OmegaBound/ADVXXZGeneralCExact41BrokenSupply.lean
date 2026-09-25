import OmegaBound.ADVXXZGeneralCExact41SelectionCount

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section

/-- The broken-supply statement, from the proved selection-count bound. -/
theorem constituent_grid_broken_supply41 : S_constituent_grid_broken_supply33 :=
  constituent_grid_broken_supply36_of_selection_count constituent_grid_selection_count41

-- Exact display-type probe.
example : S_constituent_grid_broken_supply33 := constituent_grid_broken_supply41

end
end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR3
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR4
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR5

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 3000

theorem released_ordinary_census_second_half :
    ((∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((3 : Fin 6), j)).val).length) +
      (∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((4 : Fin 6), j)).val).length) +
      (∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((5 : Fin 6), j)).val).length) = 459) ∧
    ((∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((3 : Fin 6), j)) r)) +
      (∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((4 : Fin 6), j)) r)) +
      (∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((5 : Fin 6), j)) r)) = 552) := by
  have h3 := released_ordinary_census_block_r3
  have h4 := released_ordinary_census_block_r4
  have h5 := released_ordinary_census_block_r5
  unfold ReleasedOrdinaryCensusBlock at h3 h4 h5
  constructor
  · rw [h3.1, h4.1, h5.1]
  · rw [h3.2, h4.2, h5.2]

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR0
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR1
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusR2

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 3000

theorem released_ordinary_census_first_half :
    ((∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((0 : Fin 6), j)).val).length) +
      (∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((1 : Fin 6), j)).val).length) +
      (∑ j : Fin 21,
        (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv ((2 : Fin 6), j)).val).length) = 459) ∧
    ((∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((0 : Fin 6), j)) r)) +
      (∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((1 : Fin 6), j)) r)) +
      (∑ j : Fin 21, ∑ r : Fin 6,
        Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv ((2 : Fin 6), j)) r)) = 552) := by
  have h0 := released_ordinary_census_block_r0
  have h1 := released_ordinary_census_block_r1
  have h2 := released_ordinary_census_block_r2
  unfold ReleasedOrdinaryCensusBlock at h0 h1 h2
  constructor
  · rw [h0.1, h1.1, h2.1]
  · rw [h0.2, h1.2, h2.2]

end OmegaBound.ADVXXZGeneral

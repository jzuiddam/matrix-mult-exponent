import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusBase

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable def releasedConstituentBlockCount (b : Fin 6) : ℕ :=
  ∑ j : Fin 21,
    (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv (b, j)).val).length

noncomputable def releasedOccurrenceBlockCount (b : Fin 6) : ℕ :=
  ∑ j : Fin 21, ∑ r : Fin 6,
    Fintype.card (ReleasedOrdinaryChildFiber (finProdFinEquiv (b, j)) r)

noncomputable def releasedOccurrenceLinearCount : ℕ :=
  ∑ t : Fin 126, ∑ r : Fin 6, Fintype.card (ReleasedOrdinaryChildFiber t r)

noncomputable def releasedOccurrenceBlockSumCount : ℕ :=
  ∑ b : Fin 6, releasedOccurrenceBlockCount b

noncomputable def releasedConstituentFirstHalfCount : ℕ :=
  releasedConstituentBlockCount 0 + releasedConstituentBlockCount 1 +
    releasedConstituentBlockCount 2

noncomputable def releasedConstituentSecondHalfCount : ℕ :=
  releasedConstituentBlockCount 3 + releasedConstituentBlockCount 4 +
    releasedConstituentBlockCount 5

noncomputable def releasedOccurrenceFirstHalfCount : ℕ :=
  releasedOccurrenceBlockCount 0 + releasedOccurrenceBlockCount 1 +
    releasedOccurrenceBlockCount 2

noncomputable def releasedOccurrenceSecondHalfCount : ℕ :=
  releasedOccurrenceBlockCount 3 + releasedOccurrenceBlockCount 4 +
    releasedOccurrenceBlockCount 5

noncomputable def releasedConstituentTermCount : ℕ :=
  6 * (releasedConstituentFirstHalfCount + releasedConstituentSecondHalfCount)

noncomputable def releasedOrdinaryOccurrenceCount : ℕ :=
  releasedOccurrenceFirstHalfCount + releasedOccurrenceSecondHalfCount

end OmegaBound.ADVXXZGeneral

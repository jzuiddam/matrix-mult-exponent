import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusCounts
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusFirstHalf

namespace OmegaBound.ADVXXZGeneral

theorem releasedOccurrence_first_half_count :
    releasedOccurrenceBlockCount 0 + releasedOccurrenceBlockCount 1 +
      releasedOccurrenceBlockCount 2 = 552 := by
  unfold releasedOccurrenceBlockCount
  exact released_ordinary_census_first_half.2

theorem releasedConstituent_first_half_count :
    releasedConstituentFirstHalfCount = 459 := by
  unfold releasedConstituentFirstHalfCount releasedConstituentBlockCount
  exact released_ordinary_census_first_half.1

end OmegaBound.ADVXXZGeneral

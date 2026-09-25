import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusCounts
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusSecondHalf

namespace OmegaBound.ADVXXZGeneral

theorem releasedOccurrence_second_half_count :
    releasedOccurrenceBlockCount 3 + releasedOccurrenceBlockCount 4 +
      releasedOccurrenceBlockCount 5 = 552 := by
  unfold releasedOccurrenceBlockCount
  exact released_ordinary_census_second_half.2

theorem releasedConstituent_second_half_count :
    releasedConstituentSecondHalfCount = 459 := by
  unfold releasedConstituentSecondHalfCount releasedConstituentBlockCount
  exact released_ordinary_census_second_half.1

end OmegaBound.ADVXXZGeneral

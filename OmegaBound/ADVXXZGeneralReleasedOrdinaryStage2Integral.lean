import OmegaBound.ADVXXZGeneralReleasedOrdinaryIntegralHelpers

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem released_ordinary_stage2_integral :
    StepIntegralAt releasedOrdinaryStep2.input releasedOrdinaryStep2.data
      (releasedOrdinaryCertificate.D ^ 2) := by
  refine ⟨by decide +kernel, ?_⟩
  intro t r
  refine ⟨?_, ?_⟩
  · apply integral_nat_mul_prob
    change 1 ∣ (ordinaryD ^ 2) ^ 2
    exact one_dvd _
  · intro u
    refine ⟨?_, ?_, ?_⟩
    · apply integral_nat_mul_two_probs
      change 1 * ordinaryD ∣ (ordinaryD ^ 2) ^ 2
      refine ⟨ordinaryD ^ 3, ?_⟩
      ring
    · intro W sigma tau
      apply integral_nat_mul_four_probs
      change 1 * ordinaryD * 1 * 1 ∣ (ordinaryD ^ 2) ^ 2
      refine ⟨ordinaryD ^ 3, ?_⟩
      ring
    · intro W sigma
      simpa using integral_nat_mul_prob
        (releasedOrdinaryStep2.data.outBase ⟨t, r, u⟩) 1
        (releasedOrdinaryStep2.data.betaChild W t r u) sigma
        (show (releasedOrdinaryStep2.data.betaChild W t r u).den ∣
          releasedOrdinaryStep2.data.outBase ⟨t, r, u⟩ by
            change 1 ∣ releasedOrdinaryStep2.data.outBase ⟨t, r, u⟩
            exact one_dvd _)

end OmegaBound.ADVXXZGeneral

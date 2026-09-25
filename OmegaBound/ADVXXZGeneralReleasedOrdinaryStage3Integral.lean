import OmegaBound.ADVXXZGeneralReleasedOrdinaryIntegralHelpers

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem released_ordinary_stage3_integral :
    StepIntegralAt releasedOrdinaryStep3.input releasedOrdinaryStep3.data
      (releasedOrdinaryCertificate.D ^ 2) := by
  refine ⟨by decide +kernel, ?_⟩
  intro t r
  refine ⟨?_, ?_⟩
  · apply integral_nat_mul_prob
    change ordinaryD ∣ (ordinaryD ^ 2) ^ 2
    refine ⟨ordinaryD ^ 3, ?_⟩
    ring
  · intro u
    refine ⟨?_, ?_, ?_⟩
    · apply integral_nat_mul_two_probs
      change ordinaryD * ordinaryD ∣ (ordinaryD ^ 2) ^ 2
      refine ⟨ordinaryD ^ 2, ?_⟩
      ring
    · intro W sigma tau
      apply integral_nat_mul_four_probs
      change ordinaryD * ordinaryD * ordinaryD * ordinaryD ∣
        (ordinaryD ^ 2) ^ 2
      refine ⟨1, ?_⟩
      ring
    · intro W sigma
      simpa using integral_nat_mul_prob
        (releasedOrdinaryStep3.data.outBase ⟨t, r, u⟩) 1
        (releasedOrdinaryStep3.data.betaChild W t r u) sigma
        (show (releasedOrdinaryStep3.data.betaChild W t r u).den ∣
          releasedOrdinaryStep3.data.outBase ⟨t, r, u⟩ by
            change ordinaryD ∣ ordinaryD ^ 4 *
              releasedConstituentSpec.outBase ⟨t, r, u⟩
            refine ⟨ordinaryD ^ 3 *
              releasedConstituentSpec.outBase ⟨t, r, u⟩, ?_⟩
            ring)

end OmegaBound.ADVXXZGeneral

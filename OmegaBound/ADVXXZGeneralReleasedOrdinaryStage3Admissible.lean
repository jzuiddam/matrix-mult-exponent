import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3Mixture
import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3Boundary

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem released_ordinary_stage3_admissible :
    ConstituentAdmissibleAt releasedConstituentSpec (ordinaryD ^ 2) where
  roles := released_ordinary_stage3_roles
  mixture := released_ordinary_stage3_mixture
  pair_mixture := released_ordinary_stage3_pair_mixture
  regional_support := released_ordinary_stage3_regional_support
  child_support := released_ordinary_stage3_child_support
  child_boundary := released_ordinary_stage3_child_boundary
  out_eq := released_ordinary_stage3_out_eq

theorem released_ordinary_stage3_step_admissible :
    ConstituentAdmissibleAt releasedOrdinaryStep3.data
      (releasedOrdinaryCertificate.D ^ 2) := by
  refine
    { roles := ?_
      mixture := ?_
      pair_mixture := ?_
      regional_support := ?_
      child_support := ?_
      child_boundary := ?_
      out_eq := ?_ }
  · simpa [releasedOrdinaryStep3, ConstituentSpec.atScale] using
      released_ordinary_stage3_roles
  · intro W t sigma
    simpa [releasedOrdinaryStep3, ConstituentSpec.atScale, scaleParent] using
      released_ordinary_stage3_mixture W t sigma
  · intro W t r sigma
    simpa [releasedOrdinaryStep3, ConstituentSpec.atScale, scaleParent] using
      released_ordinary_stage3_pair_mixture W t r sigma
  · intro W t r
    simpa [releasedOrdinaryStep3, ConstituentSpec.atScale, scaleParent] using
      released_ordinary_stage3_regional_support W t r
  · intro W t r u
    simpa [releasedOrdinaryStep3, ConstituentSpec.atScale, scaleParent] using
      released_ordinary_stage3_child_support W t r u
  · intro t r u
    simpa [releasedOrdinaryStep3, ConstituentSpec.atScale, scaleParent] using
      released_ordinary_stage3_child_boundary t r u
  · intro t r u
    have h := released_ordinary_stage3_out_eq t r u
    change
      ((ordinaryD ^ 4 * releasedConstituentSpec.outBase ⟨t, r, u⟩ : ℕ) : ℚ) =
        (((ordinaryD ^ 2) ^ 2 : ℕ) : ℚ) *
          ((ordinaryD ^ 2 * releasedParent.baseN t : ℕ) : ℚ) *
          (releasedConstituentSpec.A t).prob r *
          ((releasedConstituentSpec.alpha t r).prob u +
            (releasedConstituentSpec.alpha t r).prob
              (complement releasedParent t u))
    push_cast at h ⊢
    rw [h]
    have hfour : (ordinaryD : ℚ) ^ 4 = ((ordinaryD : ℚ) ^ 2) ^ 2 := by
      ring
    rw [hfour]
    ring

end OmegaBound.ADVXXZGeneral

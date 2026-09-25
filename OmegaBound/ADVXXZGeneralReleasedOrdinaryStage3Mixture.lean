import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3
import OmegaBound.ADVXXZT6Round82Closure

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
namespace OmegaBound.ADVXXZGeneral

private theorem stage3_mixture_prob_cast {ι : Type*} [Fintype ι]
    (P : RatDist ι) (i : ι) : ((P.prob i : ℚ) : ℝ) = P.probR i := by
  simp [RatDist.prob, RatDist.probR]

/-- The released parent-mixture law, transported from the exact real-valued table statement
to the rational probabilities stored by `ConstituentSpec`. -/
theorem released_ordinary_stage3_mixture (W : Side) (t : Fin 126)
    (sigma : Chunk 4) :
    (releasedParent.beta W t).prob sigma =
      ∑ r, (releasedConstituentSpec.A t).prob r *
        (releasedConstituentSpec.betaRegion W t r).prob sigma := by
  apply (Rat.cast_injective : Function.Injective ((↑·) : ℚ → ℝ))
  simp only [Rat.cast_sum, Rat.cast_mul, stage3_mixture_prob_cast]
  simpa only [releasedParent, releasedConstituentSpec] using
    OmegaBound.ADVXXZT6Round82.released_parent_mixture W t sigma

end OmegaBound.ADVXXZGeneral

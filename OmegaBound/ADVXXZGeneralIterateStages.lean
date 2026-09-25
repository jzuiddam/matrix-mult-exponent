import PLATFORM.Statements.«V17_C_Exact.3»
import PLATFORM.Statements.«V17_C_Exact.4»
import PLATFORM.Statements.«V17_N_Iterate.1»
import OmegaBound.ADVXXZGeneralAmend27N
import OmegaBound.ADVXXZGeneralCExact33Statements
import OmegaBound.ADVXXZGeneralIterateStagesAssembly

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The finite global/constituent recursion, conditional on three constituent-stage
propositions; they are discharged in `ADVXXZGeneralIterateStagesUnconditional`. -/
theorem iterate_stages_of_constituent :
    S_V17_C_Exact_3.{u} → S_V17_C_Exact_4.{u} →
      S_constituent_pooled_positive33 → S_V17_N_Iterate_1 := by
  intro _hexact _hpositive hpool C hC
  let Q := iterateFinalQ C hC hpool
  let V := iterateFinalV C hC hpool
  let f := boundaryNumericalFamily C Q V
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    simpa [f, Q, V, boundaryNumericalFamily] using
      iterate_all_stages_integral C hC hpool ε hε
  · intro ε hε
    constructor
    · intro m
      exact one_le_mul_of_one_le_of_one_le
        (iterateStageQThrough_one C hC hpool (C.top + 1) ε m)
        ((iterateGlobalData C hC).Q_one (iterateTolerance C.top ε) m)
    · apply sublinear_log_mul_of_one_le
        (fun m => iterateStageQThrough C hC hpool (C.top + 1) ε m)
        (fun m => (iterateGlobalData C hC).Q (iterateTolerance C.top ε) m)
      · exact iterateStageQThrough_one C hC hpool (C.top + 1) ε
      · exact (iterateGlobalData C hC).Q_one (iterateTolerance C.top ε)
      · exact iterateStageQThrough_sublinear C hC hpool (C.top + 1) ε hε
      · exact (iterateGlobalData C hC).Q_sublinear (iterateTolerance C.top ε)
          (iterateTolerance_pos C.top hε)
  · have hg := lowerRate_tolerance_scale (outerN C) (iterateGlobalData C hC).V
      (gRate C.global) ((3 : ℚ) ^ C.top) (by positivity)
      (iterateGlobalData C hC).V_lowerRate
    have hs := iterateStageVThrough_lowerRate C hC hpool (C.top + 1)
    have hv := lowerRate_mul (outerN C)
      (fun ε m => (iterateGlobalData C hC).V (iterateTolerance C.top ε) m)
      (iterateStageVThrough C hC hpool (C.top + 1))
      (gRate C.global) (iterateStageRateThrough C (C.top + 1))
      (by simpa only [iterateTolerance] using hg) hs
    rw [iterateStageRateThrough_top] at hv
    simpa only [f, V, boundaryNumericalFamily, iterateFinalV,
      derivedRetainedRate_eq_iterateStageRate] using hv
  · exact boundaryNumericalFamily_matrix_lowerRates C hC Q V

end
end OmegaBound.ADVXXZGeneral
end

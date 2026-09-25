import OmegaBound.ADVXXZGeneralIterateStages
import OmegaBound.ADVXXZGeneralCExact42RegionalExact
import OmegaBound.ADVXXZGeneralCExact42PositiveRegional
import OmegaBound.ADVXXZGeneralCExact42Pooled
import OmegaBound.ADVXXZGeneralClosureConditional

/-!
# The unconditional recursion and the general certificate bound

The conditional recursion `iterate_stages_of_constituent` (`ADVXXZGeneralIterateStages`) takes
three constituent-stage propositions, proved in the `ADVXXZGeneralCExact42*` modules.
Discharging them gives the frozen `V17_N_Iterate.1`, and the conditionals of
`ADVXXZGeneralClosureConditional` then give `V17_N_Closure.1` and `V17_N_Closure.2`.
-/

namespace OmegaBound.ADVXXZGeneral

/-- Frozen `V17_N_Iterate.1`: the finite global/constituent recursion, unconditional. -/
theorem iterate_stages : S_V17_N_Iterate_1 :=
  iterate_stages_of_constituent.{0} constituent_positive_exact_regional33.{0}
    constituent_positive_positive_regional33.{0} constituent_pooled_positive33

/-- Frozen `V17_N_Closure.1`: the general certificate bound, for every field. -/
theorem certificate_bound : S_V17_N_Closure_1.{u} :=
  certificate_bound_of_iterate.{u} iterate_stages

/-- Frozen `V17_N_Closure.2`: closure under convergent certificate sequences, for every field. -/
theorem omegaRect_le_of_certificates_tendsto : S_V17_N_Closure_2.{u} :=
  omegaRect_le_of_certificates_tendsto_of_bound.{u} certificate_bound.{u}

example : S_V17_N_Iterate_1 := iterate_stages
example : S_V17_N_Closure_1.{u} := certificate_bound.{u}
example : S_V17_N_Closure_2.{u} := omegaRect_le_of_certificates_tendsto.{u}

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.iterate_stages
#print axioms OmegaBound.ADVXXZGeneral.certificate_bound
#print axioms OmegaBound.ADVXXZGeneral.omegaRect_le_of_certificates_tendsto

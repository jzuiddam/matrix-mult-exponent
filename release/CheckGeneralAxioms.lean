import OmegaBound.FinalBound

/-! The general theorems of the route (constituent and global stages, recursion, certificate
bound and closure) and the two kernel-only legs of the released instance:
each prints exactly the three kernel axioms `propext`, `Classical.choice`, `Quot.sound`. Run by
`release/reproduce.sh general`; expected output in `release/CheckGeneralAxioms.expected`. -/

#print axioms OmegaBound.ADVXXZGeneral.constituent_positive_exact_regional33
#print axioms OmegaBound.ADVXXZGeneral.constituent_positive_positive_regional33
#print axioms OmegaBound.ADVXXZGeneral.constituent_pooled_positive33
#print axioms OmegaBound.ADVXXZGeneral.global_exact_uniform
#print axioms OmegaBound.ADVXXZGeneral.global_nearby_uniform
#print axioms OmegaBound.ADVXXZGeneral.global_positive_integral_for_iterate
#print axioms OmegaBound.ADVXXZGeneral.iterate_stages
#print axioms OmegaBound.ADVXXZGeneral.certificate_bound
#print axioms OmegaBound.ADVXXZGeneral.omegaRect_le_of_certificates_tendsto
#print axioms OmegaBound.ADVXXZGeneral.released_level2_retained_leg
#print axioms OmegaBound.ADVXXZGeneral.released_global_retained_leg

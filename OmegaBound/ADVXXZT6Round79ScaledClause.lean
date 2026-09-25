import OmegaBound.ADVXXZT6Round78ReleasedComplement
import OmegaBound.ADVXXZT6Round19PaperContract

/-!
# C9 at the realizable scale

In the proposition `n_t` is the actual input count and the output multiplicities scale with it (`constituent.tex:9-11,113-121,140-146,488-495`).

This file therefore renders C9 on a positive denominator sublattice.  At base scale `scale`,
`d.outBase` is the natural output table for input counts `p.baseN t * scale`; multiplying both
input and output by `m` gives every later point of the same lattice.  For the released rational
simplexes, `certificateDen^2` clears `A * (alpha(u) + alpha(complement u))` symbolically.

The symmetric reading is the one computed by the released implementation: `TermInfo.m:213-218`
adds the same `term_frac * split_dist * region_prop` to both child pointers.  The evaluator keeps
these as `GVar` weights; `Workspace.m:130-142,179-206` and `GetFeasibility.m:7-26` impose no
scale-one integrality constraint.
-/

set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round79

open ADVXXZPaper
open ADVXXZCertificateConstituentData
open ADVXXZCertificateConstituentClosure
open ADVXXZT6Round19

/-- Correct C9: the displayed natural table is attached to actual input length
`p.baseN t * scale`, not to the normalized released weight at multiplier one.

SOURCE: `constituent.tex:9-11,119-121,140-146,488-495`.
-/
def OutputParameterClauseAtScale (p : ConstituentInput w s) (d : ConstituentData p)
    (scale : Nat) : Prop :=
  forall x, (d.outBase x : Real) = ((p.baseN x.1 * scale : Nat) : Real) *
    d.A x.1 x.2.1 * symWeight d x.1 x.2.1 x.2.2

/-- The paper's C1--C10 record with only C9 re-rendered at a declared positive realizable scale.
The other clauses are exactly the clause renderings of `ADVXXZT6Round19`.

SOURCE: `constituent.tex:113-136`.
-/
structure CorrectedConstituentConstraints (p : ConstituentInput w s)
    (d : ConstituentData p) (scale : Nat) : Prop where
  scale_pos : 0 < scale
  alpha_and_marginals : AlphaAndMarginalsClause p d
  region_weights : RegionWeightsClause d
  regional_mixture : RegionalMixtureClause p d
  child_complete_splits : ChildCompleteSplitClause p d
  parent_product : ParentProductClause p d
  output_parameters : OutputParameterClauseAtScale p d scale
  six_permutations : SixPermutationsClause d
  regional_exponents : RegionalExponentClause d

end OmegaBound.ADVXXZT6Round79

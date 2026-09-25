import OmegaBound.ADVXXZPaperTheorems
import OmegaBound.ADVXXZT6Selection
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The paper's constituent proposition

This module is a specification.  It constructs no large family.  It restates
`prop:constituent-stage-no-eps` clause by clause, with the six regional outputs kept as an
explicit heterogeneous tensor product.  The only replacement of the source notation is that
the two asymptotic losses are named functions with their stated dependencies.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Filter Finset Tensor3 Asymptotics
open scoped Topology

namespace OmegaBound
namespace ADVXXZT6Round19

open ADVXXZ (SplitDist iface)
open ADVXXZHoles (famDS)
open ADVXXZPaper

/-! ## The paper's two named losses -/

/-- The kernel-checkable rendering of the two losses in the exponent.

`littleO` is the paper's parameter-independent `o(n)`.  `littleOEpsilon ε` is the paper's
`o_ε(n)` and may depend on the fixed positive interface tolerance.  Both are sublinear in the
paper's tensor-power length `n`; no endpoint or logarithm-base convention is built into them.

SOURCE: `constituent.tex:113-118`.
-/
structure PaperLossFunctions where
  /-- The named replacement for `o(n)`; SOURCE: `constituent.tex:118`. -/
  littleO : Nat -> Real
  /-- The named replacement for `o_ε(n)` with its ε-dependence explicit;
  SOURCE: `constituent.tex:118`. -/
  littleOEpsilon : Rat -> Nat -> Real
  /-- Losses are charges, hence nonnegative; SOURCE: `constituent.tex:118`. -/
  littleO_nonneg : forall n, 0 <= littleO n
  /-- The ε-dependent loss is also a nonnegative charge;
  SOURCE: `constituent.tex:118`. -/
  littleOEpsilon_nonneg : forall ε n, 0 <= littleOEpsilon ε n
  /-- The named `o(n)` has its literal asymptotic meaning;
  SOURCE: `constituent.tex:118`. -/
  littleO_sublinear : littleO =o[atTop] (fun n : Nat => (n : Real))
  /-- For each fixed positive ε, the named `o_ε(n)` is sublinear in `n`;
  SOURCE: `constituent.tex:115,118`. -/
  littleOEpsilon_sublinear : forall ε : Rat, 0 < ε ->
    littleOEpsilon ε =o[atTop] (fun n : Nat => (n : Real))

/-! ## Every hypothesis and itemized clause -/

/-- The hypotheses on the input interface tensor: positive tolerance and positive parent
coordinates for every term.  The parameter record also carries the term multiplicities, complete
split distributions, exact support, and `i_t+j_t+k_t` level equation.

SOURCE: `constituent.tex:9-11,113-117`.
-/
def InputHypotheses (ε : Rat) (p : ConstituentInput w s) : Prop :=
  0 < ε /\ (forall t, 0 < p.i t /\ 0 < p.j t /\ 0 < p.k t)

/-- `α_t^(r)` is a distribution whose marginals are the one-level splits of the regional
complete split distributions.

SOURCE: `constituent.tex:41-47,111-112`.
-/
def AlphaAndMarginalsClause (p : ConstituentInput w s) (d : ConstituentData p) : Prop :=
  (forall t r, IsProbability (d.alpha t r)) /\
    forall W t r a,
      constituentMarginal d t r W a = halfMarginal (d.betaRegion W t r) a

/-- Every region weight lies in `[0,1]`, and the six weights for each term sum to one.

SOURCE: `constituent.tex:122-123`.
-/
def RegionWeightsClause (d : ConstituentData p) : Prop :=
  (forall t r, 0 <= d.A t r /\ d.A t r <= 1) /\
    forall t, (∑ r, d.A t r) = 1

/-- The weighted mixture of the six regional complete split distributions is the input complete
split distribution, for every term and every tensor side.

SOURCE: `constituent.tex:124`.
-/
def RegionalMixtureClause (p : ConstituentInput w s) (d : ConstituentData p) : Prop :=
  forall W t σ, (p.beta W t).probR σ =
    ∑ r, d.A t r * (d.betaRegion W t r).probR σ

/-- Each child object is a level-`(ℓ-1)` complete split distribution.  The Lean type
`SplitDist w` carries normalization; this predicate records its exact child-level support.

SOURCE: `constituent.tex:125`.
-/
def ChildCompleteSplitClause (p : ConstituentInput w s) (d : ConstituentData p) : Prop :=
  forall W t r u σ, (d.betaChild W t r u).probR σ ≠ 0 ->
    ADVXXZ.chunkLvl σ = coord W u.1

/-- The regional parent complete split distribution is the α-weighted concatenation product of
the two complementary child complete split distributions.

SOURCE: `constituent.tex:126-127`.
-/
def ParentProductClause (p : ConstituentInput w s) (d : ConstituentData p) : Prop :=
  forall W t r σ, (d.betaRegion W t r).probR σ =
    ∑ u, d.alpha t r u * pairProb (d.betaChild W t r u)
      (d.betaChild W t r (complement p t u)) σ

/-- The output parameter list is indexed by `(t,r,i',j',k')`.  `ChildShape p t` enforces
`i'+j'+k'=2^(ℓ-1)` and the three parent-coordinate bounds; `outBase` is exactly
`n_t A_(t,r) (α(u)+α(parent-u))`.

SOURCE: `constituent.tex:119-121`.
-/
def OutputParameterClause (p : ConstituentInput w s) (d : ConstituentData p) : Prop :=
  forall x, (d.outBase x : Real) = (p.baseN x.1 : Real) * d.A x.1 x.2.1 *
    symWeight d x.1 x.2.1 x.2.2

/-- The six maps are precisely the six permutations of `X,Y,Z`.

SOURCE: `constituent.tex:128`.
-/
def SixPermutationsClause (d : ConstituentData p) : Prop :=
  EnumeratesPermutations d.perm

/-- For every region, all term contributions are summed in each direction before the one
three-way minimum defining `E_r`.  The definitions `constituentRowX/Y/Z` contain the sums over
all `t`; `constituentRegionRate` takes the minimum only after those sums.

SOURCE: `constituent.tex:128-134`.
-/
def RegionalExponentClause (d : ConstituentData p) : Prop :=
  forall r, d.E r = constituentRegionRate d r

/-- The complete collection of hypotheses and five itemized constraints of the proposition.
No producer conclusion is hidden in this record.

SOURCE: `constituent.tex:113-135`.
-/
structure PaperConstituentClauses (p : ConstituentInput w s) (d : ConstituentData p) : Prop where
  /-- α distributions and their required marginals; SOURCE: `constituent.tex:41-47`. -/
  alpha_and_marginals : AlphaAndMarginalsClause p d
  /-- Six weights in `[0,1]` summing to one; SOURCE: `constituent.tex:123`. -/
  region_weights : RegionWeightsClause d
  /-- Input split distributions are the weighted regional mixture;
  SOURCE: `constituent.tex:124`. -/
  regional_mixture : RegionalMixtureClause p d
  /-- Every output split distribution is complete at the child level;
  SOURCE: `constituent.tex:125`. -/
  child_complete_splits : ChildCompleteSplitClause p d
  /-- Regional parent distributions are α-weighted complementary products;
  SOURCE: `constituent.tex:126-127`. -/
  parent_product : ParentProductClause p d
  /-- The output parameter-list multiplicity formula and its restricted index;
  SOURCE: `constituent.tex:119-121`. -/
  output_parameters : OutputParameterClause p d
  /-- The regional role maps enumerate all permutations; SOURCE: `constituent.tex:128`. -/
  six_permutations : SixPermutationsClause d
  /-- Each `E_r` is the minimum after all regional term sums;
  SOURCE: `constituent.tex:128-134`. -/
  regional_exponents : RegionalExponentClause d


/-! ## The six regional output tensors -/

/-- One region's output parameter index `(t,i',j',k')`, with the shape equation and bounds
carried by `ChildShape`.

SOURCE: `constituent.tex:119-121,488-495`.
-/
abbrev RegionOutputTerm (p : ConstituentInput w s) :=
  (t : Fin s) × ChildShape p t

/-- A finite enumeration of the paper's restricted `(t,i',j',k')` output indices.

SOURCE: `constituent.tex:119-121`.
-/
noncomputable def regionOutputIndex (p : ConstituentInput w s)
    (x : Fin (Fintype.card (RegionOutputTerm p))) : RegionOutputTerm p :=
  (Fintype.equivFin (RegionOutputTerm p)).symm x

/-- The exact output multiplicity in one region at scale multiplier `m`.

SOURCE: `constituent.tex:119-121,491-493`.
-/
noncomputable def regionOutN (p : ConstituentInput w s) (d : ConstituentData p)
    (m : Nat) (r : Fin 6) (x : Fin (Fintype.card (RegionOutputTerm p))) : Nat :=
  d.outBase ⟨(regionOutputIndex p x).1, r, (regionOutputIndex p x).2⟩ * m

/-- The output's child `i'` coordinate.  Membership in `ChildShape` carries its paper bounds and
the child-level shape equation.

SOURCE: `constituent.tex:119-121`.
-/
noncomputable def regionOutI (p : ConstituentInput w s)
    (x : Fin (Fintype.card (RegionOutputTerm p))) : Nat :=
  coord .X (regionOutputIndex p x).2.1

/-- The output's child `j'` coordinate.

SOURCE: `constituent.tex:119-121`.
-/
noncomputable def regionOutJ (p : ConstituentInput w s)
    (x : Fin (Fintype.card (RegionOutputTerm p))) : Nat :=
  coord .Y (regionOutputIndex p x).2.1

/-- The output's child `k'` coordinate.

SOURCE: `constituent.tex:119-121`.
-/
noncomputable def regionOutK (p : ConstituentInput w s)
    (x : Fin (Fintype.card (RegionOutputTerm p))) : Nat :=
  coord .Z (regionOutputIndex p x).2.1

/-- The three complete split distributions attached to one regional output term.

SOURCE: `constituent.tex:119-121,125`.
-/
noncomputable def regionOutBeta (p : ConstituentInput w s) (d : ConstituentData p)
    (W : Side) (r : Fin 6) (x : Fin (Fintype.card (RegionOutputTerm p))) : SplitDist w :=
  d.betaChild W (regionOutputIndex p x).1 r (regionOutputIndex p x).2

/-- The level-`(ℓ-1)` interface tensor returned by one region.

SOURCE: `constituent.tex:119-121,483-495`.
-/
noncomputable def regionOutput (q : Nat) (p : ConstituentInput w s)
    (d : ConstituentData p) (m : Nat) (r : Fin 6) :=
  iface q w (regionOutN p d m r) (regionOutI p) (regionOutJ p) (regionOutK p)
    (regionOutBeta p d .X r) (regionOutBeta p d .Y r) (regionOutBeta p d .Z r) 0

/-- The proposition's final output is the tensor product of all six regional outputs, not region
zero and not six unrelated uses of the whole source.

SOURCE: `constituent.tex:497`.
-/
noncomputable def sixRegionOutput (q : Nat) (p : ConstituentInput w s)
    (d : ConstituentData p) (m : Nat) :=
  CW90Eight.piT (fun r : Fin 6 => regionOutput q p d m r)

/-- The paper's `n := sum_t n_t`, after the common integral multiplier `m`.

SOURCE: `constituent.tex:9-11`.
-/
def paperN (p : ConstituentInput w s) (m : Nat) : Nat :=
  (∑ t, p.baseN t) * m

/-- `E_r` after scaling every `n_t` by `m`; each unscaled `E_r` already sums all terms in its
region before taking the minimum.

SOURCE: `constituent.tex:128-134`.
-/
noncomputable def scaledEr (d : ConstituentData p) (m : Nat) (r : Fin 6) : Real :=
  (m : Real) * d.E r

/-- The exact `sum_r E_r` appearing in the proposition's copy exponent.

SOURCE: `constituent.tex:118,128-134`.
-/
noncomputable def summedRegionalExponent (d : ConstituentData p) (m : Nat) : Real :=
  ∑ r : Fin 6, scaledEr d m r

/-- One eventual finite producer family witnessing the paper's conclusion.  The threshold may
depend on the fixed positive ε, exactly where the proof invokes “sufficiently large `n`”.

SOURCE: `constituent.tex:113-121,479-497`; sufficiently-large quantifier made explicit in
VXXZ24 `analysis_constituent.tex:324-325`.
-/
structure PaperConstituentProducerWitness (q : Nat) (p : ConstituentInput w s)
    (d : ConstituentData p) (loss : PaperLossFunctions) where
  /-- Actual natural copy counts; SOURCE: `constituent.tex:118-120`. -/
  copies : Rat -> Nat -> Nat
  /-- For every ε > 0 and every sufficiently large scale, the input degenerates into at least
  `2^(sum_r E_r-o(n)-o_ε(n))` copies of the tensor product of the six regional outputs.

  SOURCE: `constituent.tex:113-121,497`.
  -/
  eventual_producer : forall ε : Rat, InputHypotheses ε p -> exists threshold : Nat,
    forall m : Nat, threshold <= m ->
      0 < copies ε m /\
      (2 : Real) ^ (summedRegionalExponent d m - loss.littleO (paperN p m) -
        loss.littleOEpsilon ε (paperN p m)) <= (copies ε m : Real) /\
      Degenerates Rat
        (iface q (w + w) (fun t => p.baseN t * m) p.i p.j p.k
          (p.beta .X) (p.beta .Y) (p.beta .Z) ε)
        (famDS (Finset.univ : Finset (Fin (copies ε m)))
          (fun _ => sixRegionOutput q p d m))

/-- **THE PAPER-SHAPED CONSTITUENT PRODUCER CONTRACT.**  It retains every hypothesis and every
itemized clause of `prop:constituent-stage-no-eps`, quantifies over every positive ε, uses actual
natural copy counts at sufficiently large `n`, and tensors the six regional outputs.  The only
formalization change is the replacement of `o(n)` and `o_ε(n)` by `PaperLossFunctions`.

SOURCE: `constituent.tex:113-136,497`.
-/
structure PaperConstituentProducerContract (q : Nat) (p : ConstituentInput w s)
    (d : ConstituentData p) where
  /-- All hypotheses and itemized constraints; SOURCE: `constituent.tex:113-135`. -/
  clauses : PaperConstituentClauses p d
  /-- The two explicitly named losses; SOURCE: `constituent.tex:118`. -/
  losses : PaperLossFunctions
  /-- The eventual degeneration and copy count; SOURCE: `constituent.tex:113-121,497`. -/
  producer : PaperConstituentProducerWitness q p d losses

end ADVXXZT6Round19
end OmegaBound

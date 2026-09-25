import OmegaBound.ADVXXZT2Inv

/-!
# The logical/physical transport, and the universal parent-mixture identities

This module proves the parent-mixture identities at **all `126` general parents, all three legs
and all five half levels** — and, on the way, repairs an indexing transport that a check at the
gate parent (`Level3TermId 10`) could not have exposed.

## The transport the base case could not see

The gate parent is `Level3TermId 10`, i.e. **global region `0`**, where the role permutation
`ADVXXZCertRegionalSemantic.physicalSide 0` is the identity.  Off region `0` the released data is
mixed:

* the constituent DAG — `globalShapeTable`, `level3Specs`, `level2ShapeTable` and the incidence
  list — is indexed in **physical MATLAB dimension order** (`Dims.m`);
* the residual complete-split tables `ADVXXZRA.regionalSplit` / `ADVXXZG1.betaIdx` are indexed in
  **logical paper-role order** (`ADVXXZCertRegionalSemantic`: "already transported from physical
  MATLAB dimensions to paper roles").

So the parent law of the level-3 node at physical row `n` of global region `r` is **not**
`betaIdx r S n`: it is `betaIdx r (roleAt r l) (logRow r n)`, where `logRow r` is the inverse of
`ADVXXZG1.physRow r` and `l` is the physical leg.  `logRow_physRow` and `physRow_logRow` prove the
two are inverse, `logRow_zero` proves the transport is invisible at region `0`, and
`mixture_needs_transport` proves that dropping it makes the parent-mixture identity **false**.

## Why the marginals are indexed, not zipped

Every constituent-side quantity below is a sum over `List.range (parKids p).length`, so the
left-half term at index `d` and the right-half term at the complementary index
`length - 1 - d` sit in the *same* summand.  `par_pair_idx` then makes the two half levels of one
summand add to the parent's own leg.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT2

open ADVXXZ (Chunk chunkLvl SplitDist)
open ADVXXZPaper (Side)
open ADVXXZG2 (leftHalfLvl rightHalfLvl)
open ADVXXZCertRegionalSemantic (physicalSide shapeOffset)

/-! ## §1  The logical/physical row transport -/

/-- Coordinate `d` of a shape triple, by physical dimension. -/
def coordIdx (t : Sh) (d : Fin 3) : ℕ := ![t.1, t.2.1, t.2.2] d

theorem coordIdx_eq (t : Sh) (d : Fin 3) : coordIdx t d = (legs t).getD d.val 0 := by
  fin_cases d <;> rfl

/-- **THE LOGICAL ROW OF A PHYSICAL ROW.**  Region `r` stores the node whose *physical* shape is
`rowShape n` at the *logical* row whose shape reads the physical coordinates through
`physicalSide r`. -/
def logRow (r : Fin 6) (n : Fin 45) : Fin 45 :=
  Fin.ofNat 45 (shapeOffset (coordIdx (ADVXXZG1.rowShape n) (physicalSide r .X))
    + coordIdx (ADVXXZG1.rowShape n) (physicalSide r .Y))

/-- **`logRow` INVERTS `ADVXXZG1.physRow`.** -/
theorem logRow_physRow : ∀ (r : Fin 6) (n : Fin 45), logRow r (ADVXXZG1.physRow r n) = n := by
  decide +kernel

/-- **AND IS INVERTED BY IT.** -/
theorem physRow_logRow : ∀ (r : Fin 6) (n : Fin 45), ADVXXZG1.physRow r (logRow r n) = n := by
  decide +kernel

/-- At global region `0` the transport is the identity — which is why the G2 base case, sited at
`Level3TermId 10 < 45`, could not expose it. -/
theorem logRow_zero : ∀ n : Fin 45, logRow 0 n = n := by decide +kernel

theorem logRow_bijective (r : Fin 6) : Function.Bijective (logRow r) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ADVXXZG1.physRow r, fun n => physRow_logRow r n, fun n => logRow_physRow r n⟩

/-- The released row index carries the released shape. -/
theorem rowShape_eq : ∀ n : Fin 45,
    ADVXXZG1.rowShape n = ADVXXZReleasedTree.globalShapeTable.getD n.val (0, 0, 0) := by
  decide +kernel

/-- **THE TRANSPORTED TABLE LIVES AT THE PHYSICAL LEG'S OWN LEVEL.** -/
theorem rowLvl_logRow : ∀ (r : Fin 6) (n : Fin 45) (l : Fin 3),
    ADVXXZG1.rowLvl (ADVXXZG1.roleAt r l) (logRow r n) = (legs (ADVXXZG1.rowShape n)).getD l.val 0 := by
  decide +kernel

/-! ## §2  The parent's own complete-split law -/

/-- The global region of the `p`-th general parent. -/
def parRegion (p : ℕ) : Fin 6 := Fin.ofNat 6 (genId p / 45)

/-- Its physical row. -/
def parRow (p : ℕ) : Fin 45 := Fin.ofNat 45 (genId p)

/-- The logical paper role that carries the parent's physical leg `l`. -/
def parSide (p : ℕ) (l : ℕ) : Side := ADVXXZG1.roleAt (parRegion p) (Fin.ofNat 3 l)

/-- **THE PARENT'S OWN RELEASED COMPLETE-SPLIT LAW** on physical leg `l`: one of the six regional
authorities G1 certified, read at the transported row and the transported side. -/
def parBeta (p : ℕ) (l : ℕ) : SplitDist 4 :=
  ADVXXZG1.betaIdx (parRegion p) (parSide p l) (logRow (parRegion p) (parRow p))

/-- The naive, untransported reading: the same region, the *physical* row, the *physical* side.
Kept only so that `mixture_needs_transport` can refute it. -/
def naiveBeta (p : ℕ) (l : ℕ) : SplitDist 4 :=
  ADVXXZG1.betaIdx (parRegion p) (ADVXXZG1.roleAt 0 (Fin.ofNat 3 l)) (parRow p)

theorem parRow_shape (p : ℕ) : ADVXXZG1.rowShape (parRow p) = parShapeOf p := by
  rw [rowShape_eq]
  rfl

/-! ## §3  The half-level marginals and the half-level joint -/

/-- The parent law's left-half level marginal. -/
def margL (B : SplitDist 4) (a : ℕ) : ℕ := ∑ c : Chunk 4, if leftHalfLvl c = a then B.num c else 0

/-- Its right-half level marginal. -/
def margR (B : SplitDist 4) (b : ℕ) : ℕ := ∑ c : Chunk 4, if rightHalfLvl c = b then B.num c else 0

/-- **THE PARENT LAW'S PAIRED HALF-LEVEL JOINT** — an object the half-level marginals do *not*
identify. -/
def jointB (B : SplitDist 4) (a b : ℕ) : ℕ :=
  ∑ c : Chunk 4, if leftHalfLvl c = a ∧ rightHalfLvl c = b then B.num c else 0

/-- The `d`-th released child shape of the `p`-th parent. -/
def kid (p d : ℕ) : Sh := (parKids p).getD d (0, 0, 0)

/-- Its complement, at the reflected index. -/
def kidC (p d : ℕ) : Sh := (parKids p).getD ((parKids p).length - 1 - d) (0, 0, 0)

/-- The constituent stage's left-half level marginal: the `A`-weighted mixture over the six
constituent regions of the child leg marginals. -/
def consMarg (p l a : ℕ) : ℕ :=
  ((List.range 6).map (fun r => (regNums p).getD r 0 *
     ((List.range (parKids p).length).map (fun d =>
        if (legs (kid p d)).getD l 0 = a then (chNums p r).getD d 0 else 0)).sum)).sum

/-- Its right-half counterpart, against the complementary child. -/
def consMargR (p l b : ℕ) : ℕ :=
  ((List.range 6).map (fun r => (regNums p).getD r 0 *
     ((List.range (parKids p).length).map (fun d =>
        if (legs (kidC p d)).getD l 0 = b then (chNums p r).getD d 0 else 0)).sum)).sum

/-- **THE CONSTITUENT STAGE'S PAIRED HALF-LEVEL JOINT.**  The two halves of one split occupy the
*same* summand, so this is a genuine joint and not a product of marginals. -/
def consJoint (p l a b : ℕ) : ℕ :=
  ((List.range 6).map (fun r => (regNums p).getD r 0 *
     ((List.range (parKids p).length).map (fun d =>
        if (legs (kid p d)).getD l 0 = a ∧ (legs (kidC p d)).getD l 0 = b
        then (chNums p r).getD d 0 else 0)).sum)).sum

/-! ## §4  The two universal laws -/

/-- **THE COMPLEMENT PAIRING, IN INDEX FORM.**  At every parent, every physical leg and every
released split index, the two halves' levels add to the parent's own leg. -/
theorem par_pair_idx : ∀ p ∈ List.range 126, ∀ l ∈ List.range 3,
    ∀ d ∈ List.range (parKids p).length,
      (legs (kid p d)).getD l 0 + (legs (kidC p d)).getD l 0
        = (legs (parShapeOf p)).getD l 0 := by
  decide +kernel

/-- **THE UNIVERSAL PARENT-MIXTURE IDENTITIES**, at every one of the
`126` general parents, both halves, all three physical legs, all five half levels —
cross-multiplied over `ℕ`, no rational formed. -/
def MargOK : Prop :=
  ∀ p ∈ List.range 126, ∀ l ∈ List.range 3, ∀ a ∈ List.range 5,
    margL (parBeta p l) a * (certDen * certDen) = consMarg p l a * (parBeta p l).den
    ∧ margR (parBeta p l) a * (certDen * certDen) = consMargR p l a * (parBeta p l).den

instance : Decidable MargOK := by unfold MargOK; infer_instance

/-- **THE PARENT CONTRACT HOLDS AT EVERY GENERAL PARENT.** -/
theorem marg_ok : MargOK := by native_decide

/-! ## §5  The transport is load-bearing -/

/-- The untransported reading, for refutation only. -/
def NaiveMargOK : Prop :=
  ∀ p ∈ List.range 126, ∀ l ∈ List.range 3, ∀ a ∈ List.range 5,
    margL (naiveBeta p l) a * (certDen * certDen) = consMarg p l a * (naiveBeta p l).den

instance : Decidable NaiveMargOK := by unfold NaiveMargOK; infer_instance

/-- **WITHOUT THE TRANSPORT THE PARENT CONTRACT IS FALSE.**  So `logRow`/`roleAt` is not a
cosmetic reindexing: it is what makes the constituent stage's parent law the released one. -/
theorem mixture_needs_transport : ¬ NaiveMargOK := by native_decide

/-- **AND THE GATE PARENT COULD NOT HAVE FOUND IT.**  Restricted to global region `0` — where the
gate parent lives — the untransported reading is *true*: the defect is invisible to any
region-zero fixture. -/
theorem naive_true_on_region_zero :
    ∀ p ∈ List.range 21, ∀ l ∈ List.range 3, ∀ a ∈ List.range 5,
      margL (naiveBeta p l) a * (certDen * certDen) = consMarg p l a * (naiveBeta p l).den := by
  native_decide

/-- The first `21` general parents are exactly the general nodes of global region `0`. -/
theorem region_zero_block : ∀ p ∈ List.range 126, (genId p < 45 ↔ p < 21) := by
  decide +kernel

end ADVXXZT2
end OmegaBound

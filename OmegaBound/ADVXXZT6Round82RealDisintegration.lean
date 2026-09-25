import OmegaBound.ADVXXZT6Round82ChildKernelChecked
import OmegaBound.ADVXXZT6Round79ScaledClause
import OmegaBound.ADVXXZT6WordLaw

/-!
# The real released disintegration

This module mirrors the released implementation in `TermInfo.m:248-263`:

* lines 248-257: for each child shape, concatenate its actual left complete-split distribution
  with the actual complete-split distribution of the complementary child, and mix those products
  with the released child simplex;
* lines 258-263: mix the six resulting regional laws with the released region simplex.

All sides here are physical sides.  The region permutation belongs to the later evaluator and is
not applied while constructing `complete_split{t}`.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

open Finset

namespace OmegaBound.ADVXXZT6Round82

open ADVXXZ (Chunk SplitDist RatDist)
open ADVXXZPaper
open ADVXXZCertificateConstituentData
open ADVXXZCertificateConstituentClosure
open ADVXXZT6Round78 (childTriple releasedChildIndexBounds)
open ADVXXZT9R16PositiveParents (releasedPositiveInput)
open ADVXXZT6SplitTargetData

private theorem sum_getD (l : List Nat) :
    (∑ d : Fin l.length, l.getD d.1 0) = l.sum := by
  calc
    (∑ d : Fin l.length, l.getD d.1 0) =
        ∑ d : Fin l.length, l[d.1] := by
          exact Finset.sum_congr rfl
            (fun d _ => List.getD_eq_getElem (l := l) (d := 0) d.isLt)
    _ = (List.ofFn (fun d : Fin l.length => l[d.1])).sum := by simp
    _ = l.sum := congrArg List.sum (List.ofFn_getElem l)

/-- Executable released six-region simplex. -/
def releasedRegionDist (t : Fin 126) : RatDist (Fin 6) where
  num r := (ADVXXZT2.regNums t.1).getD r.1 0
  den := ADVXXZT2.certDen
  den_pos := by decide +kernel
  sum_num := by
    have h := (ADVXXZT2.mult_ok t.1 (List.mem_range.mpr t.isLt)).2.1
    have hlen := (ADVXXZT2.mult_ok t.1 (List.mem_range.mpr t.isLt)).1
    let e : Fin 6 ≃ Fin (ADVXXZT2.regNums t.1).length := finCongr hlen.symm
    change (∑ r : Fin 6, (ADVXXZT2.regNums t.1).getD r.1 0) = ADVXXZT2.certDen
    rw [show (∑ r : Fin 6, (ADVXXZT2.regNums t.1).getD r.1 0) =
        ∑ d : Fin (ADVXXZT2.regNums t.1).length,
          (ADVXXZT2.regNums t.1).getD d.1 0 by
      exact Equiv.sum_comp e (fun d => (ADVXXZT2.regNums t.1).getD d.1 0)]
    rw [sum_getD, h]

/-- Executable released child simplex in its committed row order. -/
def releasedChildRowDist (t : Fin 126) (r : Fin 6) :
    RatDist (Fin (ADVXXZT2.parKids t.1).length) where
  num d := (ADVXXZT2.chNums t.1 r.1).getD d.1 0
  den := ADVXXZT2.certDen
  den_pos := by decide +kernel
  sum_num := by
    have hm := ADVXXZT2.mult_ok t.1 (List.mem_range.mpr t.isLt)
    have hlen := (hm.2.2.1 r.1 (List.mem_range.mpr r.isLt)).1
    have hsum := (hm.2.2.1 r.1 (List.mem_range.mpr r.isLt)).2.1
    change (∑ d : Fin (ADVXXZT2.parKids t.1).length,
      (ADVXXZT2.chNums t.1 r.1).getD d.1 0) = ADVXXZT2.certDen
    rw [show (∑ d : Fin (ADVXXZT2.parKids t.1).length,
        (ADVXXZT2.chNums t.1 r.1).getD d.1 0) =
      ∑ d : Fin (ADVXXZT2.chNums t.1 r.1).length,
        (ADVXXZT2.chNums t.1 r.1).getD d.1 0 by
          simpa using (Equiv.sum_comp (finCongr hlen)
            (fun d => (ADVXXZT2.chNums t.1 r.1).getD d.1 0)).symm]
    rw [sum_getD, hsum]

/-- The released row coordinate really recovers the paper child shape. -/
theorem kidPat_childIndex (t : Fin 126) (u : ChildShape releasedPositiveInput t) :
    ADVXXZT6Selection.kidPat t (ADVXXZT6Round78.childIndex t u) = u.1 := by
  have hget := @List.findIdx_getElem _
    (fun v => v == childTriple t u) (ADVXXZT2.parKids t.1)
    (releasedChildIndexBounds t u)
  have htriple :
      (ADVXXZT2.parKids t.1)[ADVXXZT6Round78.childIndexNat t u]'
          (releasedChildIndexBounds t u) =
        childTriple t u := by
    simpa [ADVXXZT6Round78.childIndexNat] using hget
  have hkid :
      ADVXXZT2.kid t.1 (ADVXXZT6Round78.childIndex t u).1 = childTriple t u := by
    rw [ADVXXZT2.kid, List.getD_eq_getElem (l := ADVXXZT2.parKids t.1)
      (d := (0, 0, 0)) (ADVXXZT6Round78.childIndex t u).isLt]
    exact htriple
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    simpa [ADVXXZT6Selection.kidPat, childTriple, coord] using congrArg Prod.fst hkid
  · apply Prod.ext
    · apply Fin.ext
      simpa [ADVXXZT6Selection.kidPat, childTriple, coord] using
        congrArg (fun q => q.2.1) hkid
    · apply Fin.ext
      simpa [ADVXXZT6Selection.kidPat, childTriple, coord] using
        congrArg (fun q => q.2.2) hkid

/-- The actual released complete-split distribution at one committed child-row coordinate. -/
def certificateBetaChildAt (W : Side) (t : Fin 126) (r : Fin 6)
    (d : Fin (ADVXXZT2.parKids t.1).length) : SplitDist 2 :=
  (releasedChildRawAt W t r d).toDist (released_child_law_facts t W r d).1

@[simp] theorem certificateBetaChildAt_den (W : Side) (t : Fin 126) (r : Fin 6)
    (d : Fin (ADVXXZT2.parKids t.1).length) :
    (certificateBetaChildAt W t r d).den = ADVXXZT2.certDen := by
  rfl

/-- The same released law, indexed by the paper child subtype. -/
noncomputable def certificateBetaChild (W : Side) (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedPositiveInput t) : SplitDist 2 :=
  certificateBetaChildAt W t r (ADVXXZT6Round78.childIndex t u)


/-- `TermInfo.m:253-256`: actual concatenation at row `d`; reversal is the right child. -/
def certificateChildProductAt (W : Side) (t : Fin 126) (r : Fin 6)
    (d : Fin (ADVXXZT2.parKids t.1).length) : SplitDist (2 + 2) :=
  (certificateBetaChildAt W t r d).concat
    (certificateBetaChildAt W t r (Fin.rev d))

@[simp] theorem certificateChildProduct_den (W : Side) (t : Fin 126) (r : Fin 6)
    (d : Fin (ADVXXZT2.parKids t.1).length) :
    (certificateChildProductAt W t r d).den = ADVXXZT2.certDen * ADVXXZT2.certDen := by
  simp [certificateChildProductAt]

/-- `TermInfo.m:248-257`: one regional complete-split law, mixed over child shapes. -/
def certificateBetaRegion (W : Side) (t : Fin 126) (r : Fin 6) :
    SplitDist (2 + 2) :=
  RatDist.mix
    (releasedChildRowDist t r)
    (certificateChildProductAt W t r)
    (ADVXXZT2.certDen * ADVXXZT2.certDen)
    (certificateChildProduct_den W t r)

@[simp] theorem certificateBetaRegion_den (W : Side) (t : Fin 126) (r : Fin 6) :
    (certificateBetaRegion W t r).den =
      ADVXXZT2.certDen * (ADVXXZT2.certDen * ADVXXZT2.certDen) := by
  rfl

/-- `TermInfo.m:258-263`: concatenate within each region, then mix the six regions. -/
def certificateParentDist (W : Side) (t : Fin 126) : SplitDist (2 + 2) :=
  RatDist.mix
    (releasedRegionDist t)
    (certificateBetaRegion W t)
    (ADVXXZT2.certDen * (ADVXXZT2.certDen * ADVXXZT2.certDen))
    (certificateBetaRegion_den W t)

private noncomputable def constituentCore
    (outBase : ConstituentTerm releasedPositiveInput -> Nat) :
    ConstituentData releasedPositiveInput :=
  { A := fun t => (releasedRegionDist t).probR
    betaRegion := certificateBetaRegion
    alpha := fun t r u => (releasedChildRowDist t r).probR
      (ADVXXZT6Round78.childIndex t u)
    betaChild := certificateBetaChild
    E := 0
    perm := ADVXXZCertificateGlobalData.certificatePerm
    outBase := outBase }

/-- The exact natural C9 table at input scale `D^2`, written against the same released rows
used by the corrected constructor. -/
noncomputable def correctedOutBase (x : ConstituentTerm releasedPositiveInput) : Nat :=
  releasedPositiveInput.baseN x.1 * (releasedRegionDist x.1).num x.2.1 *
    ((releasedChildRowDist x.1 x.2.1).num (ADVXXZT6Round78.childIndex x.1 x.2.2) +
      (releasedChildRowDist x.1 x.2.1).num
        (ADVXXZT6Round78.childIndex x.1 (complement releasedPositiveInput x.1 x.2.2)))

/-- Corrected released data: actual child CSDs, actual regional products, and the scaled
natural output table of C9 at scale `D^2`. -/
noncomputable def releasedCorrectedData : ConstituentData releasedPositiveInput :=
  { A := fun t => (releasedRegionDist t).probR
    betaRegion := certificateBetaRegion
    alpha := fun t r u => (releasedChildRowDist t r).probR
      (ADVXXZT6Round78.childIndex t u)
    betaChild := certificateBetaChild
    E := fun r => constituentRegionRate
      (constituentCore correctedOutBase) r
    perm := ADVXXZCertificateGlobalData.certificatePerm
    outBase := correctedOutBase }

/-- Probability of a rational mixture, in the exact form used by C5 and C7. -/
theorem mix_probR {k i : Type*} [Fintype k] [Fintype i] [DecidableEq i]
    (A : RatDist k) (P : k -> RatDist i) (d : Nat) (hd : forall r, (P r).den = d)
    (x : i) :
    (RatDist.mix A P d hd).probR x = ∑ r, A.probR r * (P r).probR x := by
  classical
  simp only [RatDist.probR, RatDist.mix_num, RatDist.mix_den, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hd r]
  field_simp [A.den_ne_zero, (P r).den_ne_zero]

/-- Concatenation has exactly the paper's product probability. -/
theorem concat_probR (L R : SplitDist 2) (sigma : Chunk (2 + 2)) :
    (L.concat R).probR sigma = L.probR (leftHalf sigma) * R.probR (rightHalf sigma) := by
  change (L.concat R).probR sigma =
    L.probR (ADVXXZ.legFst sigma) * R.probR (ADVXXZ.legSnd sigma)
  simp only [RatDist.probR, SplitDist.concat_num, SplitDist.concat_den]
  push_cast
  ring

/-- C7 follows definitionally from the released child-product mixture. -/
theorem certificatePairedDisintegration (W : Side) (t : Fin 126) (r : Fin 6)
    (sigma : Chunk (2 + 2)) :
    (certificateBetaRegion W t r).probR sigma =
      ∑ u,
        (releasedChildRowDist t r).probR (ADVXXZT6Round78.childIndex t u) *
          pairProb (certificateBetaChild W t r u)
            (certificateBetaChild W t r (complement releasedPositiveInput t u)) sigma := by
  rw [certificateBetaRegion, mix_probR]
  rw [show (∑ d, (releasedChildRowDist t r).probR d *
      (certificateChildProductAt W t r d).probR sigma) =
      ∑ u, (releasedChildRowDist t r).probR (ADVXXZT6Round78.childIndex t u) *
        (certificateChildProductAt W t r (ADVXXZT6Round78.childIndex t u)).probR sigma by
    exact (Equiv.sum_comp (ADVXXZT6Round78.childRowEquiv t)
      (fun d => (releasedChildRowDist t r).probR d *
        (certificateChildProductAt W t r d).probR sigma)).symm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [certificateChildProductAt, concat_probR]
  simp only [pairProb, certificateBetaChild]
  rw [ADVXXZT6Round78.releasedComplementLayout t u]

/-- The constructed parent law is exactly the outer six-region mixture in C5. -/
theorem certificateParentDist_probR (W : Side) (t : Fin 126) (sigma : Chunk (2 + 2)) :
    (certificateParentDist W t).probR sigma =
      ∑ r, releasedCorrectedData.A t r *
        (releasedCorrectedData.betaRegion W t r).probR sigma := by
  rw [certificateParentDist, mix_probR]
  rfl

/-- C8 for the actual released child law. -/
theorem certificateBetaChild_supported (W : Side) (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedPositiveInput t) (sigma : Chunk 2) :
    (certificateBetaChild W t r u).probR sigma ≠ 0 ->
      ADVXXZ.chunkLvl sigma = coord W u.1 := by
  intro h
  have hs := (released_child_law_facts t W r (ADVXXZT6Round78.childIndex t u)).2 sigma
  cases W <;>
    simp only [releasedChildCoord] at hs <;>
    rw [kidPat_childIndex] at hs <;>
    apply hs <;>
    simp only [bne_iff_ne] <;>
    intro hn <;>
    apply h <;>
    simp [certificateBetaChild, certificateBetaChildAt, RatDist.probR,
      RawTarget.toDist, hn]

end OmegaBound.ADVXXZT6Round82

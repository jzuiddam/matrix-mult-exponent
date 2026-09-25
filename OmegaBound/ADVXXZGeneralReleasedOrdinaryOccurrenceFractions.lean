import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalNextLink

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000 in
theorem released_left_fraction_at (i : OmegaBound.ADVXXZT2.Occ) :
    (OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD
        (OmegaBound.ADVXXZT2.leftOcc i).val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode).frac =
      OmegaBound.ADVXXZT6.reconstructedFrac (OmegaBound.ADVXXZT2.rowOf i) := by
  have hfrac := OmegaBound.ADVXXZT6.frac_law
  unfold OmegaBound.ADVXXZT6.FracLaw OmegaBound.ADVXXZT6.fracOK at hfrac
  have hall : (List.range 5508).all OmegaBound.ADVXXZT6.fracRowOK = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hfrac).1).1
  have hrow := (List.all_eq_true.mp hall) i.val (List.mem_range.mpr i.isLt)
  unfold OmegaBound.ADVXXZT6.fracRowOK at hrow
  have hincidence : OmegaBound.ADVXXZT6.incidenceArray[i.val]? =
      some (OmegaBound.ADVXXZT2.rowOf i) := by
    simp [OmegaBound.ADVXXZT6.incidenceArray, OmegaBound.ADVXXZT2.rowOf,
      OmegaBound.ADVXXZT1.inc_length, i.isLt]
  have hleft : (OmegaBound.ADVXXZT2.rowOf i).left.val <
      OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.length := by
    rw [OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length]
    exact (OmegaBound.ADVXXZT2.rowOf i).left.isLt
  have hright : (OmegaBound.ADVXXZT2.rowOf i).right.val <
      OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.length := by
    rw [OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length]
    exact (OmegaBound.ADVXXZT2.rowOf i).right.isLt
  have hleftLookup : OmegaBound.ADVXXZT6.termDataArray[(OmegaBound.ADVXXZT2.rowOf i).left.val]? =
      some (OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD
        (OmegaBound.ADVXXZT2.rowOf i).left.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode) := by
    simp [OmegaBound.ADVXXZT6.termDataArray, hleft,
      List.getD_eq_getElem _ _ hleft]
  have hrightLookup : OmegaBound.ADVXXZT6.termDataArray[(OmegaBound.ADVXXZT2.rowOf i).right.val]? =
      some (OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD
        (OmegaBound.ADVXXZT2.rowOf i).right.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode) := by
    simp [OmegaBound.ADVXXZT6.termDataArray, hright,
      List.getD_eq_getElem _ _ hright]
  rw [hincidence] at hrow
  simp only at hrow
  rw [hleftLookup, hrightLookup] at hrow
  simp only [Bool.and_eq_true_iff, beq_iff_eq] at hrow
  exact hrow.1.1.1.2

theorem released_nodeForPattern_childIndex
    (t : Fin 126) (r : Fin 6) (u : ChildShape releasedParent t) :
    OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1 =
      OmegaBound.ADVXXZT2.leftOcc
        (OmegaBound.ADVXXZT6SplitTargetData.occurrence t r
          (OmegaBound.ADVXXZT6Round78.childIndex t u)) := by
  have hk := OmegaBound.ADVXXZT6Round82.kidPat_childIndex t u
  have hpat : OmegaBound.ADVXXZT6SplitTargetData.patShape
      (OmegaBound.ADVXXZT6Selection.kidPat t
        (OmegaBound.ADVXXZT6Round78.childIndex t u)) =
      OmegaBound.ADVXXZT6Round78.childTriple t u := by
    rw [hk]
    rfl
  rw [← hk]
  unfold OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
  rw [if_pos]
  · apply congrArg OmegaBound.ADVXXZT2.leftOcc
    apply Fin.ext
    rw [hpat]
    simp [OmegaBound.ADVXXZT6SplitTargetData.occurrence,
      OmegaBound.ADVXXZT6Round78.childIndex,
      OmegaBound.ADVXXZT6Round78.childIndexNat]
  · have hb := OmegaBound.ADVXXZT6Round78.releasedChildIndexBounds t u
    have hfound := @List.findIdx_getElem _
      (fun v => v == OmegaBound.ADVXXZT6Round78.childTriple t u)
      (OmegaBound.ADVXXZT2.parKids t.1) hb
    have heq :
        (OmegaBound.ADVXXZT2.parKids t.1)[
          OmegaBound.ADVXXZT6Round78.childIndexNat t u]'hb =
            OmegaBound.ADVXXZT6Round78.childTriple t u := by
      simpa [OmegaBound.ADVXXZT6Round78.childIndexNat] using hfound
    rw [hpat, ← heq]
    exact List.getElem_mem hb

theorem released_mlt_childIndex (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedParent t) :
    (OmegaBound.ADVXXZT2.mlt t.val r.val).getD
        (OmegaBound.ADVXXZT6Round78.childIndex t u).val 0 =
      (OmegaBound.ADVXXZT2.regNums t.val).getD r.val 0 *
        ((OmegaBound.ADVXXZT2.chNums t.val r.val).getD
            (OmegaBound.ADVXXZT6Round78.childIndex t u).val 0 +
          (OmegaBound.ADVXXZT2.chNums t.val r.val).getD
            (OmegaBound.ADVXXZT6Round78.childIndex t
              (complement releasedParent t u)).val 0) := by
  have hm := OmegaBound.ADVXXZT2.mult_ok t.val (List.mem_range.mpr t.isLt)
  have hlen := (hm.2.2.1 r.val (List.mem_range.mpr r.isLt)).1
  have hd : (OmegaBound.ADVXXZT6Round78.childIndex t u).val <
      (OmegaBound.ADVXXZT2.chNums t.val r.val).length := by
    rw [hlen]
    exact (OmegaBound.ADVXXZT6Round78.childIndex t u).isLt
  have hdc : (OmegaBound.ADVXXZT6Round78.childIndex t
      (complement releasedParent t u)).val <
      (OmegaBound.ADVXXZT2.chNums t.val r.val).length := by
    rw [hlen]
    exact (OmegaBound.ADVXXZT6Round78.childIndex t
      (complement releasedParent t u)).isLt
  have hcomp0 := congrArg Fin.val
    (OmegaBound.ADVXXZT6Round78.releasedComplementLayout t u)
  have hcomp : (OmegaBound.ADVXXZT6Round78.childIndex t
      (complement releasedParent t u)).val =
      (OmegaBound.ADVXXZT2.parKids t.val).length -
        (1 + (OmegaBound.ADVXXZT6Round78.childIndex t u).val) := by
    change (OmegaBound.ADVXXZT6Round78.childIndex t
      (complement OmegaBound.ADVXXZT9R16PositiveParents.releasedPositiveInput t u)).val = _
    simpa [Nat.add_comm] using hcomp0
  have hrev : (OmegaBound.ADVXXZT2.parKids t.val).length -
      (1 + (OmegaBound.ADVXXZT6Round78.childIndex t u).val) <
      (OmegaBound.ADVXXZT2.chNums t.val r.val).length := by
    omega
  simp [OmegaBound.ADVXXZT2.mlt, OmegaBound.ADVXXZT2.symW,
    List.getD_eq_getElem _ _ hd, List.getD_eq_getElem _ _ hdc,
    hcomp, hlen, hrev, Nat.sub_sub]
  left
  simp [hrev]

set_option maxRecDepth 100000 in
theorem released_outBase_reconstructs_fraction
    (x : ConstituentTerm releasedParent) :
    (releasedConstituentSpec.outBase x : ℚ) = (ordinaryD : ℚ)^4 *
      (OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD
        (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern x.2.1 x.1 x.2.2.1).val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode).frac := by
  let d := OmegaBound.ADVXXZT6Round78.childIndex x.1 x.2.2
  let i := OmegaBound.ADVXXZT6SplitTargetData.occurrence x.1 x.2.1 d
  have hindex : OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern x.2.1 x.1 x.2.2.1 =
      OmegaBound.ADVXXZT2.leftOcc i :=
    released_nodeForPattern_childIndex x.1 x.2.1 x.2.2
  rw [hindex, released_left_fraction_at]
  have hfine :
      (OmegaBound.ADVXXZT2.rowOf i).parent = x.1 ∧
      (OmegaBound.ADVXXZT2.rowOf i).region = x.2.1 ∧
      (OmegaBound.ADVXXZT2.rowOf i).coordinate.val = d.val ∧
      OmegaBound.ADVXXZT2.l2sh (OmegaBound.ADVXXZT2.rowOf i).left.val =
        OmegaBound.ADVXXZT2.kid x.1.val d.val ∧
      OmegaBound.ADVXXZT2.l2sh (OmegaBound.ADVXXZT2.rowOf i).right.val =
        OmegaBound.ADVXXZT2.kidC x.1.val d.val := by
    simpa [i] using
      (OmegaBound.ADVXXZT6SplitTargetData.fine_index_ok x.1 x.2.1 d)
  have hout : releasedConstituentSpec.outBase x =
      OmegaBound.ADVXXZT6.parentCellNum (OmegaBound.ADVXXZT2.rowOf i) *
        (OmegaBound.ADVXXZT2.mlt (OmegaBound.ADVXXZT2.rowOf i).parent.val
          (OmegaBound.ADVXXZT2.rowOf i).region.val).getD
            (OmegaBound.ADVXXZT2.rowOf i).coordinate.val 0 := by
    change OmegaBound.ADVXXZT6Selection.parentMass x.1 *
        (OmegaBound.ADVXXZT2.regNums x.1.val).getD x.2.1.val 0 *
          ((OmegaBound.ADVXXZT2.chNums x.1.val x.2.1.val).getD
              (OmegaBound.ADVXXZT6Round78.childIndex x.1 x.2.2).val 0 +
            (OmegaBound.ADVXXZT2.chNums x.1.val x.2.1.val).getD
              (OmegaBound.ADVXXZT6Round78.childIndex x.1
                (complement releasedParent x.1 x.2.2)).val 0) = _
    unfold OmegaBound.ADVXXZT6.parentCellNum
    simp only
    rw [hfine.1, hfine.2.1, hfine.2.2.1]
    rw [released_mlt_childIndex x.1 x.2.1 x.2.2]
    unfold OmegaBound.ADVXXZT6Selection.parentMass
    ring
  rw [hout]
  unfold OmegaBound.ADVXXZT6.reconstructedFrac
  push_cast
  have hD : (ordinaryD : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < ordinaryD by decide +kernel))
  field_simp [hD]

end OmegaBound.ADVXXZGeneral

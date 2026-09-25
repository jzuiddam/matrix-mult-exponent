import OmegaBound.ADVXXZGeneralReleasedCertificateScaleV22
import OmegaBound.ADVXXZGeneralPopulationConstructorsV22

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace OmegaBound.ADVXXZGeneral

abbrev ReleasedOrdinaryOccurrence :=
  {x : ConstituentTerm releasedParent //
    0 < releasedConstituentSpec.outBase x ∧
    0 < coord .X x.2.2.1 ∧ 0 < coord .Y x.2.2.1 ∧ 0 < coord .Z x.2.2.1}

noncomputable def ordinaryOccurrence0 : ReleasedOrdinaryOccurrence :=
  ⟨⟨0, 0, releasedInteriorChildV22⟩,
    released_interior_child_mass_v22, released_interior_child_grades_v22⟩

noncomputable instance instNonemptyReleasedOrdinaryOccurrence :
    Nonempty ReleasedOrdinaryOccurrence := ⟨ordinaryOccurrence0⟩

noncomputable def ordinaryOccurrence (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :
    ReleasedOrdinaryOccurrence := (Fintype.equivFin ReleasedOrdinaryOccurrence).symm t

noncomputable def releasedOrdinaryParent :
    ConstituentInput 1 (Fintype.card ReleasedOrdinaryOccurrence) where
  terms_nonempty := Fintype.card_pos
  baseN := fun t => releasedConstituentSpec.outBase (ordinaryOccurrence t).1
  baseN_pos := fun t => (ordinaryOccurrence t).2.1
  i := fun t => coord .X (ordinaryOccurrence t).1.2.2.1
  j := fun t => coord .Y (ordinaryOccurrence t).1.2.2.1
  k := fun t => coord .Z (ordinaryOccurrence t).1.2.2.1
  i_pos := fun t => (ordinaryOccurrence t).2.2.1
  j_pos := fun t => (ordinaryOccurrence t).2.2.2.1
  k_pos := fun t => (ordinaryOccurrence t).2.2.2.2
  shape_sum := fun t => (ordinaryOccurrence t).1.2.2.1.2
  beta := fun W t => releasedConstituentSpec.betaChild W
    (ordinaryOccurrence t).1.1 (ordinaryOccurrence t).1.2.1 (ordinaryOccurrence t).1.2.2
  beta_supported := by
    intro W t σ h
    have hs := OmegaBound.ADVXXZT6Round82.certificateBetaChild_supported W
      (ordinaryOccurrence t).1.1 (ordinaryOccurrence t).1.2.1
      (ordinaryOccurrence t).1.2.2 σ h
    cases W <;> exact hs

noncomputable def ordinaryTarget (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :=
  let x := (ordinaryOccurrence t).1
  OmegaBound.ADVXXZT6SplitTargetData.targetNode
    (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern x.2.1 x.1 x.2.2.1)

abbrev ordinaryD : ℕ := OmegaBound.ADVXXZT2.certDen

def ordinaryLargeSide (v : Shape 2) : Side :=
  if coord .X v = 2 then .X else if coord .Y v = 2 then .Y else .Z

abbrev OrdinaryChild (v : Shape 2) :=
  {u : Shape 1 // coord .X u ≤ coord .X v ∧
    coord .Y u ≤ coord .Y v ∧ coord .Z u ≤ coord .Z v}

theorem ordinary_child_counts (v : Shape 2)
    (hx : 0 < coord .X v) (hy : 0 < coord .Y v) (hz : 0 < coord .Z v) :
    (Finset.univ.filter (fun u : OrdinaryChild v => coord (ordinaryLargeSide v) u.1 = 1)).card = 2 ∧
    (Finset.univ.filter (fun u : OrdinaryChild v => ¬ coord (ordinaryLargeSide v) u.1 = 1)).card = 2 := by
  revert v
  decide +kernel

theorem ordinary_mu_table_bound :
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows.all
      (fun x => decide (x.muNum ≤ ordinaryD / 2)) = true := by
  decide +kernel

theorem ordinary_mu_bound (i : Fin 5508) :
    (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).muNum ≤ ordinaryD / 2 := by
  have ha : OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray.all
      (fun x => decide (x.muNum ≤ ordinaryD / 2)) = true := by
    simpa [OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray] using ordinary_mu_table_bound
  have hi : i.val < OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray.size := by
    simpa [OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray,
      OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows_length] using i.isLt
  simp only [Array.all_eq_true] at ha
  have h := ha i.val hi
  simpa [OmegaBound.ADVXXZT6SplitTargetData.targetNode, Array.getD, hi] using h

def ordinaryAlphaDist (v : Shape 2)
    (hx : 0 < coord .X v) (hy : 0 < coord .Y v) (hz : 0 < coord .Z v)
    (muNum : ℕ) (hmu : muNum ≤ ordinaryD / 2) : RatDist (OrdinaryChild v) where
  num := fun u => if coord (ordinaryLargeSide v) u.1 = 1 then ordinaryD / 2 - muNum else muNum
  den := ordinaryD
  den_pos := by decide +kernel
  sum_num := by
    obtain ⟨ha, hb⟩ := ordinary_child_counts v hx hy hz
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, ha, hb]
    have heven : 2 * (ordinaryD / 2) = ordinaryD := by decide +kernel
    omega

def ordinaryRegionDist : RatDist (Fin 6) where
  num := fun r => if r = 0 then 1 else 0
  den := 1
  den_pos := by decide +kernel
  sum_num := by simp

def ordinaryChildBeta (W : Side) (u : Shape 1) : SplitDist 1 where
  num := fun σ => if (σ 0).val = coord W u then 1 else 0
  den := 1
  den_pos := by decide +kernel
  sum_num := by
    revert W u
    decide +kernel

theorem ordinaryTarget_mu_bound (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :
    (ordinaryTarget t).muNum ≤ ordinaryD / 2 :=
  ordinary_mu_bound (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
    (ordinaryOccurrence t).1.2.1 (ordinaryOccurrence t).1.1 (ordinaryOccurrence t).1.2.2.1)

noncomputable def releasedOrdinaryData2 : ConstituentSpec releasedOrdinaryParent where
  A := fun _ => ordinaryRegionDist
  alpha := fun t _ => ordinaryAlphaDist (ordinaryOccurrence t).1.2.2.1
    (ordinaryOccurrence t).2.2.1 (ordinaryOccurrence t).2.2.2.1
    (ordinaryOccurrence t).2.2.2.2 (ordinaryTarget t).muNum (ordinaryTarget_mu_bound t)
  betaRegion := fun W t _ => releasedOrdinaryParent.beta W t
  betaChild := fun W _ _ u => ordinaryChildBeta W u.1
  perm := releasedPerm
  outBase := fun x => if x.2.1 = 0 then
    2 * ordinaryD^3 * releasedOrdinaryParent.baseN x.1 *
      (if coord (ordinaryLargeSide (ordinaryOccurrence x.1).1.2.2.1) x.2.2.1 = 1
        then ordinaryD / 2 - (ordinaryTarget x.1).muNum else (ordinaryTarget x.1).muNum)
    else 0

noncomputable def releasedOrdinaryStep2 : Step (wid (2 - 1)) where
  s := Fintype.card ReleasedOrdinaryOccurrence
  input := releasedOrdinaryParent
  data := releasedOrdinaryData2

noncomputable def releasedOrdinaryStep3 : Step (wid (3 - 1)) where
  s := 126
  input := scaleParent releasedParent (ordinaryD^2) (by decide +kernel)
  data := { releasedConstituentSpec.atScale (ordinaryD^2) (by decide +kernel) with
    outBase := fun x => ordinaryD^4 * releasedConstituentSpec.outBase x }

noncomputable def releasedOrdinaryStage (l : Stage 3) :
    Option (Step (wid (l.val - 1))) :=
  if h : l.val = 3 then by simpa [h] using (some releasedOrdinaryStep3)
  else by
    have h2 : l.val = 2 := by have := l.property; omega
    simpa [h2] using (some releasedOrdinaryStep2)

noncomputable def releasedOrdinaryCertificate : Certificate where
  q := 5
  width := 4
  top := 3
  kappa := 1
  global := releasedGlobalSpec
  stage := releasedOrdinaryStage
  D := ordinaryD^2
  modulus := releasedCertificate.modulus

end OmegaBound.ADVXXZGeneral

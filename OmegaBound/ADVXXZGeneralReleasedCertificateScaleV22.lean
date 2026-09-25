import OmegaBound.ADVXXZGeneralCertScaleV22
import OmegaBound.ADVXXZGeneralReleasedCertificate

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

noncomputable def releasedInteriorChildV22 : ChildShape releasedParent 0 :=
  complement releasedParent 0 releasedFirstChild

theorem released_first_child_shape_v22 :
    coord .X releasedFirstChild.1 = 0 ∧ coord .Y releasedFirstChild.1 = 0 ∧
      coord .Z releasedFirstChild.1 = 4 := by
  have h := OmegaBound.ADVXXZT6Round82.kidPat_childIndex 0 releasedFirstChild
  change OmegaBound.ADVXXZT6Selection.kidPat 0
    ((OmegaBound.ADVXXZT6Round78.childRowEquiv 0) releasedFirstChild) = _ at h
  have hi : (OmegaBound.ADVXXZT6Round78.childRowEquiv 0) releasedFirstChild =
      ⟨0, by decide +kernel⟩ := by
    simp only [releasedFirstChild, id_eq, Equiv.apply_symm_apply]
  rw [hi] at h
  rw [← h]
  decide +kernel

theorem released_interior_child_grades_v22 :
    0 < coord .X releasedInteriorChildV22.1 ∧
    0 < coord .Y releasedInteriorChildV22.1 ∧
    0 < coord .Z releasedInteriorChildV22.1 := by
  have hf := released_first_child_shape_v22
  change 0 < releasedParent.i 0 - coord .X releasedFirstChild.1 ∧
    0 < releasedParent.j 0 - coord .Y releasedFirstChild.1 ∧
    0 < releasedParent.k 0 - coord .Z releasedFirstChild.1
  rw [hf.1, hf.2.1, hf.2.2]
  decide +kernel

theorem released_interior_child_mass_v22 :
    0 < releasedConstituentSpec.outBase ⟨0, 0, releasedInteriorChildV22⟩ := by
  have hi : OmegaBound.ADVXXZT6Round78.childIndex 0 releasedFirstChild =
      ⟨0, by decide +kernel⟩ := by
    change (OmegaBound.ADVXXZT6Round78.childRowEquiv 0) releasedFirstChild = _
    simp only [releasedFirstChild, id_eq, Equiv.apply_symm_apply]
  have hc := OmegaBound.ADVXXZT6Round78.releasedComplementLayout 0 releasedFirstChild
  rw [hi] at hc
  change OmegaBound.ADVXXZT6Round78.childIndex 0 releasedInteriorChildV22 = _ at hc
  change 0 < releasedParent.baseN 0 *
    (OmegaBound.ADVXXZT6Round82.releasedRegionDist 0).num 0 *
      ((OmegaBound.ADVXXZT6Round82.releasedChildRowDist 0 0).num
          (OmegaBound.ADVXXZT6Round78.childIndex 0 releasedInteriorChildV22) + _)
  apply Nat.mul_pos
  · exact Nat.mul_pos (releasedParent.baseN_pos 0) (by decide +kernel)
  · rw [hc]
    exact Nat.add_pos_left (by decide +kernel) _

theorem nonempty_child_inventory_v22 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (x : ConstituentTerm p)
    (hmass : 0 < d.outBase x)
    (hx : 0 < coord .X x.2.2.1) (hy : 0 < coord .Y x.2.2.1)
    (hz : 0 < coord .Z x.2.2.1) :
    ¬ InventoryEq (interior (childInventory d)) [] := by
  classical
  let a : ℚ × AtomKey := ((d.outBase x : ℚ),
    ⟨w, x.2.2.1, fun W σ => (d.betaChild W x.1 x.2.1 x.2.2).prob σ⟩)
  have ha : a ∈ childInventory d := by
    apply List.mem_map.mpr
    refine ⟨(Fintype.equivFin (ConstituentTerm p)) x, by simp, ?_⟩
    exact congrArg (fun y : ConstituentTerm p =>
      ((d.outBase y : ℚ), (⟨w, y.2.2.1,
        fun W σ => (d.betaChild W y.1 y.2.1 y.2.2).prob σ⟩ : AtomKey)))
      ((Fintype.equivFin (ConstituentTerm p)).symm_apply_apply x)
  have hpos : (0 : ℚ) < d.outBase x := by exact_mod_cast hmass
  have hmem : a ∈ (interior (childInventory d)).filter (fun a => decide (a.1 ≠ 0)) := by
    simp only [List.mem_filter, interior, decide_eq_true_eq]
    exact ⟨⟨ha, hpos, hx, hy, hz⟩, ne_of_gt hpos⟩
  intro h
  have hnil := (List.Perm.mem_iff h).mp hmem
  simpa using hnil

theorem releasedCertificate_not_admissible_at : ¬ AdmissibleAt releasedCertificate := by
  intro h
  let l2 : Stage 3 := ⟨2, by omega⟩
  let l3 : Stage 3 := ⟨3, by omega⟩
  have h2 : releasedCertificate.stage l2 = none := by
    simp [releasedCertificate, releasedStage, l2]
  have h3 : releasedCertificate.stage l3 = some releasedStep3 := by
    simp [releasedCertificate, releasedStage, l3]
  have hl := h.next_link l2 l3 (by decide +kernel)
  rw [QAt, h3, P, h2] at hl
  exact nonempty_child_inventory_v22 releasedConstituentSpec
    ⟨0, 0, releasedInteriorChildV22⟩ released_interior_child_mass_v22
    released_interior_child_grades_v22.1 released_interior_child_grades_v22.2.1
    released_interior_child_grades_v22.2.2 hl

end OmegaBound.ADVXXZGeneral

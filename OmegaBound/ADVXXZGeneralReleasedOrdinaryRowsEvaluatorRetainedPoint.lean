import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorTermEquiv

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 10000
set_library_suggestions Lean.LibrarySuggestions.empty
set_option linter.constructorNameAsVariable false
namespace OmegaBound.ADVXXZGeneral

private theorem interior_shape_kind32
    (v : Shape 2) (hx : 0 < coord .X v) (hy : 0 < coord .Y v)
    (hz : 0 < coord .Z v)
    (kind : OmegaBound.ADVXXZLevel2Closure.Kind) (rot : Fin 3)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt kind rot) :
    kind = .k112 := by
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  cases kind <;> fin_cases rot
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp_all <;> omega

private theorem k112_shape_interior32
    (v : Shape 2) (rot : Fin 3)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt .k112 rot) :
    0 < coord .X v ∧ 0 < coord .Y v ∧ 0 < coord .Z v := by
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp_all

noncomputable def releasedAddressRate32
    (x : ConstituentTerm releasedParent) (W : Side) : ℝ :=
  if coord W x.2.2.1 = 2 then
    OmegaBound.ADVXXZLevel2Closure.entropyMu
      ((OmegaBound.ADVXXZT6SplitTargetData.targetNode
        (releasedTermNode32 x)).muNum / (ordinaryD : ℝ))
  else Real.log 2

private theorem address_rate_shape32 (v : Shape 2) (mu : ℝ)
    (rot : Fin 3)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt .k112 rot)
    (W : Side) :
    (if coord W v = 2 then
        OmegaBound.ADVXXZLevel2Closure.entropyMu mu else Real.log 2) =
      OmegaBound.ADVXXZLevel2Closure.rotate
        (OmegaBound.ADVXXZLevel2Closure.retainedStandard .k112 mu) rot
        (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  fin_cases rot <;> cases W
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape,
      Function.iterate_succ_apply, Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals
    simp [OmegaBound.ADVXXZLevel2Closure.rotate,
      OmegaBound.ADVXXZLevel2Closure.retainedStandard,
      OmegaBound.ADVXXZT6Round82.sideIndex] <;> simp_all

theorem releasedAddressRate_eq_releasedTerm32
    (x : ConstituentTerm releasedParent)
    (hx : 0 < coord .X x.2.2.1) (hy : 0 < coord .Y x.2.2.1)
    (hz : 0 < coord .Z x.2.2.1) (W : Side) :
    releasedAddressRate32 x W =
      OmegaBound.ADVXXZLevel2Closure.rotate
        (OmegaBound.ADVXXZLevel2Closure.retainedStandard
          (OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).kind
          (((OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).mu.getD 0 : ℚ) : ℝ))
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).rot
        (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
  have hshape := released_child_target_shape x.1 x.2.1 x.2.2
  rw [← releasedTermNode_eq_nodeForPattern32 x] at hshape
  have hkind := interior_shape_kind32 x.2.2.1 hx hy hz
    (OmegaBound.ADVXXZT6SplitTargetData.targetNode
      (releasedTermNode32 x)).kind
    (OmegaBound.ADVXXZT6SplitTargetData.targetNode
      (releasedTermNode32 x)).rot hshape
  have hm := released_ordinary_target_metadata_dataById32
    (releasedTermNode32 x)
  dsimp only at hm
  rcases hm with ⟨hmkind, hmrot, hmu⟩
  have hdataKind :
      (OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 x)).kind = .k112 := hmkind.symm.trans hkind
  have hshape' :
      (coord .X x.2.2.1, coord .Y x.2.2.1, coord .Z x.2.2.1) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt .k112
          (OmegaBound.ADVXXZT6SplitTargetData.targetNode
            (releasedTermNode32 x)).rot := by
    simpa only [hkind] using hshape
  rw [if_pos (Or.inl hkind)] at hmu
  unfold releasedAddressRate32
  rw [hdataKind, ← hmrot, hmu]
  simp only [Option.getD_some]
  push_cast
  exact address_rate_shape32 x.2.2.1
    ((OmegaBound.ADVXXZT6SplitTargetData.targetNode
      (releasedTermNode32 x)).muNum / (ordinaryD : ℝ))
    (OmegaBound.ADVXXZT6SplitTargetData.targetNode
      (releasedTermNode32 x)).rot hshape' W

theorem released_active_term_retained32
    (x : ConstituentTerm releasedParent) (hx : OrdinaryStageActive x)
    (W : Side) :
    (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).toTerm.retained
        (OmegaBound.ADVXXZT6Round82.sideIndex W) =
      ((releasedConstituentSpec.outBase x : ℝ) / (ordinaryD : ℝ)^4) *
        releasedAddressRate32 x W := by
  have hrate := releasedAddressRate_eq_releasedTerm32 x
    hx.2.1 hx.2.2.1 hx.2.2.2 W
  have hfracQ := released_outBase_reconstructs_fraction x
  rw [← releasedTermNode_eq_nodeForPattern32 x,
    releasedTable_getD_eq_dataById32] at hfracQ
  have hfracR :
      (releasedConstituentSpec.outBase x : ℝ) =
        (ordinaryD : ℝ)^4 *
          (OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).frac := by
    exact_mod_cast hfracQ
  rw [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
    OmegaBound.ADVXXZLevel2Closure.Term.retained, ← hrate, hfracR]
  have hD : (ordinaryD : ℝ) ≠ 0 := by
    exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
  field_simp

theorem released_inactive_term_retained_zero32
    (x : ConstituentTerm releasedParent) (hx : ¬ OrdinaryStageActive x)
    (W : Side) :
    (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).toTerm.retained
        (OmegaBound.ADVXXZT6Round82.sideIndex W) = 0 := by
  have hshape := released_child_target_shape x.1 x.2.1 x.2.2
  rw [← releasedTermNode_eq_nodeForPattern32 x] at hshape
  have hm := released_ordinary_target_metadata_dataById32
    (releasedTermNode32 x)
  dsimp only at hm
  rcases hm with ⟨hmkind, hmrot, hmu⟩
  by_cases hinter :
      0 < coord .X x.2.2.1 ∧ 0 < coord .Y x.2.2.1 ∧
        0 < coord .Z x.2.2.1
  · have hmass : releasedConstituentSpec.outBase x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      exact hx ⟨hp, hinter⟩
    have hfracQ := released_outBase_reconstructs_fraction x
    rw [← releasedTermNode_eq_nodeForPattern32 x,
      releasedTable_getD_eq_dataById32, hmass] at hfracQ
    have hprod :
        (ordinaryD : ℚ)^4 *
          (OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).frac = 0 := hfracQ.symm
    have hD : (ordinaryD : ℚ)^4 ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
    have hfrac :
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).frac = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hD
    simp [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
      OmegaBound.ADVXXZLevel2Closure.Term.retained, hfrac]
  · have htargetKind :
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode
          (releasedTermNode32 x)).kind ≠ .k112 := by
      intro hk
      apply hinter
      apply k112_shape_interior32 x.2.2.1
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode
          (releasedTermNode32 x)).rot
      simpa only [hk] using hshape
    have hdataKind :
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).kind ≠ .k112 := by
      intro hk
      exact htargetKind (hmkind.trans hk)
    have hzero (rot d : Fin 3) : (![0, 0, 0] : Fin 3 → ℝ) (d + rot) = 0 := by
      fin_cases rot <;> fin_cases d <;> rfl
    generalize hd :
      OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 x) = d at hdataKind ⊢
    rcases d with ⟨node, kind, rot, frac, mu⟩
    cases kind with
    | k112 => exact (hdataKind rfl).elim
    | k022 =>
        simp only [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
          OmegaBound.ADVXXZLevel2Closure.Term.retained,
          OmegaBound.ADVXXZLevel2Closure.retainedStandard,
          OmegaBound.ADVXXZLevel2Closure.rotate]
        exact mul_eq_zero_of_right _ (hzero rot _)
    | k013 =>
        simp only [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
          OmegaBound.ADVXXZLevel2Closure.Term.retained,
          OmegaBound.ADVXXZLevel2Closure.retainedStandard,
          OmegaBound.ADVXXZLevel2Closure.rotate]
        exact mul_eq_zero_of_right _ (hzero rot _)
    | k031 =>
        simp only [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
          OmegaBound.ADVXXZLevel2Closure.Term.retained,
          OmegaBound.ADVXXZLevel2Closure.retainedStandard,
          OmegaBound.ADVXXZLevel2Closure.rotate]
        exact mul_eq_zero_of_right _ (hzero rot _)
    | k004 =>
        simp only [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
          OmegaBound.ADVXXZLevel2Closure.Term.retained,
          OmegaBound.ADVXXZLevel2Closure.retainedStandard,
          OmegaBound.ADVXXZLevel2Closure.rotate]
        exact mul_eq_zero_of_right _ (hzero rot _)

theorem released_term_retained32
    (x : ConstituentTerm releasedParent) (W : Side) :
    (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).toTerm.retained
        (OmegaBound.ADVXXZT6Round82.sideIndex W) =
      if h : OrdinaryStageActive x then
        ((releasedConstituentSpec.outBase x : ℝ) / (ordinaryD : ℝ)^4) *
          releasedAddressRate32 x W
      else 0 := by
  split_ifs with h
  · exact released_active_term_retained32 x h W
  · exact released_inactive_term_retained_zero32 x h W

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixStage2

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
set_option linter.constructorNameAsVariable false
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6Round82 (sideIndex)

private def ordinaryStage2LargeActiveCount32 (v : Shape 2) (W : Side) : ℕ :=
  (Finset.univ.filter fun u : OrdinaryChild v =>
    OrdinaryStage2Active W u.1 ∧
      coord (ordinaryLargeSide v) u.1 = 1).card

private def ordinaryStage2OtherActiveCount32 (v : Shape 2) (W : Side) : ℕ :=
  (Finset.univ.filter fun u : OrdinaryChild v =>
    OrdinaryStage2Active W u.1 ∧
      coord (ordinaryLargeSide v) u.1 ≠ 1).card

-- This closed census ranges only over the fifteen width-two shapes and their children.
set_option maxHeartbeats 1000000 in
private theorem ordinary_stage2_active_counts_rotate32
    (v : Shape 2) (rot : Fin 3)
    (hshape : (coord .X v, coord .Y v, coord .Z v) =
      OmegaBound.ADVXXZLevel2Closure.shapeAt .k112 rot)
    (W : Side) :
    (ordinaryStage2LargeActiveCount32 v W,
      ordinaryStage2OtherActiveCount32 v W) =
      if sideIndex W + rot = 1 then (0, 1) else (1, 0) := by
  revert v rot W
  decide +kernel

private theorem ordinary_stage2_weight_sum32 (v : Shape 2) (W : Side)
    (large other : ℝ) :
    (∑ u : OrdinaryChild v,
      if OrdinaryStage2Active W u.1 then
        if coord (ordinaryLargeSide v) u.1 = 1 then large else other
      else 0) =
      (ordinaryStage2LargeActiveCount32 v W : ℝ) * large +
        (ordinaryStage2OtherActiveCount32 v W : ℝ) * other := by
  classical
  calc
    _ = (∑ u : OrdinaryChild v,
          if OrdinaryStage2Active W u.1 ∧
              coord (ordinaryLargeSide v) u.1 = 1 then large else 0) +
        ∑ u : OrdinaryChild v,
          if OrdinaryStage2Active W u.1 ∧
              coord (ordinaryLargeSide v) u.1 ≠ 1 then other else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      by_cases ha : OrdinaryStage2Active W u.1 <;>
        by_cases hl : coord (ordinaryLargeSide v) u.1 = 1 <;>
        simp [ha, hl]
    _ = _ := by
      change (∑ u ∈ (Finset.univ : Finset (OrdinaryChild v)),
          if OrdinaryStage2Active W u.1 ∧
              coord (ordinaryLargeSide v) u.1 = 1 then large else 0) +
        (∑ u ∈ (Finset.univ : Finset (OrdinaryChild v)),
          if OrdinaryStage2Active W u.1 ∧
              coord (ordinaryLargeSide v) u.1 ≠ 1 then other else 0) = _
      rw [← Finset.sum_filter, ← Finset.sum_filter,
        Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      rfl

-- The additional budget covers elaboration of the dependent child-shape sum.
set_option maxHeartbeats 1000000 in
/-- The active width-one child weights are exactly the rotated `k112` matrix
coefficient, before multiplication by the parent fraction. -/
theorem ordinary_stage2_child_weight_rotate32
    (v : Shape 2) (rot : Fin 3)
    (hshape : (coord .X v, coord .Y v, coord .Z v) =
      OmegaBound.ADVXXZLevel2Closure.shapeAt .k112 rot)
    (W : Side) (mu : ℕ) (hmu : mu ≤ ordinaryD / 2) :
    (2 * (∑ u : OrdinaryChild v,
        if OrdinaryStage2Active W u.1 then
          (((if coord (ordinaryLargeSide v) u.1 = 1 then
              ordinaryD / 2 - mu else mu) : ℕ) : ℝ)
        else 0) / (ordinaryD : ℝ)) * Real.log 5 =
      OmegaBound.ADVXXZLevel2Closure.rotate
        (OmegaBound.ADVXXZLevel2Closure.matrixStandard 5 .k112
          ((mu : ℝ) / (ordinaryD : ℝ))) rot (sideIndex W) := by
  simp only [Nat.cast_ite]
  rw [ordinary_stage2_weight_sum32]
  have hc := ordinary_stage2_active_counts_rotate32 v rot hshape W
  have heven : 2 * (ordinaryD / 2) = ordinaryD := by decide +kernel
  have hevenR : (2 : ℝ) * (ordinaryD / 2 : ℕ) = (ordinaryD : ℝ) := by
    exact_mod_cast heven
  have hsub : ((ordinaryD / 2 - mu : ℕ) : ℝ) =
      ((ordinaryD / 2 : ℕ) : ℝ) - (mu : ℝ) := Nat.cast_sub hmu
  have hD : (ordinaryD : ℝ) ≠ 0 := by
    exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
  have hcL := congrArg Prod.fst hc
  have hcO := congrArg Prod.snd hc
  fin_cases rot <;> cases W
  all_goals
    simp [sideIndex, OmegaBound.ADVXXZLevel2Closure.rotate,
      OmegaBound.ADVXXZLevel2Closure.matrixStandard] at hcL hcO ⊢
  all_goals
    rw [hcL, hcO]
    norm_num
    try rw [hsub]
    field_simp [hD] <;> nlinarith [hevenR]

/-- `outBase` is supported on region zero, so one level-two parent fibre is
the released `2 * D^3` multiplicity times its active child weight. -/
theorem ordinary_stage2_outBase_fiber32
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (W : Side) :
    (∑ ru : Fin 6 × ChildShape releasedOrdinaryParent t,
      if OrdinaryStage2Active W ru.2.1 then
        releasedOrdinaryData2.outBase ⟨t, ru.1, ru.2⟩ else 0) =
      2 * ordinaryD ^ 3 * releasedOrdinaryParent.baseN t *
        ∑ u : OrdinaryChild (ordinaryOccurrence t).1.2.2.1,
          if OrdinaryStage2Active W u.1 then
            if coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) u.1 = 1
            then ordinaryD / 2 - (ordinaryTarget t).muNum
            else (ordinaryTarget t).muNum
          else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [releasedOrdinaryData2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fin.sum_univ_six]
  by_cases ha : OrdinaryStage2Active W u.1
  · simp [ha]
  · simp [ha]

private theorem ordinary_interior_kind_stage2_32
    (v : Shape 2) (hx : 0 < coord .X v) (hy : 0 < coord .Y v)
    (hz : 0 < coord .Z v)
    (kind : OmegaBound.ADVXXZLevel2Closure.Kind) (rot : Fin 3)
    (hshape : (coord .X v, coord .Y v, coord .Z v) =
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

/-- One positive interior occurrence's complete region/child `Q2` mass, after the
single `D^8` normalization, is its released `k112` matrix term. -/
theorem ordinary_stage2_fiber_matrix32
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (W : Side) :
    Real.log 5 *
        (((∑ ru : Fin 6 × ChildShape releasedOrdinaryParent t,
          if OrdinaryStage2Active W ru.2.1 then
            releasedOrdinaryData2.outBase ⟨t, ru.1, ru.2⟩ else 0) : ℕ) : ℝ) /
        (ordinaryD : ℝ) ^ 8 =
      (OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 (ordinaryOccurrence t).1)).toTerm.matrix 5
          (sideIndex W) := by
  let x := (ordinaryOccurrence t).1
  let n := releasedTermNode32 x
  let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode n
  let data := OmegaBound.ADVXXZT7SpecialInventory.dataById n
  have hshape := released_child_target_shape x.1 x.2.1 x.2.2
  rw [← releasedTermNode_eq_nodeForPattern32 x] at hshape
  have hk : d.kind = .k112 := ordinary_interior_kind_stage2_32 x.2.2.1
    (ordinaryOccurrence t).2.2.1 (ordinaryOccurrence t).2.2.2.1
    (ordinaryOccurrence t).2.2.2.2 d.kind d.rot hshape
  have hm := released_ordinary_target_metadata_dataById32 n
  dsimp only [d, data] at hm
  rcases hm with ⟨hmkind, hmrot, hmu⟩
  have hdataKind : data.kind = .k112 := hmkind.symm.trans hk
  rw [if_pos (Or.inl hk)] at hmu
  have htarget : ordinaryTarget t = d := by
    simpa only [ordinaryTarget, d, n, x] using
      congrArg OmegaBound.ADVXXZT6SplitTargetData.targetNode
        (releasedTermNode_eq_nodeForPattern32 (ordinaryOccurrence t).1).symm
  have hshape' :
      (coord .X x.2.2.1, coord .Y x.2.2.1, coord .Z x.2.2.1) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt .k112 d.rot := by
    rw [hk] at hshape
    exact hshape
  have hweight := ordinary_stage2_child_weight_rotate32 x.2.2.1 d.rot hshape' W
    (ordinaryTarget t).muNum (ordinaryTarget_mu_bound t)
  have hfiberR :
      (((∑ ru : Fin 6 × ChildShape releasedOrdinaryParent t,
        if OrdinaryStage2Active W ru.2.1 then
          releasedOrdinaryData2.outBase ⟨t, ru.1, ru.2⟩ else 0) : ℕ) : ℝ) =
        (2 : ℝ) * (ordinaryD : ℝ) ^ 3 *
          (releasedOrdinaryParent.baseN t : ℝ) *
          ∑ u : OrdinaryChild (ordinaryOccurrence t).1.2.2.1,
            if OrdinaryStage2Active W u.1 then
              (((if coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) u.1 = 1
                then ordinaryD / 2 - (ordinaryTarget t).muNum
                else (ordinaryTarget t).muNum) : ℕ) : ℝ)
            else 0 := by
    exact_mod_cast ordinary_stage2_outBase_fiber32 t W
  have hfracQ := released_outBase_reconstructs_fraction x
  rw [← releasedTermNode_eq_nodeForPattern32 x,
    releasedTable_getD_eq_dataById32] at hfracQ
  have hfracR : (releasedOrdinaryParent.baseN t : ℝ) =
      (ordinaryD : ℝ) ^ 4 * (data.frac : ℝ) := by
    change (releasedConstituentSpec.outBase x : ℝ) = _
    exact_mod_cast hfracQ
  have hD : (ordinaryD : ℝ) ≠ 0 := by
    exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
  rw [hfiberR]
  change _ = data.toTerm.matrix 5 (sideIndex W)
  rw [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
    OmegaBound.ADVXXZLevel2Closure.Term.matrix, hdataKind, ← hmrot, hmu]
  simp only [Option.getD_some]
  push_cast
  rw [htarget] at hweight
  simp only [Nat.cast_ite] at hweight
  dsimp only [x] at hweight
  rw [htarget]
  rw [hfracR]
  rw [← hweight]
  field_simp [hD] <;> ring

/-- **The complete `Q2` interior census.**  After `D^8` normalization it is
the sum of the released `k112` matrix terms indexed by the positive interior
level-three occurrences. -/
theorem ordinary_stage2_matrix_census32 (W : Side) :
    ordinaryInventoryRate 5 W
        (QAt releasedOrdinaryCertificatePhysical ordinaryLevel2) /
        (ordinaryD : ℝ) ^ 8 =
      ∑ t : Fin (Fintype.card ReleasedOrdinaryOccurrence),
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 (ordinaryOccurrence t).1)).toTerm.matrix 5
            (sideIndex W) := by
  rw [ordinary_stage2_inventory_rate32, Fintype.sum_sigma,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  have hcast :
      (∑ ru : Fin 6 × ChildShape releasedOrdinaryParent t,
        if OrdinaryStage2Active W ru.2.1 then
          (releasedOrdinaryData2.outBase ⟨t, ru.1, ru.2⟩ : ℝ) else 0) =
        (((∑ ru : Fin 6 × ChildShape releasedOrdinaryParent t,
          if OrdinaryStage2Active W ru.2.1 then
            releasedOrdinaryData2.outBase ⟨t, ru.1, ru.2⟩ else 0) : ℕ) : ℝ) := by
    exact_mod_cast rfl
  rw [hcast]
  exact ordinary_stage2_fiber_matrix32 t W

end OmegaBound.ADVXXZGeneral
end

import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixQ3

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 5000
set_library_suggestions Lean.LibrarySuggestions.empty
set_option linter.constructorNameAsVariable false
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6SplitTargetData (TargetNode wordId)
open OmegaBound.ADVXXZT6Round82 (sideIndex)

/-- The interior/boundary split used to partition the complete released level-two
matrix row without inspecting the 5,508-row table. -/
def OrdinaryInterior32 (x : ConstituentTerm releasedParent) : Prop :=
  0 < coord .X x.2.2.1 ∧ 0 < coord .Y x.2.2.1 ∧ 0 < coord .Z x.2.2.1

instance instDecidableOrdinaryInterior32 (x : ConstituentTerm releasedParent) :
    Decidable (OrdinaryInterior32 x) := by
  unfold OrdinaryInterior32
  infer_instance

private theorem ordinary_k112_interior_q3_32
    (v : Shape 2) (rot : Fin 3)
    (hshape : (coord .X v, coord .Y v, coord .Z v) =
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

private theorem released_boundary_term_matrix_target32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) (W : Side)
    (hk : (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).kind ≠ .k112) :
    (OmegaBound.ADVXXZT7SpecialInventory.dataById i).toTerm.matrix 5 (sideIndex W) =
      ((OmegaBound.ADVXXZT7SpecialInventory.dataById i).frac : ℝ) *
        OmegaBound.ADVXXZLevel2Closure.rotate
          (OmegaBound.ADVXXZLevel2Closure.matrixStandard 5
            (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).kind
            (((OmegaBound.ADVXXZT6SplitTargetData.targetNode i).muNum : ℝ) /
              (ordinaryD : ℝ)))
          (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).rot (sideIndex W) := by
  have hm := released_ordinary_target_metadata_dataById32 i
  dsimp only at hm
  rcases hm with ⟨hmkind, hmrot, hmu⟩
  rw [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
    OmegaBound.ADVXXZLevel2Closure.Term.matrix, ← hmkind, ← hmrot]
  cases hkind : (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).kind
  · exact (hk hkind).elim
  · rw [if_pos (Or.inr hkind)] at hmu
    rw [hmu]
    simp only [Option.getD_some]
    push_cast
    rfl
  · rw [if_neg (by simp [hkind])] at hmu
    simp [hmu, OmegaBound.ADVXXZLevel2Closure.matrixStandard]
  · rw [if_neg (by simp [hkind])] at hmu
    simp [hmu, OmegaBound.ADVXXZLevel2Closure.matrixStandard]
  · rw [if_neg (by simp [hkind])] at hmu
    simp [hmu, OmegaBound.ADVXXZLevel2Closure.matrixStandard]

/-- One non-interior level-three address contributes its corresponding released
boundary matrix term after `D^8` normalization; an interior address contributes zero. -/
theorem ordinary_stage3_address_matrix32
    (x : ConstituentTerm releasedParent) (W : Side) :
    ordinaryAtomRate 5 W
        ((((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℕ) : ℚ),
          (⟨2, x.2.2.1, fun V σ =>
            (releasedConstituentSpec.betaChild V x.1 x.2.1 x.2.2).prob σ⟩ : AtomKey)) /
        (ordinaryD : ℝ) ^ 8 =
      if OrdinaryInterior32 x then 0 else
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W) := by
  by_cases hinter : OrdinaryInterior32 x
  · rw [if_pos hinter]
    rw [ordinary_atom_rate_interior_zero32 W]
    · simp
    · exact hinter.1
    · exact hinter.2.1
    · exact hinter.2.2
  · rw [if_neg hinter]
    let i := releasedTermNode32 x
    let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode i
    have hshape := released_child_target_shape x.1 x.2.1 x.2.2
    rw [← releasedTermNode_eq_nodeForPattern32 x] at hshape
    have hk : d.kind ≠ .k112 := by
      intro hk
      apply hinter
      rw [hk] at hshape
      exact ordinary_k112_interior_q3_32 x.2.2.1 d.rot hshape
    have hrate := ordinary_boundary_atom_rate32 W
      (((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℕ) : ℚ)
      x.2.2.1 d (ordinary_mu_bound i) hshape hk
    have hrate' :
        ordinaryAtomRate 5 W
            ((((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℕ) : ℚ),
              (⟨2, x.2.2.1, fun V σ =>
                (releasedConstituentSpec.betaChild V x.1 x.2.1 x.2.2).prob σ⟩ : AtomKey)) =
          ((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℝ) *
            OmegaBound.ADVXXZLevel2Closure.rotate
              (OmegaBound.ADVXXZLevel2Closure.matrixStandard 5 d.kind
                ((d.muNum : ℝ) / (ordinaryD : ℝ))) d.rot (sideIndex W) := by
      have hbeta : (fun V σ =>
          (releasedConstituentSpec.betaChild V x.1 x.2.1 x.2.2).prob σ) =
          (fun V σ => ((d.raw (sideIndex V)).nums (wordId σ) : ℚ) /
            (ordinaryD : ℚ)) := by
        funext V σ
        simp only [releasedConstituentSpec,
          OmegaBound.ADVXXZT6Round82.certificateBetaChild,
          OmegaBound.ADVXXZT6Round82.certificateBetaChildAt,
          OmegaBound.ADVXXZT6Round82.releasedChildRawAt,
          OmegaBound.ADVXXZT6SplitTargetData.fineRaw,
          OmegaBound.ADVXXZT6Round82.kidPat_childIndex,
          OmegaBound.ADVXXZT6SplitTargetData.RawTarget.toDist,
          RatDist.prob, d, i]
        rw [← releasedTermNode_eq_nodeForPattern32 x]
        rfl
      rw [hbeta]
      exact hrate
    have hterm := released_boundary_term_matrix_target32 i W hk
    have hfracQ := released_outBase_reconstructs_fraction x
    rw [← releasedTermNode_eq_nodeForPattern32 x,
      releasedTable_getD_eq_dataById32] at hfracQ
    have hfracR : (releasedConstituentSpec.outBase x : ℝ) =
        (ordinaryD : ℝ) ^ 4 *
          ((OmegaBound.ADVXXZT7SpecialInventory.dataById i).frac : ℝ) := by
      exact_mod_cast hfracQ
    have hD : (ordinaryD : ℝ) ≠ 0 := by
      exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
    rw [hrate']
    rw [hterm]
    push_cast
    rw [hfracR]
    field_simp [hD] <;> ring

/-- **The complete `Q3` boundary census.**  After `D^8` normalization it is
the sum of all non-interior released matrix terms. -/
theorem ordinary_stage3_matrix_census32 (W : Side) :
    ordinaryInventoryRate 5 W
        (QAt releasedOrdinaryCertificatePhysical ordinaryLevel3) /
        (ordinaryD : ℝ) ^ 8 =
      ∑ x : ConstituentTerm releasedParent,
        if OrdinaryInterior32 x then 0 else
          (OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W) := by
  rw [ordinary_stage_inventory_rate32 W ordinaryLevel3 releasedOrdinaryStep3
    ordinary_stage3_eq32, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  exact ordinary_stage3_address_matrix32 x W

end OmegaBound.ADVXXZGeneral
end

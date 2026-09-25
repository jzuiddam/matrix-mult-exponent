import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixStage2Census
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixQ3Census

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 5000
set_library_suggestions Lean.LibrarySuggestions.empty
set_option linter.constructorNameAsVariable false
namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6Round82 (sideIndex)

private theorem sum_get_reindex_matrix32 {α : Type*} {M : Type*} [AddCommMonoid M]
    (L : List α) (N : ℕ) (hL : L.length = N) (f : α → M) :
    ∑ a : Fin L.length, f (L.get a) =
      ∑ i : Fin N, f (L.get ⟨i.val, by rw [hL]; exact i.isLt⟩) := by
  subst hL
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- Reindex the released matrix row by constituent addresses without comparing the
literal 5,508-row table to its own length. -/
theorem matrixRow_eq_sum_addresses32 (W : Side) :
    OmegaBound.ADVXXZLevel2Closure.matrixRow 5
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms (sideIndex W) =
      ∑ x : ConstituentTerm releasedParent,
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W) := by
  unfold OmegaBound.ADVXXZLevel2Closure.matrixRow
    OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms
  rw [sum_get_reindex_matrix32
    OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable 5508
    OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length
    (fun data => data.toTerm.matrix 5 (sideIndex W))]
  rw [show (∑ i : OmegaBound.ADVXXZCertSemantic.Level2TermId,
      (OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.get
        ⟨i.val, by
          rw [OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length]
          exact i.isLt⟩).toTerm.matrix 5 (sideIndex W)) =
      ∑ i : OmegaBound.ADVXXZCertSemantic.Level2TermId,
        (OmegaBound.ADVXXZT7SpecialInventory.dataById i).toTerm.matrix 5
          (sideIndex W) by
    apply Finset.sum_congr rfl
    intro i _
    rw [← releasedTable_getD_eq_dataById32 i]
    rw [List.getD_eq_getElem _ _ (by
      rw [OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length]
      exact i.isLt)]
    rfl]
  exact (Equiv.sum_comp releasedTermEquiv32
    (fun i => (OmegaBound.ADVXXZT7SpecialInventory.dataById i).toTerm.matrix 5
      (sideIndex W))).symm

private theorem released_zero_mass_term_matrix32
    (x : ConstituentTerm releasedParent)
    (hmass : releasedConstituentSpec.outBase x = 0) (W : Side) :
    (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W) = 0 := by
  have hfracQ := released_outBase_reconstructs_fraction x
  rw [← releasedTermNode_eq_nodeForPattern32 x,
    releasedTable_getD_eq_dataById32, hmass] at hfracQ
  have hD : (ordinaryD : ℚ) ^ 4 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (show ordinaryD ≠ 0 by decide +kernel)
  have hfrac : (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).frac = 0 :=
    (mul_eq_zero.mp hfracQ.symm).resolve_left hD
  simp [OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData.toTerm,
    OmegaBound.ADVXXZLevel2Closure.Term.matrix, hfrac]

private theorem stage2_matrix_sum_as_addresses32 (W : Side) :
    (∑ t : Fin (Fintype.card ReleasedOrdinaryOccurrence),
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 (ordinaryOccurrence t).1)).toTerm.matrix 5
            (sideIndex W)) =
      ∑ x : ConstituentTerm releasedParent,
        if OrdinaryStageActive x then
          (OmegaBound.ADVXXZT7SpecialInventory.dataById
            (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W)
        else 0 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := OrdinaryStageActive)
    (F := (inferInstance : Fintype ReleasedOrdinaryOccurrence))
    (Finset.univ.filter OrdinaryStageActive)
    (fun x => by simp)
    (fun x => (OmegaBound.ADVXXZT7SpecialInventory.dataById
      (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W))]
  rw [← Equiv.sum_comp (Fintype.equivFin ReleasedOrdinaryOccurrence).symm
    (fun x : ReleasedOrdinaryOccurrence =>
      (OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 x.1)).toTerm.matrix 5 (sideIndex W))]
  rfl

private theorem matrix_address_split32 (x : ConstituentTerm releasedParent) (W : Side) :
    (if OrdinaryStageActive x then
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W)
      else 0) +
      (if OrdinaryInterior32 x then 0 else
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W)) =
      (OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 x)).toTerm.matrix 5 (sideIndex W) := by
  by_cases hinter : OrdinaryInterior32 x
  · rw [if_pos hinter]
    by_cases hmass : 0 < releasedConstituentSpec.outBase x
    · rw [if_pos (⟨hmass, hinter⟩)]
      simp
    · have hzero : releasedConstituentSpec.outBase x = 0 := Nat.eq_zero_of_not_pos hmass
      rw [if_neg (fun h => hmass h.1), released_zero_mass_term_matrix32 x hzero W]
      simp
  · rw [if_neg hinter, if_neg]
    · simp
    · exact fun h => hinter h.2

/-- **The released ordinary matrix census.**  The level-three boundary and
level-two descendant inventories together give the complete released matrix row,
with the denominator applied exactly once. -/
theorem released_ordinary_matrix_census32 (W : Side) :
    (ordinaryInventoryRate 5 W
          (QAt releasedOrdinaryCertificatePhysical ordinaryLevel3) +
        ordinaryInventoryRate 5 W
          (QAt releasedOrdinaryCertificatePhysical ordinaryLevel2)) /
        (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 4 =
      OmegaBound.ADVXXZLevel2Closure.matrixRow 5
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms (sideIndex W) := by
  have hden : (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 4 =
      (ordinaryD : ℝ) ^ 8 := by
    simp only [releasedOrdinaryCertificatePhysical, Nat.cast_pow]
    ring
  rw [hden, add_div, ordinary_stage3_matrix_census32,
    ordinary_stage2_matrix_census32, stage2_matrix_sum_as_addresses32,
    matrixRow_eq_sum_addresses32]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [add_comm] using matrix_address_split32 x W

end OmegaBound.ADVXXZGeneral
end

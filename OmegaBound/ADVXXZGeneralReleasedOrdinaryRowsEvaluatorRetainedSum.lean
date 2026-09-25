import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorRetainedPoint
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorPenalty

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- The complete directional occurrence total: every positive interior level-three
address, weighted by its released out-base multiplicity and by its own `112` nats. -/
noncomputable def ordinaryDirectionalTotal (W : Side) : ℝ :=
  ∑ t, (releasedOrdinaryParent.baseN t : ℝ) * ordinary112Nats t W

/-- Positional reindexing of a list lookup sum, stated for a **variable** list and a
**variable** length so that no elaboration step ever compares the released table's
literal length with `5508` (which would force the 5,508-row append chain into weak
head normal form). -/
private theorem sum_get_reindex32 {α : Type*} {M : Type*} [AddCommMonoid M]
    (L : List α) (N : ℕ) (hL : L.length = N) (f : α → M) :
    ∑ a : Fin L.length, f (L.get a) =
      ∑ i : Fin N, f (L.get ⟨i.val, by rw [hL]; exact i.isLt⟩) := by
  subst hL
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- Reindex the released level-two retained row by the typed node id. -/
theorem retainedRow_eq_sum_dataById32 (d : Fin 3) :
    OmegaBound.ADVXXZLevel2Closure.retainedRow
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms d =
      ∑ i : OmegaBound.ADVXXZCertSemantic.Level2TermId,
        (OmegaBound.ADVXXZT7SpecialInventory.dataById i).toTerm.retained d :=
  sum_get_reindex32 OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable 5508
    OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable_length
    (fun data => data.toTerm.retained d)

/-- The same row, indexed by the constituent addresses through the bijection `releasedTermEquiv32`. -/
theorem retainedRow_eq_sum_addresses32 (W : Side) :
    OmegaBound.ADVXXZLevel2Closure.retainedRow
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms
        (OmegaBound.ADVXXZT6Round82.sideIndex W) =
      ∑ x : ConstituentTerm releasedParent,
        (OmegaBound.ADVXXZT7SpecialInventory.dataById
          (releasedTermNode32 x)).toTerm.retained
            (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
  rw [retainedRow_eq_sum_dataById32]
  exact (Equiv.sum_comp releasedTermEquiv32
    (fun i => (OmegaBound.ADVXXZT7SpecialInventory.dataById i).toTerm.retained
      (OmegaBound.ADVXXZT6Round82.sideIndex W))).symm

/-- The address rate at an interior occurrence is exactly the printed `112` nats. -/
theorem releasedAddressRate_eq_ordinary112Nats32
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (W : Side) :
    releasedAddressRate32 (ordinaryOccurrence t).1 W = ordinary112Nats t W := by
  unfold releasedAddressRate32 ordinary112Nats
  rw [releasedTermNode_eq_nodeForPattern32]
  rfl

/-- **The weighted occurrence census.**  The complete released level-two retained
row in direction `W` is the total interior occurrence mass times its address
entropy, normalised once by `ordinaryD ^ 4`. -/
theorem released_retained_row_census32 (W : Side) :
    OmegaBound.ADVXXZLevel2Closure.retainedRow
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms
        (OmegaBound.ADVXXZT6Round82.sideIndex W) =
      ordinaryDirectionalTotal W / (ordinaryD : ℝ) ^ 4 := by
  rw [retainedRow_eq_sum_addresses32]
  have hpoint : ∀ x : ConstituentTerm releasedParent,
      (OmegaBound.ADVXXZT7SpecialInventory.dataById
        (releasedTermNode32 x)).toTerm.retained
          (OmegaBound.ADVXXZT6Round82.sideIndex W) =
        if OrdinaryStageActive x then
          ((releasedConstituentSpec.outBase x : ℝ) / (ordinaryD : ℝ) ^ 4) *
            releasedAddressRate32 x W
        else 0 := by
    intro x
    rw [released_term_retained32 x W]
    by_cases h : OrdinaryStageActive x
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := OrdinaryStageActive)
    (F := (inferInstance : Fintype ReleasedOrdinaryOccurrence))
    (Finset.univ.filter OrdinaryStageActive)
    (fun x => by simp) (fun x => ((releasedConstituentSpec.outBase x : ℝ) /
      (ordinaryD : ℝ) ^ 4) * releasedAddressRate32 x W)]
  rw [← Equiv.sum_comp (Fintype.equivFin ReleasedOrdinaryOccurrence).symm
    (fun y : ReleasedOrdinaryOccurrence =>
      ((releasedConstituentSpec.outBase y.1 : ℝ) / (ordinaryD : ℝ) ^ 4) *
        releasedAddressRate32 y.1 W)]
  unfold ordinaryDirectionalTotal
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hb : (releasedOrdinaryParent.baseN t : ℝ)
      = (releasedConstituentSpec.outBase (ordinaryOccurrence t).1 : ℝ) := rfl
  rw [show ((Fintype.equivFin ReleasedOrdinaryOccurrence).symm t) = ordinaryOccurrence t from rfl,
    releasedAddressRate_eq_ordinary112Nats32 t W, hb]
  ring

end OmegaBound.ADVXXZGeneral
end

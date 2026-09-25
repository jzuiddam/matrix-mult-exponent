import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensusCounts

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 3000

theorem releasedConstituentTerm_card_eq_count :
    Fintype.card (ConstituentTerm releasedParent) = releasedConstituentTermCount := by
  have hc (t : Fin 126) :
      Fintype.card (ChildShape releasedParent t) =
        (OmegaBound.ADVXXZT2.parKids t.val).length := by
    simpa [releasedParent] using
      OmegaBound.ADVXXZT6Round78.releasedChildCardinality t
  change Fintype.card ((t : Fin 126) × Fin 6 × ChildShape releasedParent t) =
    releasedConstituentTermCount
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, Fintype.card_fin, hc]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := 6) (n := 21))
    (fun t : Fin 126 => 6 * (OmegaBound.ADVXXZT2.parKids t.val).length)]
  rw [Fintype.sum_prod_type]
  calc
    (∑ b : Fin 6, ∑ j : Fin 21,
        6 * (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv (b, j)).val).length) =
        ∑ b : Fin 6, 6 * (∑ j : Fin 21,
          (OmegaBound.ADVXXZT2.parKids (finProdFinEquiv (b, j)).val).length) := by
      apply Finset.sum_congr rfl
      intro b _
      exact (Finset.mul_sum ..).symm
    _ = releasedConstituentTermCount := by
      unfold releasedConstituentTermCount releasedConstituentFirstHalfCount
        releasedConstituentSecondHalfCount releasedConstituentBlockCount
      rw [sum_fin_six]
      ac_rfl

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZT6Round61AnalyticBase
import OmegaBound.ADVXXZT6Round26CountingSpine

set_option maxRecDepth 100000
set_option linter.style.longLine false

open Finset

namespace OmegaBound.ADVXXZT6Round61

theorem releasedParentPart_card_eq_sum_firstMultiplicity
    (r : Fin 6) (m : Nat) (p : Fin 126) :
    (ADVXXZT6Round21.releasedParentPart r m p).card =
      ∑ d : Fin (ADVXXZT2.parKids p.1).length,
        ADVXXZT6Selection.firstMultiplicity r m p d := by
  classical
  unfold ADVXXZT6Round21.releasedParentPart ADVXXZT6Round21.partOfOn
  rw [Finset.card_filter]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp_rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp only [Finset.sum_boole, Finset.filter_eq', Finset.mem_univ, true_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_id]
  rw [Finset.sum_eq_single p]
  · simp
  · intro p' _ hp
    simp [hp]
  · simp


end OmegaBound.ADVXXZT6Round61

import OmegaBound.ADVXXZGeneralRowsSemanticCore30

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT6Round130
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000

theorem semantic_parent_le_paper_X30 (dual : DualQ130f) (p : Fin 126)
    (r : Fin 6) :
    (releasedCertificate.D ^ 2 : ℝ) *
        semanticQuantity130f dual p r (roleIndex30 .X) ≤
      Real.log 2 * paperParent30 p r .X := by
  let d := releasedConstituentSpec.toPaper
  let weight : ℝ := d.A p r * (releasedParent.baseN p : ℝ)
  have hw : 0 ≤ weight := mul_nonneg
    ((releasedConstituentSpec.A p).probR_nonneg r) (Nat.cast_nonneg _)
  have halpha : IsProbability (d.alpha p r) :=
    ⟨(releasedConstituentSpec.alpha p r).probR_nonneg,
      (releasedConstituentSpec.alpha p r).sum_probR⟩
  have hx := log_two_mul_constituentPenalty_le_fenchel130 d p r halpha
    (dual.lambdaSum : ℝ) (dualMarginReal130f dual)
  have hscale (E : ℝ) :
      (releasedCertificate.D ^ 2 : ℝ) * ((coefficientQ130f r p : ℝ) * E) =
        weight * E :=
    (mul_assoc _ _ _).symm.trans
      (congrArg (fun c : ℝ => c * E) (coefficient_scale30 r p))
  dsimp only [roleIndex30, semanticQuantity130f]
  rw [hscale]
  rw [released_role_projection30, released_marginal_projection30,
    released_alpha_projection30]
  change weight *
    (OmegaBound.Entropy.H Finset.univ
        (constituentMarginal d p r (d.perm r .X)) +
      OmegaBound.Entropy.H Finset.univ (d.alpha p r) -
      constituentFenchelUpper130 p (d.alpha p r) (dual.lambdaSum : ℝ)
        (dualMarginReal130f dual)) ≤
    Real.log 2 * (weight *
      (entropy (constituentMarginal d p r (d.perm r .X)) -
        constituentPenalty d p r))
  have hm : OmegaBound.Entropy.H Finset.univ
      (constituentMarginal d p r (d.perm r .X)) =
      Real.log 2 * entropy (constituentMarginal d p r (d.perm r .X)) := by
    exact (OmegaBound.Entropy.H_mul_log_two Finset.univ _).symm.trans
      (mul_comm _ _)
  rw [hm]
  calc
    weight * (Real.log 2 * entropy (constituentMarginal d p r (d.perm r .X)) +
        OmegaBound.Entropy.H Finset.univ (d.alpha p r) -
        constituentFenchelUpper130 p (d.alpha p r) (dual.lambdaSum : ℝ)
          (dualMarginReal130f dual)) ≤
      weight * (Real.log 2 *
        (entropy (constituentMarginal d p r (d.perm r .X)) -
          constituentPenalty d p r)) := by
            apply mul_le_mul_of_nonneg_left _ hw
            linarith only [hx]
    _ = _ := by ring

end OmegaBound.ADVXXZGeneral

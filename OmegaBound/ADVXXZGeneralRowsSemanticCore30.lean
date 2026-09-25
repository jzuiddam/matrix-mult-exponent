import OmegaBound.ADVXXZGeneralRowsSemanticProjection30
import OmegaBound.ADVXXZT6Round61ReleasedCountProbe

open scoped BigOperators
open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000

def roleIndex30 : Side → Fin 3
  | .X => 0
  | .Y => 1
  | .Z => 2


noncomputable def paperRow30 (r : Fin 6) (W : Side) : ℝ :=
  let d := releasedConstituentSpec.toPaper
  match W with
  | .X => constituentRowX d r (d.perm r .X)
  | .Y => constituentRowY d r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
  | .Z => constituentRowZ d r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)


noncomputable def paperParent30 (p : Fin 126) (r : Fin 6) (W : Side) : ℝ :=
  let d := releasedConstituentSpec.toPaper
  d.A p r * (releasedParent.baseN p : ℝ) *
    match W with
    | .X => entropy (constituentMarginal d p r (d.perm r .X)) -
        constituentPenalty d p r
    | .Y => splitEntropy (d.betaRegion (d.perm r .Y) p r) -
        constituentEta d p r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)
    | .Z => splitEntropy (d.betaRegion (d.perm r .Z) p r) -
        constituentLambda d p r (d.perm r .X) (d.perm r .Y) (d.perm r .Z)

def PaperSemanticParentBound30 : Prop :=
  ∀ (dual : DualQ130f) (p : Fin 126) (r : Fin 6) (W : Side),
    (releasedCertificate.D ^ 2 : ℝ) *
        semanticQuantity130f dual p r (roleIndex30 W) ≤
      Real.log 2 * paperParent30 p r W

theorem coefficient_scale30 (r : Fin 6) (p : Fin 126) :
    (releasedCertificate.D ^ 2 : ℝ) * (coefficientQ130f r p : ℝ) =
      releasedConstituentSpec.toPaper.A p r * (releasedParent.baseN p : ℝ) := by
  have hsum : (∑ d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length,
      (OmegaBound.ADVXXZT2.chNums p.val r.val).getD d.val 0) =
      OmegaBound.ADVXXZT2.certDen :=
    (OmegaBound.ADVXXZT6Round82.releasedChildRowDist p r).sum_num
  have hcard : (OmegaBound.ADVXXZT6Round21.releasedParentPart r 1 p).card =
      OmegaBound.ADVXXZT6Selection.parentMass p *
      (OmegaBound.ADVXXZT2.regNums p.val).getD r.val 0 *
        OmegaBound.ADVXXZT2.certDen := by
    rw [OmegaBound.ADVXXZT6Round61.releasedParentPart_card_eq_sum_firstMultiplicity]
    simp only [OmegaBound.ADVXXZT6Selection.firstMultiplicity, mul_one,
      ← Finset.mul_sum, hsum]
  have hD : (OmegaBound.ADVXXZT2.certDen : ℝ) ≠ 0 := by
    exact_mod_cast (show OmegaBound.ADVXXZT2.certDen ≠ 0 by decide +kernel)
  change (OmegaBound.ADVXXZT2.certDen : ℝ) ^ 2 *
    (((OmegaBound.ADVXXZT6Round21.releasedParentPart r 1 p).card /
      (OmegaBound.ADVXXZT2.certDen : ℚ) ^ 4 : ℚ) : ℝ) =
    ((OmegaBound.ADVXXZT2.regNums p.val).getD r.val 0 : ℝ) /
      (OmegaBound.ADVXXZT2.certDen : ℝ) *
        (OmegaBound.ADVXXZT6Selection.parentMass p : ℝ)
  rw [hcard]
  push_cast
  field_simp
  <;> ring

theorem paperRow_eq_sum30 (r : Fin 6) (W : Side) :
    paperRow30 r W = ∑ p, paperParent30 p r W := by
  cases W <;> rfl

end OmegaBound.ADVXXZGeneral

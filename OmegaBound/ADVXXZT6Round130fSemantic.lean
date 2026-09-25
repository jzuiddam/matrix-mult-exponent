import OmegaBound.ADVXXZT6Round130fEvaluator
import OmegaBound.ADVXXZT6Round130YZSemanticBase
import OmegaBound.ADVXXZT6Round82Clauses

/-! # Semantic evaluator over the released finite tables -/

set_option maxRecDepth 1000000
set_library_suggestions Lean.LibrarySuggestions.empty

open Finset

namespace OmegaBound.ADVXXZT6Round130f

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZCertRegionalSemantic (physicalSide)

def physicalRole130f (r : Fin 6) (W : Side) : Side :=
  OmegaBound.ADVXXZT3.paperSide (physicalSide r W)

def sumQFin130f {n : Nat} (f : Fin n → ℚ) : ℚ :=
  (List.ofFn f).sum

def coefficientQ130f (r : Fin 6) (p : Fin 126) : ℚ :=
  (OmegaBound.ADVXXZT6Round21.releasedParentPart r 1 p).card /
    ((OmegaBound.ADVXXZT2.certDen : ℚ) ^ 4)

def childQ130f (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) : ℚ :=
  probQ130f (OmegaBound.ADVXXZT6Round82.releasedChildRowDist p r) d

def symQ130f (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) : ℚ :=
  childQ130f p r d + childQ130f p r (Fin.rev d)

def betaChildQ130f (W : Side) (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) (i : Fin 9) : ℚ :=
  probQ130f (OmegaBound.ADVXXZT6Round82.certificateBetaChildAt W p r d)
    (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm i)

def betaRegionQ130f (W : Side) (p : Fin 126) (r : Fin 6) (i : Fin 81) : ℚ :=
  probQ130f (OmegaBound.ADVXXZT6Round82.certificateBetaRegion W p r)
    (OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm i)

def marginalQ130f (W : Side) (p : Fin 126) (r : Fin 6) (a : Fin 5) : ℚ :=
  sumQFin130f fun d =>
    if OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d W = a
    then childQ130f p r d else 0

def etaSelected130f (p : Fin 126) (ySide zSide : Side)
    (a : Fin 5) (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) : Bool :=
  decide (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d ySide = a ∧
    0 < (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d zSide).val)

def lambdaSelected130f (p : Fin 126) (xSide ySide zSide : Side)
    (a : Fin 5) (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) : Bool :=
  decide (0 < (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d xSide).val ∧
    0 < (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d ySide).val ∧
    OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d zSide = a)

def selectedMassQ130f (p : Fin 126) (r : Fin 6)
    (selected : Fin (OmegaBound.ADVXXZT2.parKids p.val).length → Bool) : ℚ :=
  sumQFin130f fun d => if selected d then symQ130f p r d else 0

def selectedBetaQ130f (W : Side) (p : Fin 126) (r : Fin 6)
    (selected : Fin (OmegaBound.ADVXXZT2.parKids p.val).length → Bool)
    (i : Fin 9) : ℚ :=
  (sumQFin130f fun d =>
      if selected d then symQ130f p r d * betaChildQ130f W p r d i else 0) /
    selectedMassQ130f p r selected

def etaQ130f (p : Fin 126) (r : Fin 6) (_xSide ySide zSide : Side) : LinearQ130f :=
  add130f
    (sumFin130f fun d =>
      if (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d zSide).val = 0 then
        scale130f (symQ130f p r d) (entropyFin130f (betaChildQ130f ySide p r d))
      else zero130f)
    (sumFin130f fun a : Fin 5 =>
      let selected := etaSelected130f p ySide zSide a
      scale130f (selectedMassQ130f p r selected)
        (entropyFin130f (selectedBetaQ130f ySide p r selected)))

def lambdaQ130f (p : Fin 126) (r : Fin 6) (xSide ySide zSide : Side) : LinearQ130f :=
  add130f
    (sumFin130f fun d =>
      if (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d xSide).val = 0 ∨
          (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d ySide).val = 0 then
        scale130f (symQ130f p r d) (entropyFin130f (betaChildQ130f zSide p r d))
      else zero130f)
    (sumFin130f fun a : Fin 5 =>
      let selected := lambdaSelected130f p xSide ySide zSide a
      scale130f (selectedMassQ130f p r selected)
        (entropyFin130f (selectedBetaQ130f zSide p r selected)))

def dualLinearQ130f (dual : DualQ130f) (p : Fin 126)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) : ℚ :=
  dual.lambdaSum +
    dual.lambdaMargin 0 (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d .X) +
    dual.lambdaMargin 1 (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d .Y) +
    dual.lambdaMargin 2 (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d .Z)

def fenchelQ130f (dual : DualQ130f) (p : Fin 126) (r : Fin 6) : LinearQ130f :=
  sub130f
    (expSumFin130f fun d => dualLinearQ130f dual p d - 1)
    (pure130f (sumQFin130f fun d => childQ130f p r d * dualLinearQ130f dual p d))

def xQ130f (dual : DualQ130f) (p : Fin 126) (r : Fin 6) (xSide : Side) : LinearQ130f :=
  scale130f dual.coefficient
    (sub130f
      (add130f (entropyFin130f (marginalQ130f xSide p r))
        (entropyFin130f (childQ130f p r)))
      (fenchelQ130f dual p r))

def yQ130f (coefficient : ℚ) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) : LinearQ130f :=
  scale130f coefficient
    (sub130f (entropyFin130f (betaRegionQ130f ySide p r))
      (etaQ130f p r xSide ySide zSide))

def zQ130f (coefficient : ℚ) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) : LinearQ130f :=
  scale130f coefficient
    (sub130f (entropyFin130f (betaRegionQ130f zSide p r))
      (lambdaQ130f p r xSide ySide zSide))

/-- The three exact semantic expressions in logical paper role order. -/
def semanticRowQ130f (dual : DualQ130f) (p : Fin 126) (r : Fin 6) (role : Fin 3) :
    LinearQ130f :=
  let xSide := physicalRole130f r .X
  let ySide := physicalRole130f r .Y
  let zSide := physicalRole130f r .Z
  match role.val with
  | 0 => xQ130f dual p r xSide
  | 1 => yQ130f dual.coefficient p r xSide ySide zSide
  | _ => zQ130f dual.coefficient p r xSide ySide zSide

end OmegaBound.ADVXXZT6Round130f

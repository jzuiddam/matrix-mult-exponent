import OmegaBound.ADVXXZGeneralRowsBridgeCandidateA30
import OmegaBound.ADVXXZT6Round130fDualR0

set_option linter.style.longLine false

open Finset
open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

def betaRegionLeftIndex30 (i : Fin 81) : Fin 9 :=
  OmegaBound.ADVXXZT6SplitTargetData.wordEquiv
    (OmegaBound.ADVXXZPaper.leftHalf
      (OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm i))

def betaRegionRightIndex30 (i : Fin 81) : Fin 9 :=
  OmegaBound.ADVXXZT6SplitTargetData.wordEquiv
    (OmegaBound.ADVXXZPaper.rightHalf
      (OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm i))

/-! Symbolic mixture elimination.  This is proved once and exposes a regional
beta law solely through the small child mass and child profile leaves. -/
set_option maxRecDepth 1000000 in
theorem betaRegionQ130f_eq_child_profiles30
    (W : Side) (p : Fin 126) (r : Fin 6) (i : Fin 81) :
    betaRegionQ130f W p r i =
      sumQFin130f fun d =>
        childQ130f p r d *
          betaChildQ130f W p r d (betaRegionLeftIndex30 i) *
          betaChildQ130f W p r (Fin.rev d) (betaRegionRightIndex30 i) := by
  apply (Rat.cast_injective : Function.Injective ((↑·) : ℚ → ℝ))
  unfold betaRegionQ130f
  rw [probQ130f_cast]
  rw [OmegaBound.ADVXXZT6Round82.certificateBetaRegion,
    OmegaBound.ADVXXZT6Round82.mix_probR]
  rw [sumQFin130f_cast]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [OmegaBound.ADVXXZT6Round82.certificateChildProductAt,
    OmegaBound.ADVXXZT6Round82.concat_probR]
  simp only [Rat.cast_mul, childQ130f, betaChildQ130f]
  rw [probQ130f_cast, probQ130f_cast, probQ130f_cast]
  simp [betaRegionLeftIndex30, betaRegionRightIndex30]
  ring

def r0yP001ChildProfileQ30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : ℚ :=
  match d.1 with
  | 0 => (7590335027579909 : ℚ) / 1152921504606846976
  | 1 => (2887005411041799 : ℚ) / 9007199254740992
  | 2 => (3114589684953723 : ℚ) / 18014398509481984
  | 3 => (6229178325611777 : ℚ) / 36028797018963968
  | 4 => (184768363767918143 : ℚ) / 576460752303423488
  | _ => (7590303173465373 : ℚ) / 1152921504606846976

set_option maxRecDepth 1000000 in
theorem r0yP001_childQ_profile30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    childQ130f 1 0 d = r0yP001ChildProfileQ30 d := by
  fin_cases d <;> decide +kernel

def r0yP001LevelProfile30
    (W : Side) (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : Fin 5 :=
  match W, d.1 with
  | .X, 0 | .X, 1 | .X, 2 => 0
  | .X, _ => 1
  | .Y, 0 | .Y, 3 => 0
  | .Y, 1 | .Y, 4 => 1
  | .Y, _ => 2
  | .Z, 0 => 4
  | .Z, 1 | .Z, 3 => 3
  | .Z, 2 | .Z, 4 => 2
  | .Z, _ => 1

set_option maxRecDepth 1000000 in
theorem r0yP001_level_profile30
    (W : Side) (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    OmegaBound.ADVXXZT6Round130.releasedKidLevel130 1 d W =
      r0yP001LevelProfile30 W d := by
  fin_cases W <;> fin_cases d <;> rfl

def r0yP001CoefficientProfileQ30 : ℚ :=
  (13470550719950447558896341882715 : ℚ) /
    20769187434139310514121985316880384

theorem r0yP001_coefficient_profile30 :
    (dualQ130fR0 1).coefficient = r0yP001CoefficientProfileQ30 := by
  rfl

def r0yP001SymProfileQ30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : ℚ :=
  r0yP001ChildProfileQ30 d + r0yP001ChildProfileQ30 (Fin.rev d)

def r0yP001BetaRegionProfileQ30 (i : Fin 81) : ℚ :=
  sumQFin130f fun d =>
    r0yP001ChildProfileQ30 d *
      targetNodeBetaProfileQ30 (r0yP001Node30 d) .Y (betaRegionLeftIndex30 i) *
      targetNodeBetaProfileQ30 (r0yP001Node30 (Fin.rev d)) .Y
        (betaRegionRightIndex30 i)

def r0yP001EtaSelectedProfile30
    (a : Fin 5) (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : Bool :=
  decide (r0yP001LevelProfile30 .Y d = a ∧
    0 < (r0yP001LevelProfile30 .Z d).val)

def r0yP001SelectedMassProfileQ30
    (selected : Fin (OmegaBound.ADVXXZT2.parKids 1).length → Bool) : ℚ :=
  sumQFin130f fun d => if selected d then r0yP001SymProfileQ30 d else 0

def r0yP001SelectedBetaProfileQ30
    (selected : Fin (OmegaBound.ADVXXZT2.parKids 1).length → Bool)
    (i : Fin 9) : ℚ :=
  (sumQFin130f fun d =>
      if selected d then r0yP001SymProfileQ30 d *
        targetNodeBetaProfileQ30 (r0yP001Node30 d) .Y i else 0) /
    r0yP001SelectedMassProfileQ30 selected

def r0yP001EtaProfile30 : LinearQ130f :=
  add130f
    (sumFin130f fun d =>
      if (r0yP001LevelProfile30 .Z d).val = 0 then
        scale130f (r0yP001SymProfileQ30 d)
          (entropyFin130f (targetNodeBetaProfileQ30 (r0yP001Node30 d) .Y))
      else zero130f)
    (sumFin130f fun a : Fin 5 =>
      let selected := r0yP001EtaSelectedProfile30 a
      scale130f (r0yP001SelectedMassProfileQ30 selected)
        (entropyFin130f (r0yP001SelectedBetaProfileQ30 selected)))

def r0yP001ProjectedY30 : LinearQ130f :=
  scale130f r0yP001CoefficientProfileQ30
    (sub130f (entropyFin130f r0yP001BetaRegionProfileQ30)
      r0yP001EtaProfile30)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem r0yP001_semantic_eq_projected30 :
    semanticRowQ130f (dualQ130fR0 1) 1 0 1 = r0yP001ProjectedY30 := by
  have hregion : betaRegionQ130f .Y 1 0 = r0yP001BetaRegionProfileQ30 := by
    funext i
    rw [betaRegionQ130f_eq_child_profiles30]
    simp_rw [r0yP001_childQ_profile30, r0yP001_betaChild_profile30]
    rfl
  change yQ130f (dualQ130fR0 1).coefficient 1 0 .X .Y .Z = _
  unfold yQ130f r0yP001ProjectedY30
  rw [r0yP001_coefficient_profile30]
  rw [hregion]
  unfold etaQ130f etaSelected130f selectedBetaQ130f selectedMassQ130f symQ130f
    r0yP001EtaProfile30 r0yP001EtaSelectedProfile30
    r0yP001SelectedBetaProfileQ30 r0yP001SelectedMassProfileQ30
    r0yP001SymProfileQ30
  simp_rw [r0yP001_childQ_profile30, r0yP001_betaChild_profile30,
    r0yP001_level_profile30]
  rfl

#print axioms betaRegionQ130f_eq_child_profiles30
#print axioms r0yP001_semantic_eq_projected30

end OmegaBound.ADVXXZGeneral

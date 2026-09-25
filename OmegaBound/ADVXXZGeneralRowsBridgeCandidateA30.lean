import OmegaBound.ADVXXZGeneralRowsSource30Projections
import OmegaBound.ADVXXZT6Round130fSemantic

set_option linter.style.longLine false

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT6Round130f

namespace OmegaBound.ADVXXZGeneral

open OmegaBound.ADVXXZT6SplitTargetData
open Source30Projections

/-! A single five-kind profile: `TargetNode.baseNum` is the explicit exhaustive
profile for `k022`, `k112`, `k013`, `k031`, and `k004`. -/
def targetNodeBetaProfileQ30 (data : TargetNode) (W : Side) (i : Fin 9) : ℚ :=
  ((data.raw (OmegaBound.ADVXXZT6Round82.sideIndex W)).nums i : ℚ) / targetDen

set_option maxRecDepth 1000000 in
theorem betaChildQ130f_eq_targetNodeProfile30
    (W : Side) (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.1).length)
    (data : TargetNode)
    (hraw : OmegaBound.ADVXXZT6Round82.releasedChildRawAt W p r d =
      data.raw (OmegaBound.ADVXXZT6Round82.sideIndex W)) :
    betaChildQ130f W p r d = targetNodeBetaProfileQ30 data W := by
  funext i
  unfold betaChildQ130f probQ130f
  unfold OmegaBound.ADVXXZT6Round82.certificateBetaChildAt
  simp only [OmegaBound.ADVXXZT6SplitTargetData.RawTarget.toDist,
    OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.apply_symm_apply]
  rw [congrArg (fun raw => raw.nums i) hraw,
    congrArg (fun raw => raw.den) hraw]
  rfl

set_option maxRecDepth 1000000 in
private theorem leftOcc_eq_level3Incidence_get_p001_30
    (i : OmegaBound.ADVXXZT2.Occ)
    (hlen : OmegaBound.ADVXXZCertSemantic.level3Incidence.length = 5508) :
    OmegaBound.ADVXXZT2.leftOcc i =
      (OmegaBound.ADVXXZCertSemantic.level3Incidence.get
        ⟨i.1, by rw [hlen]; exact i.isLt⟩).left := by
  rfl

set_option maxRecDepth 1000000 in
private theorem level3Incidence_get_shard00_p001_30 (j : ℕ)
    (hj : j < OmegaBound.ADVXXZCertSemantic.level3Incidence00.length)
    (hall : j < OmegaBound.ADVXXZCertSemantic.level3Incidence.length) :
    OmegaBound.ADVXXZCertSemantic.level3Incidence.get ⟨j, hall⟩ =
      OmegaBound.ADVXXZCertSemantic.level3Incidence00.get ⟨j, hj⟩ := by
  unfold OmegaBound.ADVXXZCertSemantic.level3Incidence
  exact List.getElem_append_left hj

def r0yP001LeftNat30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : ℕ :=
  match d.1 with
  | 0 => 24
  | 1 => 26
  | 2 => 28
  | 3 => 29
  | 4 => 27
  | _ => 25

def r0yP001Left30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    OmegaBound.ADVXXZCertSemantic.Level2TermId :=
  ⟨r0yP001LeftNat30 d, by fin_cases d <;> decide +kernel⟩

def r0yP001Node30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) : TargetNode :=
  match d.1 with
  | 0 => ⟨.k004, 0, 0⟩
  | 1 => ⟨.k013, 0, 0⟩
  | 2 => ⟨.k022, 0, 5521029838364560569925632⟩
  | 3 => ⟨.k031, 2, 0⟩
  | 4 => ⟨.k112, 0, 0⟩
  | _ => ⟨.k112, 1, 2445031678436507979350016⟩

theorem r0yP001_occurrence30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    occurrence 1 0 d = Fin.ofNat 5508 (24 + d.1) := by
  rw [occurrence_eq_projected30]
  apply Fin.ext
  rfl

theorem r0yP001_left30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    OmegaBound.ADVXXZT2.leftOcc (occurrence 1 0 d) =
      r0yP001Left30 d := by
  rw [r0yP001_occurrence30,
    leftOcc_eq_level3Incidence_get_p001_30 _ OmegaBound.ADVXXZT1.inc_length]
  fin_cases d <;>
    rw [level3Incidence_get_shard00_p001_30 (hj := by decide +kernel)] <;> rfl

theorem r0yP001_node30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    targetNodeRows.getD (r0yP001LeftNat30 d) dummyTargetNode =
      r0yP001Node30 d := by
  fin_cases d <;>
    rw [targetNodeRows_getD_shard0_30 (hj := by decide +kernel)] <;> rfl

theorem r0yP001_raw30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    OmegaBound.ADVXXZT6Round82.releasedChildRawAt .Y 1 0 d =
      (r0yP001Node30 d).raw (OmegaBound.ADVXXZT6Round82.sideIndex .Y) := by
  apply releasedChildRawAt_eq_explicit30 .Y 1 0 d
    (Fin.ofNat 5508 (24 + d.1))
    (r0yP001Left30 d)
    (r0yP001Node30 d)
  · exact r0yP001_occurrence30 d
  · exact r0yP001_left30 d
  · exact r0yP001_node30 d

theorem r0yP001_betaChild_profile30
    (d : Fin (OmegaBound.ADVXXZT2.parKids 1).length) :
    betaChildQ130f .Y 1 0 d = targetNodeBetaProfileQ30 (r0yP001Node30 d) .Y :=
  betaChildQ130f_eq_targetNodeProfile30 .Y 1 0 d _ (r0yP001_raw30 d)

#print axioms betaChildQ130f_eq_targetNodeProfile30
#print axioms r0yP001_betaChild_profile30

end OmegaBound.ADVXXZGeneral

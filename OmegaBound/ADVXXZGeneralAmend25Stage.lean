import OmegaBound.ADVXXZGeneralAmend25Parent
import OmegaBound.ADVXXZGeneralStageDefinitionsV22
import OmegaBound.ADVXXZGeneralAmend25Population
set_option autoImplicit false
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
noncomputable def stagePartKeepAt25 {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (step : DeletionStep) (W : Side)
    (a : (stagePopulationAt q p d b m r).Part W) : Prop := by
  classical
  let P := stagePopulationAt q p d b m r
  let S := selected (rolePopulation P (d.perm r)) M B ω
  let matching := S.filter fun j => Parent25.containsSide p d b m r W j a
  let C := fun which : Fin 2 => matching.filter fun j => Parent25.compatible p d b m r which j a
  let hInput := Parent25.inputPartKeep p d b m ε r W a
  let hHash := matching.Nonempty
  let hX := W = d.perm r .X → ∃ j ∈ matching, P.incidence W j a
  let hYC := W = d.perm r .Y → (C 0).Nonempty
  let hYU := W = d.perm r .Y → (C 0).card = 1
  let hYF := W = d.perm r .Y → ∃ j ∈ C 0, P.incidence W j a
  let hZC := W = d.perm r .Z → (C 1).Nonempty
  let hZU := W = d.perm r .Z → (C 1).card = 1
  let hZF := W = d.perm r .Z → ∃ j ∈ C 1, P.incidence W j a
  exact match step with
  | .input => hInput
  | .hash => hInput ∧ hHash
  | .xExact => hInput ∧ hHash ∧ hX
  | .yCompat => hInput ∧ hHash ∧ hX ∧ hYC
  | .yUnique => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU
  | .yUseful => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF
  | .zCompat => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC
  | .zUnique => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU
  | .zUseful => hInput ∧ hHash ∧ hX ∧ hYC ∧ hYU ∧ hYF ∧ hZC ∧ hZU ∧ hZF

noncomputable def stageKeepAt25 {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (step : DeletionStep) (W : Side) :
    (regionalInputZ q p d (b*m) ε).leg W → Prop :=
  fun x => stagePartKeepAt25 q b m M ε p d r B ω step W
    (stagePartAt q b m ε p d r W x)

noncomputable def holesAt25 {w s : ℕ} (q b m M : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    Finset ((stagePopulationAt q p d b m r).Part W) := by
  classical
  exact (exactPartsAt q b m p d r j W).filter fun a =>
    ¬ stagePartKeepAt25 q b m M ε p d r B ω .zUseful W a

noncomputable def stageGood25 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6)
    (M : ℕ) (B : Finset (ZMod M))
    (ω : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) : Prop :=
  j ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B ω ∧
    ∀ W : Side,
      4 * (stagePopulationAt q p d b m r).n *
        (holesAt25 q b m M ε p d r B ω j W).card ≤
          (exactPartsAt q b m p d r j W).card


end
end OmegaBound.ADVXXZGeneral


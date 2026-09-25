import OmegaBound.ADVXXZGeneralInputCellAggregation
import OmegaBound.ADVXXZGeneralInputTransportCont3
import OmegaBound.ADVXXZGeneralPProjectionParent25

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The public input density is the bad-event proportion on the exact-part
subtype used by the moment argument. -/
theorem inputDensity_eq_exactPart_bad_ratio {w s : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (b : ℕ) (ε : ℚ)
    (m : ℕ) {r : Fin 6} (J : AlphaLabel p d b m r) (W : Side) :
    InputDensity q p d b ε m J W =
      ((Finset.univ.filter fun a : StageExactPart27 0 b m p d r J.val W =>
        ¬ Parent25.inputPartKeep p d b m ε r W a.val).card : ℝ) /
        Fintype.card (StageExactPart27 0 b m p d r J.val W) := by
  rw [inputDensity_eq_parent25_filter]
  dsimp only
  let S := exactPartsAt 0 b m p d r J.val W
  let bad : (stagePopulationAt 0 p d b m r).Part W → Prop := fun a =>
    ¬ Parent25.inputPartKeep p d b m ε r W a
  let Ω := StageExactPart27 0 b m p d r J.val W
  let E : {a : Ω // bad a.val} ≃ ↥(S.filter bad) :=
    { toFun := fun a => ⟨a.val.val,
        Finset.mem_filter.mpr ⟨a.val.property,a.property⟩⟩
      invFun := fun a => ⟨⟨a.val,(Finset.mem_filter.mp a.property).1⟩,
        (Finset.mem_filter.mp a.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hnum : (S.filter bad).card =
      (Finset.univ.filter fun a : Ω => bad a.val).card := by
    calc
      (S.filter bad).card = Fintype.card ↥(S.filter bad) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card {a : Ω // bad a.val} := (Fintype.card_congr E).symm
      _ = (Finset.univ.filter fun a : Ω => bad a.val).card := by
        rw [Fintype.card_subtype]
  have hden : S.card = Fintype.card Ω := by
    exact (Fintype.card_coe S).symm
  change ((S.filter bad).card : ℝ) / S.card = _
  rw [hnum,hden]

end
end OmegaBound.ADVXXZGeneral
end

import OmegaBound.ADVXXZGeneralAmend29CExact
import OmegaBound.ADVXXZGeneralInputDensityBridge
import OmegaBound.ADVXXZGeneralGridInput29TwinInputKeepBound

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

/-- Input concentration uniformly over every empirical grid,
with its constant and threshold chosen before the scale and the grid. -/
theorem constituent_grid_input_concentration29 (q w s b : ℕ) (hq : 0 < q)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) :
  ∀ ε : ℚ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ,
    ∀ m, M ≤ m → ∀ (h : ConstituentExactGrid27 d m) (r : Fin 6)
      (J : AlphaLabel (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r) (W : Side),
      constituentGridInputDensity29 q d hd ε m h r J W ≤ C / (b*m : ℝ)^2 := by
  intro ε hε
  obtain ⟨Cinput,hCinput,hinput⟩ :=
    Grid29.inputExactPart_not_keep_bound (w := w) (s := s) ε hε
  have hbpos : 0 < b := hb.1
  let C : ℝ := Cinput * (b : ℝ)^2
  refine ⟨C, by dsimp [C]; positivity, 2, ?_⟩
  intro m hm h r J W
  unfold constituentGridInputDensity29
  rw [inputDensity_eq_exactPart_bad_ratio]
  have hbound := hinput
    (constituentGridParent27 d hd m h)
    (constituentGridSpec27 d hd m h)
    (gridInputAdm29 d hd m h)
    (gridInputInt29 d hd hb m h) hm r J W
  apply hbound.trans_eq
  dsimp [C]
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  field_simp

end
end OmegaBound.ADVXXZGeneral
end

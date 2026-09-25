import OmegaBound.ADVXXZGeneralRates
import OmegaBound.ADVXXZGeneralCertInventory

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

instance instFintypeStage (top : ℕ) : Fintype (Stage top) :=
  Fintype.ofFinset (Finset.Icc 2 top) (by
    intro l
    change l ∈ Finset.Icc 2 top ↔ 2 ≤ l ∧ l ≤ top
    exact Finset.mem_Icc)

noncomputable def cLength {w s : ℕ} (p : ConstituentInput w s) (b m : ℕ) : ℕ :=
  constituentBaseTotal p * (b * m)

noncomputable def derivedRetainedRate (C : Certificate) : ℝ :=
  gRate C.global + ∑ l : Stage C.top,
    match C.stage l with
    | none => 0
    | some d => cRate d.data * (constituentBaseTotal d.input : ℝ) / (C.D : ℝ)^2

end OmegaBound.ADVXXZGeneral
end

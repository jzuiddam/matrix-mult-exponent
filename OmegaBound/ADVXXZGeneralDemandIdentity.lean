import OmegaBound.ADVXXZGeneralRates

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

theorem alpha_sub_demand_min (H X Y Z : ℝ) :
  H-max (H-X) (max (H-Y) (H-Z)) = min X (min Y Z) := by
  have sub_max' (a b d : ℝ) : a - max b d = min (a - b) (a - d) := by
    rcases le_total b d with h | h
    · rw [max_eq_right h, min_eq_right (by linarith)]
    · rw [max_eq_left h, min_eq_left (by linarith)]
  rw [sub_max', sub_max']
  ring

end OmegaBound.ADVXXZGeneral
end

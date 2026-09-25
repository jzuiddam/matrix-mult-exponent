import OmegaBound.ADVXXZGeneralAmend25Parent

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
namespace OmegaBound.ADVXXZGeneral

/-- The left projection of a corrected per-parent paired word is its `W = 0` word. -/
theorem parent25_leftHalf_paired {w s : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {b m : ℕ} {r : Fin 6}
    (a : Parent25.Pos p d b m r → Chunk w) (t : Fin s)
    (i : Fin (Parent25.parentCount p d b m r t)) :
    leftHalf (Parent25.paired a t i) = a ⟨t, i, 0⟩ := by
  funext c
  simp only [leftHalf, Parent25.paired]
  split
  · rfl
  · omega

/-- The right projection of a corrected per-parent paired word is its `W = 1` word. -/
theorem parent25_rightHalf_paired {w s : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {b m : ℕ} {r : Fin 6}
    (a : Parent25.Pos p d b m r → Chunk w) (t : Fin s)
    (i : Fin (Parent25.parentCount p d b m r t)) :
    rightHalf (Parent25.paired a t i) = a ⟨t, i, 1⟩ := by
  funext c
  simp only [rightHalf, Parent25.paired]
  split
  · omega
  · congr 3
    exact Nat.add_sub_cancel_left w c

end OmegaBound.ADVXXZGeneral
end

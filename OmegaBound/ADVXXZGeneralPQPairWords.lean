import OmegaBound.ADVXXZGeneralPProjectionParent25

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
namespace OmegaBound.ADVXXZGeneral

private def parent25Unpair {w s b m : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {r : Fin 6}
    (x : (t : Fin s) → Fin (Parent25.parentCount p d b m r t) → Chunk (w+w))
    (z : Parent25.Pos p d b m r) : Chunk w :=
  Fin.cases (leftHalf (x z.1 z.2.1)) (fun _ => rightHalf (x z.1 z.2.1)) z.2.2

/-- A word on the corrected sigma-position carrier is exactly a parent-indexed family of
paired words. -/
def parent25PairWordsEquiv {w s b m : ℕ} {p : ConstituentInput w s}
    {d : ConstituentSpec p} {r : Fin 6} :
    (Parent25.Pos p d b m r → Chunk w) ≃
      ((t : Fin s) → Fin (Parent25.parentCount p d b m r t) → Chunk (w+w)) where
  toFun a t i := Parent25.paired a t i
  invFun := parent25Unpair
  left_inv a := by
    funext z c
    rcases z with ⟨t, i, h⟩
    fin_cases h
    · simp only [parent25Unpair, Fin.cases_zero]
      exact congrFun (parent25_leftHalf_paired a t i) c
    · simp only [parent25Unpair, Fin.cases_succ]
      exact congrFun (parent25_rightHalf_paired a t i) c
  right_inv x := by
    funext t i c
    by_cases hc : c.val < w
    · simp only [Parent25.paired, dif_pos hc, parent25Unpair, Fin.isValue, ↓reduceIte,
        Fin.cases_zero, leftHalf]
    · have hw : w + (c.val - w) = c.val := by omega
      simp only [Parent25.paired, dif_neg hc]
      change (rightHalf (x t i)) ⟨c.val - w, by omega⟩ = x t i c
      unfold rightHalf
      rw [show (⟨w + (c.val - w), by omega⟩ : Fin (w+w)) = c by exact Fin.ext hw]

end OmegaBound.ADVXXZGeneral
end

import OmegaBound.ADVXXZSplitIface

/-!
# The point mass at a level-1 word

`ADVXXZCon.deltaDist σ` is the complete split distribution concentrated on the level-1 word `σ`,
in the integrality convention (denominator `1`).  At width `w = 1` every complete split
distribution admitted by the sources' support assumption (`constituent.tex:14-27`,
`global.tex:99-112`) is of this form, since there is exactly one word of each level.
-/

open Finset

namespace OmegaBound

namespace ADVXXZCon

open ADVXXZ (Chunk SplitDist RatDist Consistent ApproxConsistent typeCnt emp approxConsistent_zero_iff)

/-! ## The point mass -/

/-- **The point mass at a level-1 word.**  Under the integrality convention this is the
`RatDist` with denominator `1`.  At width `w = 1` every complete split distribution admitted by
the sources' support assumption is of this form, since there is exactly one word of each level. -/
def deltaDist {w : ℕ} (σ : Chunk w) : SplitDist w where
  num τ := if τ = σ then 1 else 0
  den := 1
  den_pos := Nat.one_pos
  sum_num := by simp

end ADVXXZCon

end OmegaBound

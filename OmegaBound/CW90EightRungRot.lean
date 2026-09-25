import OmegaBound.CW90EightValue
import OmegaBound.ASISum
import OmegaBound.CW90Seven

/-!
# Coppersmith–Winograd 1990, §8: the cyclic rotation of legs

`rotT A y z x = A x y z` permutes the leg types.  A direct sum of matrix products rotates to a
direct sum of matrix products with the same volumes (`dsT_rot`: three commuting indicator
factors), and tensor powers commute with the rotation (`powT_rot`).
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

open CW90

variable {X Y Z : Type}

/-! ## Rotating the legs -/

/-- **The cyclic rotation of the legs**, `x → z`-slot: `rotT A y z x = A x y z`. -/
def rotT (A : Tensor3 ℚ X Y Z) : Tensor3 ℚ Y Z X := fun y z x => A x y z

@[simp] theorem rotT_apply (A : Tensor3 ℚ X Y Z) (y : Y) (z : Z) (x : X) :
    rotT A y z x = A x y z := rfl

/-- A direct sum of matrix multiplication tensors rotates to a direct sum of matrix
multiplication tensors: the three indicator factors of the triangle simply commute. -/
theorem dsT_rot {ι : Type} [DecidableEq ι] (P Q R : ι → Type)
    [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (R i)]
    (x : DIdx P Q) (y : DIdx Q R) (z : DIdx R P) :
    dsT Q R P y z x = dsT P Q R x y z := by
  rw [dsT_apply, dsT_apply]; ring

namespace MMDecomp

variable {A : Tensor3 ℚ X Y Z}

end MMDecomp

/-- Tensor powers commute with the rotation. -/
theorem powT_rot (A : Tensor3 ℚ X Y Z) (n : ℕ) : powT (rotT A) n = rotT (powT A n) := by
  funext b c a
  rw [powT_apply, rotT_apply, powT_apply]
  exact Finset.prod_congr rfl fun _ _ => rfl

end CW90Eight

end OmegaBound

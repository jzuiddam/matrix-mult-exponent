import OmegaBound.CWTri
import OmegaBound.CW90Tensor
import OmegaBound.Schonhage2548Sum

/-!
# Coppersmith–Winograd 1990, §8: `Σ`-indexed direct sums of matrix multiplication tensors

`dsT P Q R` is the direct sum `⊕_{i : ι} ⟨|P i|,|Q i|,|R i|⟩` on the legs `DLeg P`, `DLeg Q`,
`DLeg R`, for an arbitrary index type `ι` with type-valued formats, defined by its triangle
indicator `CW.triInd` (`dsT_apply` unfolds it).  It is the target of the degeneration
decompositions `DDecomp` of `CW90EightValD`.
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

open CW

/-! ## `Σ`-indexed direct sums of matrix multiplication tensors -/

section DSum

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- A leg of a `ι`-indexed direct sum of matrix multiplication tensors. -/
abbrev DLeg (P : ι → Type) : Type := (i : ι) × P i

/-- The `x`-index type of a `ι`-indexed direct sum of matrix multiplication tensors. -/
abbrev DIdx (P Q : ι → Type) : Type := (i : ι) × (P i × Q i)

/-- **The direct sum `⊕_{i : ι} ⟨|P i|, |Q i|, |R i|⟩`**, defined by its triangle
indicator on the legs `Σ P`, `Σ Q`, `Σ R`.  Because the legs remember the summand, an
entry vanishes unless all three indices lie in the same summand. -/
def dsT (P Q R : ι → Type) [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)]
    [∀ i, DecidableEq (R i)] : Tensor3 ℚ (DIdx P Q) (DIdx Q R) (DIdx R P) := fun x y z =>
  triInd ((⟨x.1, x.2.1⟩ : DLeg P), (⟨x.1, x.2.2⟩ : DLeg Q))
    ((⟨y.1, y.2.1⟩ : DLeg Q), (⟨y.1, y.2.2⟩ : DLeg R))
    ((⟨z.1, z.2.1⟩ : DLeg R), (⟨z.1, z.2.2⟩ : DLeg P))

theorem dsT_apply (P Q R : ι → Type) [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)]
    [∀ i, DecidableEq (R i)] (x : DIdx P Q) (y : DIdx Q R) (z : DIdx R P) :
    dsT P Q R x y z
      = (if (⟨x.1, x.2.2⟩ : DLeg Q) = ⟨y.1, y.2.1⟩ then (1 : ℚ) else 0)
        * (if (⟨y.1, y.2.2⟩ : DLeg R) = ⟨z.1, z.2.1⟩ then (1 : ℚ) else 0)
        * (if (⟨z.1, z.2.2⟩ : DLeg P) = ⟨x.1, x.2.1⟩ then (1 : ℚ) else 0) := rfl

end DSum

namespace MMDecomp

variable {X Y Z X' Y' Z' : Type} {A : Tensor3 ℚ X Y Z} {A' : Tensor3 ℚ X' Y' Z'}

end MMDecomp

section Closure

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

end Closure

section Bridge

variable {ι : Type}

end Bridge

namespace MMDecomp

variable {X Y Z : Type} {A : Tensor3 ℚ X Y Z}


end MMDecomp

namespace MMDecomp

variable {X Y Z X' Y' Z' : Type} {A : Tensor3 ℚ X Y Z} {B : Tensor3 ℚ X' Y' Z'}

end MMDecomp

end CW90Eight

end OmegaBound

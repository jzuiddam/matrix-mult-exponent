import OmegaBound.CW90EightDSum
import OmegaBound.ASISum
import OmegaBound.CW90Seven

/-!
# Coppersmith–Winograd 1990, §8: the heterogeneous tensor product

`CW90Eight.piT` is the tensor product of a `Fin m`-indexed family of tensors on different leg
types: the legs are the dependent function types and an entry is the product of the entries.
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

open CW90

section YieldsDBasic

variable {t : ℝ} {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']

end YieldsDBasic

/-! ## The heterogeneous tensor product -/

/-- **The heterogeneous tensor product of a `Fin m`-indexed family of tensors.**  The legs
are the dependent function types; the entry is the product of the entries. -/
def piT {m : ℕ} {X Y Z : Fin m → Type} (A : ∀ i, Tensor3 ℚ (X i) (Y i) (Z i)) :
    Tensor3 ℚ ((i : Fin m) → X i) ((i : Fin m) → Y i) ((i : Fin m) → Z i) :=
  fun x y z => ∏ i, A i (x i) (y i) (z i)

end CW90Eight

end OmegaBound

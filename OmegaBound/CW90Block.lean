import OmegaBound.CW90Tensor
import OmegaBound.Schonhage2548Sum

/-!
# Coppersmith–Winograd 1990, §6: blocks of `T_q^{⊗3N}`

A block of the `3N`-th tensor power of `T_q` (see `OmegaBound.CW90.T`) in which every position
carries exactly one of the three "zero" labels is recorded by an equivalence
`σ : Fin 3 × Fin N ≃ Fin (3 * N)` (`CW90.Blk N`) whose first coordinate is the colour of a
position; `CW90.col σ` is the induced colouring `Fin (3 * N) → Fin 3`.
-/

open Polynomial Finset Tensor3

namespace OmegaBound

namespace CW90

/-! ## Blocks -/

/-- A block of the `3N`-th tensor power of `T q`: an identification of the `3 * N`
coordinate positions with `Fin 3 × Fin N`.  The first coordinate is the *colour* of a
position; colour `t` marks the position as one where the `t`-th of `x, y, z` carries the
block-`[0]` variable. -/
abbrev Blk (N : ℕ) := Fin 3 × Fin N ≃ Fin (3 * N)

/-- The colouring of positions determined by a block. -/
def col {N : ℕ} (σ : Blk N) (p : Fin (3 * N)) : Fin 3 := (σ.symm p).1

variable {q N : ℕ}

variable (q N)

variable {q N}

end CW90

end OmegaBound

import OmegaBound.ASISum
import OmegaBound.CW90Tensor

/-!
# An indicator collapse for triple sums

`indicator_triple_sum`: three indicator rows `[x = x₀]·p₁`, `[y = y₀]·p₂`, `[z = z₀]·p₃` collapse
the triple sum `∑ x y z, … · C (A x y z)` to `p₁ · p₂ · p₃ · C (A x₀ y₀ z₀)`.
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

section BlockStrassen

variable {F : Type*} [Field F]

variable {e h ℓ q : ℕ}

variable {X Y Z : Type}

variable {A : Tensor3 F X Y Z} {bx : X → Fin e × Fin h} {byy : Y → Fin h × Fin ℓ}
  {bz : Z → Fin ℓ × Fin e}

/-! ## The substitution collapses -/

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Three indicator rows collapse the triple sum to a single entry. -/
theorem indicator_triple_sum [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (A : Tensor3 F X Y Z) (x₀ : X) (y₀ : Y) (z₀ : Z) (p₁ p₂ p₃ : Polynomial F) :
    (∑ x : X, ∑ y : Y, ∑ z : Z,
      (if x = x₀ then p₁ else 0) * (if y = y₀ then p₂ else 0) * (if z = z₀ then p₃ else 0)
        * Polynomial.C (A x y z))
      = p₁ * p₂ * p₃ * Polynomial.C (A x₀ y₀ z₀) := by
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

end BlockStrassen

end CW90Eight

end OmegaBound

/-
Copyright (c) 2026 Jeroen Zuiddam.
Released under the Apache License 2.0; see LICENSE.
The identity tensor.
-/
import OmegaBound.Tensor.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The identity tensor

`Tensor3.identity R r`, the identity tensor `I_r` of size `r × r × r`. For its subrank and geometric
rank see [KMZ23].

## References

* [KMZ23] Kopparty, Moshkovitz, Zuiddam. "Geometric Rank of Tensors and Subrank of
  Matrix Multiplication." Discrete Analysis 2023:1.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Tensor3

variable {R : Type*} [CommSemiring R]
variable {α β γ : Type*}

/-! ### The Identity Tensor -/

section Identity

variable (R : Type*) [CommSemiring R]

/-- The identity tensor I_r of size r × r × r.
    I_r(i,j,k) = 1 if i = j = k, else 0 -/
def identity (r : ℕ) : Tensor3 R (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ j = k then 1 else 0

variable {R}

end Identity

end Tensor3

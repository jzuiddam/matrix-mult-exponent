import OmegaBound.CW90EightValue
import OmegaBound.CW90EightStrassen
import OmegaBound.ASISum
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Coppersmith–Winograd 1990, §8: the value with a *degeneration* witness

* `DDecomp A` — a decomposition of `A` witnessed by `Degenerates ℚ A (dsT P Q R)`, with summand
  volumes `DDecomp.vol` and `τ`-weight `DDecomp.wt`.
* `YieldsD t A w` — some such decomposition of `A` has weight at least `w`.
* `HasValD t A v` — `V_τ(A) ≥ v`, witnessed: some power `A^{⊗n}`, `n ≥ 1`, degenerates to a
  `dsT` of `τ`-weight `≥ v^n`.
-/

open Tensor3 Finset

namespace OmegaBound


namespace CW90Eight

open CW90

/-! ## Decompositions witnessed by a degeneration -/

/-- **A decomposition of `A` witnessed by a degeneration.**  The witness `deg` is a degeneration of `A`
onto the direct sum `dsT P Q R`.  This is what the `(d)` term of §8 produces. -/
structure DDecomp {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (A : Tensor3 ℚ X Y Z) : Type 1 where
  /-- The set of summands. -/
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  /-- There is at least one summand. -/
  ne : Nonempty ι
  /-- The first format of each summand. -/
  P : ι → Type
  /-- The second format of each summand. -/
  Q : ι → Type
  /-- The third format of each summand. -/
  R : ι → Type
  [fP : ∀ i, Fintype (P i)]
  [fQ : ∀ i, Fintype (Q i)]
  [fR : ∀ i, Fintype (R i)]
  [dP : ∀ i, DecidableEq (P i)]
  [dQ : ∀ i, DecidableEq (Q i)]
  [dR : ∀ i, DecidableEq (R i)]
  /-- Every summand has volume at least `2`. -/
  big : ∀ i, 2 ≤ Fintype.card (P i) * Fintype.card (Q i) * Fintype.card (R i)
  /-- `A` degenerates to the direct sum. -/
  deg : Degenerates ℚ A (dsT P Q R)

attribute [instance] DDecomp.fι DDecomp.dι DDecomp.fP DDecomp.fQ DDecomp.fR
  DDecomp.dP DDecomp.dQ DDecomp.dR

namespace DDecomp

variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z'] {A : Tensor3 ℚ X Y Z} {A' : Tensor3 ℚ X' Y' Z'}

/-- The volume of the `i`-th summand. -/
def vol (D : DDecomp A) (i : D.ι) : ℕ :=
  Fintype.card (D.P i) * Fintype.card (D.Q i) * Fintype.card (D.R i)

/-- **The `τ`-weight of a decomposition**, `∑_i (|P i||Q i||R i|)^τ`. -/
noncomputable def wt (t : ℝ) (D : DDecomp A) : ℝ := ∑ i : D.ι, ((D.vol i : ℕ) : ℝ) ^ t

end DDecomp

namespace DDecomp

variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z'] {A : Tensor3 ℚ X Y Z} {B : Tensor3 ℚ X' Y' Z'}

end DDecomp

/-! ## The value -/

/-- `YieldsD t A w`: the tensor `A` **degenerates** to a direct sum of matrix multiplication
tensors of total `τ`-weight at least `w`. -/
def YieldsD (t : ℝ) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (A : Tensor3 ℚ X Y Z) (w : ℝ) : Prop :=
  ∃ D : DDecomp A, w ≤ D.wt t

/-- **`V_τ(A) ≥ v`, witnessed by a degeneration.**  Some tensor power `A^{⊗n}`, `n ≥ 1`,
degenerates to a direct sum of matrix multiplication tensors of total `τ`-weight at least
`v^n`. -/
def HasValD (t : ℝ) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (A : Tensor3 ℚ X Y Z) (v : ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ YieldsD t (powT A n) (v ^ n)

end CW90Eight

end OmegaBound

import OmegaBound.ASISum
import OmegaBound.CW90Seven
import OmegaBound.EntropyBasic
import OmegaBound.CW90EightBlkPi

/-!
# The released special level-2 closure: exact finite semantics

This file defines the five standard orientations `112`, `022`, `013`, `031`, and `004` of the
released `TermInfoLv2.m`, MATLAB's left rotation `Rot3` (`rotate`), the unrotated retained and
matrix rate vectors of each orientation (`retainedStandard`, `matrixStandard`), the typed
level-2 `Term`, and the level-2 aggregates `retainedRow`, `matrixRow` and `symmetricRate` (the
symmetric three-way minimum).
-/

open Finset

namespace OmegaBound
namespace ADVXXZLevel2Closure

/-! ## The finite five-orbit universe -/

/-- The five standard orientations implemented by `TermInfoLv2.EvaluatePost`. -/
inductive Kind where
  | k112 | k022 | k013 | k031 | k004
  deriving DecidableEq, Repr

abbrev Shape := ℕ × ℕ × ℕ

def standardShape : Kind → Shape
  | .k112 => (1, 1, 2)
  | .k022 => (0, 2, 2)
  | .k013 => (0, 1, 3)
  | .k031 => (0, 3, 1)
  | .k004 => (0, 0, 4)

/-- The same cyclic left rotation used on the rate vectors. -/
def rotateShape (s : Shape) : Shape := (s.2.1, s.2.2, s.1)

/-- The concrete shape belonging to a MATLAB branch and `rotate_num`. -/
def shapeAt (kind : Kind) (rot : Fin 3) : Shape :=
  rotateShape^[rot.val] (standardShape kind)

/-! ## Exact rate vectors -/

/-- A three-dimensional logarithmic rate vector. -/
abbrev Rate3 := Fin 3 → ℝ

/-- MATLAB `Rot3`: rotate a three-vector to the left `rot` times. -/
def rotate (v : Rate3) (rot : Fin 3) : Rate3 := fun d => v (d + rot)


/-- `H(mu,mu,1-2mu)` in natural logarithms. -/
noncomputable def entropyMu (mu : ℝ) : ℝ :=
  Real.negMulLog mu + Real.negMulLog mu + Real.negMulLog (1 - 2 * mu)

/-- The unrotated `num_block_contribution` from `TermInfoLv2.m`. -/
noncomputable def retainedStandard (kind : Kind) (mu : ℝ) : Rate3 :=
  match kind with
  | .k112 => ![Real.log 2, Real.log 2, entropyMu mu]
  | .k022 | .k013 | .k031 | .k004 => ![0, 0, 0]

/-- The unrotated `mat_size_contribution` from `TermInfoLv2.m`. -/
noncomputable def matrixStandard (q : ℕ) (kind : Kind) (mu : ℝ) : Rate3 :=
  match kind with
  | .k112 => ![(1 - 2 * mu) * Real.log q, 2 * mu * Real.log q,
      (1 - 2 * mu) * Real.log q]
  | .k022 => ![0, 0, entropyMu mu + 2 * (1 - 2 * mu) * Real.log q]
  | .k013 | .k031 => ![0, 0, Real.log 2 + Real.log q]
  | .k004 => ![0, 0, 0]

/-- One typed level-2 term after propagation of its `term_frac` from the higher levels. -/
structure Term where
  kind : Kind
  rot : Fin 3
  frac : ℝ
  mu : ℝ

/-- The only analytic box condition introduced at level 2.  `mu` is unused outside `112/022`,
but imposing the same box uniformly makes validity easy to aggregate and is non-vacuous. -/
def Term.Valid (term : Term) : Prop :=
  0 ≤ term.frac ∧ 0 ≤ term.mu ∧ term.mu ≤ 1 / 2

/-- Rotate exactly as MATLAB does and multiply by `term_frac`. -/
noncomputable def Term.retained (term : Term) : Rate3 :=
  fun d => term.frac * rotate (retainedStandard term.kind term.mu) term.rot d

/-- Rotate exactly as MATLAB does and multiply by `term_frac`. -/
noncomputable def Term.matrix (q : ℕ) (term : Term) : Rate3 :=
  fun d => term.frac * rotate (matrixStandard q term.kind term.mu) term.rot d

/-- Sum the retained-vector contributions of every level-2 term. -/
noncomputable def retainedRow {n : ℕ} (terms : Fin n → Term) : Rate3 :=
  fun d => ∑ a, (terms a).retained d

/-- Sum the level-2 part of the three workspace matrix rows. -/
noncomputable def matrixRow (q : ℕ) {n : ℕ} (terms : Fin n → Term) : Rate3 :=
  fun d => ∑ a, (terms a).matrix q d

/-- The symmetric three-way minimum used at level 2. -/
noncomputable def symmetricRate {n : ℕ} (terms : Fin n → Term) : ℝ :=
  min (retainedRow terms 0) (min (retainedRow terms 1) (retainedRow terms 2))

open CW90Eight

end ADVXXZLevel2Closure
end OmegaBound

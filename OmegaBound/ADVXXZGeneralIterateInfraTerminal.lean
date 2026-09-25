import OmegaBound.ADVXXZGeneralAmend31BoundaryMatrixRestrict
import OmegaBound.ADVXXZGeneralAmend31AccumulatedBoundaryLowerRate
import OmegaBound.ADVXXZGeneralStageNumerical

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- Every occurrence whose physical width is one is a boundary occurrence.  No merging by
`AtomKey` or mass quotient is performed. -/
theorem width_one_inventory_boundary (I : Inventory)
    (hw : ∀ a ∈ I, a.2.1 = 1) : boundaryOccurrences27 I = I := by
  apply List.filter_eq_self.mpr
  rintro ⟨mass, w, u, β⟩ ha
  simp only [decide_eq_true_eq]
  have hw' : w = 1 := hw ⟨mass, w, u, β⟩ ha
  subst w
  exact level_one_boundary31 u

/-- Matrix multiplication tensors multiply by the standard finite-product reindexing. -/
theorem matMulZ_tensorProd_reindex (a b c a' b' c' : ℕ) :
    Restricts (tensorProd (matMulZ a b c).tensor (matMulZ a' b' c').tensor)
        (matMulZ (a * a') (b * b') (c * c')).tensor ∧
      Restricts (matMulZ (a * a') (b * b') (c * c')).tensor
        (tensorProd (matMulZ a b c).tensor (matMulZ a' b' c').tensor) := by
  classical
  constructor
  · refine ADVXXZ.restricts_of_sub (mmIdx a b a' b') (mmIdx b c b' c')
      (mmIdx c a c' a') ?_
    intro x y z
    exact matMul_tensorProd_apply a b c a' b' c' x y z
  · refine ADVXXZ.restricts_of_sub (mmIdxInv a b a' b') (mmIdxInv b c b' c')
      (mmIdxInv c a c' a') ?_
    intro x y z
    symm
    simpa using matMul_tensorProd_apply a b c a' b' c'
      (mmIdxInv a b a' b' x) (mmIdxInv b c b' c' y) (mmIdxInv c a c' a' z)

/-- Appending occurrence lists multiplies their accumulated matrix tensors, up to the standard
matrix-product reindexing. -/
theorem boundaryMatrixZ_append_reindex (q n : ℕ) (I J : Inventory) :
    Restricts
        (tensorProd (boundaryMatrixZ q I n).tensor (boundaryMatrixZ q J n).tensor)
        (boundaryMatrixZ q (I ++ J) n).tensor ∧
      Restricts (boundaryMatrixZ q (I ++ J) n).tensor
        (tensorProd (boundaryMatrixZ q I n).tensor (boundaryMatrixZ q J n).tensor) := by
  unfold boundaryMatrixZ
  rw [boundary_dimension_append31, boundary_dimension_append31,
    boundary_dimension_append31]
  exact
    matMulZ_tensorProd_reindex
      (boundaryDimension31 q I n .X) (boundaryDimension31 q I n .Y)
      (boundaryDimension31 q I n .Z) (boundaryDimension31 q J n .X)
      (boundaryDimension31 q J n .Y) (boundaryDimension31 q J n .Z)

/-- Attach the three accumulated physical matrix dimensions to any retained/source copy data. -/
noncomputable def boundaryNumericalFamily (C : Certificate)
    (Q V : ℚ → ℕ → ℕ) : NumericalFamily where
  Q := Q
  V := V
  a := fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .X
  b := fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .Y
  c := fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .Z

set_option maxHeartbeats 1000000 in
-- Reducing the dependent accumulated-inventory projections exceeds the default heartbeat budget.
/-- The terminal family carries all three matrix `LowerRate`s required by
`IntegralNumericalProduction`; only the retained production and retained rate remain for the
stage recursion to supply. -/
theorem boundaryNumericalFamily_matrix_lowerRates
    (C : Certificate) (hC : AdmissibleAt C) (Q V : ℚ → ℕ → ℕ) :
    LowerRate (outerN C) (boundaryNumericalFamily C Q V).a (derivedMatrixRateAt C .X) ∧
      LowerRate (outerN C) (boundaryNumericalFamily C Q V).b (derivedMatrixRateAt C .Y) ∧
      LowerRate (outerN C) (boundaryNumericalFamily C Q V).c (derivedMatrixRateAt C .Z) := by
  change
    LowerRate (outerN C)
        (fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .X)
        (derivedMatrixRateAt C .X) ∧
      LowerRate (outerN C)
        (fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .Y)
        (derivedMatrixRateAt C .Y) ∧
      LowerRate (outerN C)
        (fun _ m => boundaryDimension31 C.q (accumulatedBoundary27 C) m .Z)
        (derivedMatrixRateAt C .Z)
  exact ⟨accumulated_boundary_lowerRate31 C hC .X,
    accumulated_boundary_lowerRate31 C hC .Y,
    accumulated_boundary_lowerRate31 C hC .Z⟩

end OmegaBound.ADVXXZGeneral
end

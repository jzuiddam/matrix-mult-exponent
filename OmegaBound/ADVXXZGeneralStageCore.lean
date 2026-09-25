import OmegaBound.ADVXXZGeneralCertCore

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

inductive DeletionStep | input | hash | xExact | yCompat | yUnique | yUseful
  | zCompat | zUnique | zUseful

structure NumericalFamily where
  Q : ℚ → ℕ → ℕ
  V : ℚ → ℕ → ℕ
  a : ℚ → ℕ → ℕ
  b : ℚ → ℕ → ℕ
  c : ℚ → ℕ → ℕ

end OmegaBound.ADVXXZGeneral
end

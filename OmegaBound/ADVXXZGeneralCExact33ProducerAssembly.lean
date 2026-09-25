import OmegaBound.ADVXXZGeneralCExact33ProducerSelection

set_option autoImplicit false

/-!
# Copies are monotone under restriction

`copiesZ_restricts33`: if `S` restricts to `T`, then `k` copies of `S` restrict to `k` copies
of `T`.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Copies are monotone under restriction. -/
theorem copiesZ_restricts33 (k : ℕ) (S T : ITensor)
    (hst : Restricts S.tensor T.tensor) :
    Restricts (copiesZ k S).tensor (copiesZ k T).tensor := by
  simpa only [copiesZ] using
    (ADVXXZStage.famDS_const_mono (Finset.univ : Finset (Fin k)) hst)

end
end OmegaBound.ADVXXZGeneral
end

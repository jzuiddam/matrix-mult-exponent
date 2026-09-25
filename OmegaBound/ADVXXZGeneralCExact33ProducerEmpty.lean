import OmegaBound.ADVXXZGeneralCExact33Population
import OmegaBound.ADVXXZGeneralAmend25Ordered
import OmegaBound.ADVXXZGeneralMap
import OmegaBound.ADVXXZGeneralTensorCopiesZ

set_option autoImplicit false

/-!
# Degenerate legs

A tensor with an empty `X` leg restricts to every tensor (`restricts_of_isEmpty_X`), and the
empty labelled family has an empty `X` leg (`emptyFamilyZ_isEmpty_X`).  These serve the
empty-selection branch of the good broken family.
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

/-- A tensor with an empty first leg restricts to every tensor. -/
theorem restricts_of_isEmpty_X {R : Type*} [CommRing R]
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (S : Tensor3 R X' Y' Z') (T : Tensor3 R X Y Z) (hS : IsEmpty X') :
    Restricts S T :=
  ⟨fun x => hS.elim x, fun _ _ => 0, fun _ _ => 0, funext fun x => hS.elim x⟩

/-- The empty labelled family has an empty first leg. -/
theorem emptyFamilyZ_isEmpty_X : IsEmpty emptyFamilyZ.X := ⟨fun x => x.elim⟩


end
end OmegaBound.ADVXXZGeneral
end

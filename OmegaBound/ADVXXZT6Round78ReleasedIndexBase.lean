import OmegaBound.ADVXXZCertificateConstituentData
import OmegaBound.ADVXXZT9R16PositiveParents

/-! # Released child-row bounds -/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round78

open ADVXXZPaper
open ADVXXZT9R16PositiveParents (releasedPositiveInput)

noncomputable def childTriple (t : Fin 126) (u : ChildShape releasedPositiveInput t) :
    Nat × Nat × Nat :=
  (coord .X u.1, coord .Y u.1, coord .Z u.1)

noncomputable def childIndexNat (t : Fin 126) (u : ChildShape releasedPositiveInput t) : Nat :=
  (ADVXXZT2.parKids t.1).findIdx (fun v => v == childTriple t u)

noncomputable def ReleasedChildIndexBounds : Prop :=
  ∀ (t : Fin 126) (u : ChildShape releasedPositiveInput t),
    childIndexNat t u < (ADVXXZT2.parKids t.1).length

noncomputable instance : Decidable ReleasedChildIndexBounds := by
  unfold ReleasedChildIndexBounds childIndexNat childTriple
  infer_instance

/-- One bounded kernel census: every paper child occurs in its released row. -/
theorem releasedChildIndexBounds : ReleasedChildIndexBounds := by
  decide +kernel

end OmegaBound.ADVXXZT6Round78

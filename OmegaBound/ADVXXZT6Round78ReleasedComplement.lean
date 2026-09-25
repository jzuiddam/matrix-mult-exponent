import OmegaBound.ADVXXZT6Round78ReleasedChildEquiv

/-!
# Released child-row pairing

The committed child rows are ordered so that list reversal is exactly the paper complement
`parentShape - childShape`.  This is the pairing needed by the canonical C7 disintegration.

SOURCE: `constituent.tex:119-127`.
-/

set_option maxRecDepth 1000000

namespace OmegaBound.ADVXXZT6Round78

open ADVXXZPaper
open ADVXXZT9R16PositiveParents (releasedPositiveInput)

noncomputable def ReleasedComplementLayout : Prop :=
  ∀ (t : Fin 126) (u : ChildShape releasedPositiveInput t),
    childIndex t (complement releasedPositiveInput t u) = Fin.rev (childIndex t u)

noncomputable instance : Decidable ReleasedComplementLayout := by
  unfold ReleasedComplementLayout
  infer_instance

/-- One kernel finite check over every released parent/child pairing. -/
theorem releasedComplementLayout : ReleasedComplementLayout := by
  decide +kernel

end OmegaBound.ADVXXZT6Round78

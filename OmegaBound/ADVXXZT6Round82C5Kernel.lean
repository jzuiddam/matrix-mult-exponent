import OmegaBound.ADVXXZT6Round82RealDisintegration

/-! # Cleared-integer C5 statement -/

namespace OmegaBound.ADVXXZT6Round82

open ADVXXZ (Chunk)
open ADVXXZPaper (Side)

/-- The physical-side index used by the committed parent table. -/
def sideNat : Side -> Nat
  | .X => 0
  | .Y => 1
  | .Z => 2

/-- C5 at one released parent, with both positive denominators cleared. -/
def ClearedC5At (t : Fin 126) : Prop :=
  forall W (sigma : Chunk 4),
    (ADVXXZT2.parBeta t.1 (sideNat W)).num sigma * (certificateParentDist W t).den =
      (certificateParentDist W t).num sigma * (ADVXXZT2.parBeta t.1 (sideNat W)).den

instance (t : Fin 126) : Decidable (ClearedC5At t) := by
  unfold ClearedC5At
  infer_instance

end OmegaBound.ADVXXZT6Round82

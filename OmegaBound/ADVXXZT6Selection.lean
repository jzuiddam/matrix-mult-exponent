import OmegaBound.ADVXXZT5Logical
import OmegaBound.ADVXXZT6Inventory

/-!
# All-parent constituent positions

For a fixed constituent region, positions are tagged by all `126` ordinary parents, by one
released first-child split coordinate, and by its exact natural multiplicity (`RegionPos`).
`kidPat` reads every released first child as a pattern in `Pat 4`, the alphabet of width-two
first children, and `parentMass` is the physical mass of the global cell owning a parent.
-/

set_option maxRecDepth 100000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZT6Selection

open ADVXXZHash (Pat exists_prime_modulus)
open ADVXXZT2 (parKids kid regNums chNums parRegion parRow logRow)

/-- The finite fact needed to regard every released first child as a `Pat 4`. -/
def KidPatOK : Prop :=
  ∀ (p : Fin 126) (d : Fin (parKids p.1).length),
    let s := kid p.1 d.1
    s.1 + s.2.1 + s.2.2 = 4 ∧ s.1 ≤ 4 ∧ s.2.1 ≤ 4 ∧ s.2.2 ≤ 4

instance : Decidable KidPatOK := by unfold KidPatOK; infer_instance

set_option maxHeartbeats 2000000 in
-- This checks every child coordinate of all 126 released ordinary parents.
theorem kid_pat_ok : KidPatOK := by native_decide

/-- The released first-child shape, in the hashing alphabet. -/
def kidPat (p : Fin 126) (d : Fin (parKids p.1).length) : Pat 4 := by
  have h := kid_pat_ok p d
  exact ⟨(⟨(kid p.1 d.1).1, by omega⟩, ⟨(kid p.1 d.1).2.1, by omega⟩,
    ⟨(kid p.1 d.1).2.2, by omega⟩), h.1⟩

/-- Physical mass of the released global cell owning parent `p`. -/
def parentMass (p : Fin 126) : ℕ :=
  ADVXXZCertificateGlobalData.Certificate.regionDist.num (parRegion p.1) *
    ADVXXZG1.aw (parRegion p.1) (logRow (parRegion p.1) (parRow p.1))

/-- First-half multiplicity of split coordinate `d` in constituent region `r`, at scale `k`.
The complementary half is supplied by reversal. -/
def firstMultiplicity (r : Fin 6) (k : ℕ) (p : Fin 126)
    (d : Fin (parKids p.1).length) : ℕ :=
  parentMass p * k * (regNums p.1).getD r.1 0 * (chNums p.1 r.1).getD d.1 0

/-- The heterogeneous positions of one complete constituent region, across all 126 parents. -/
abbrev RegionPos (r : Fin 6) (k : ℕ) : Type :=
  (p : Fin 126) × (d : Fin (parKids p.1).length) × Fin (firstMultiplicity r k p d)

end ADVXXZT6Selection
end OmegaBound

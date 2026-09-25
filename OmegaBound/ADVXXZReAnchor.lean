import OmegaBound.ADVXXZCertRows
import OmegaBound.ADVXXZRegionalCertificateSplitData
import OmegaBound.ADVXXZR1CertificateSplitData
import OmegaBound.ADVXXZR2CertificateSplitData
import OmegaBound.ADVXXZR3CertificateSplitData
import OmegaBound.ADVXXZR4CertificateSplitData
import OmegaBound.ADVXXZR5CertificateSplitData

/-!
# The global datum at the regional certificate tables

`regionalSplit r` is region `r`'s own residual complete-split table family
(`ADVXXZRegionalCertificateSplitData` for region zero, `ADVXXZR1CertificateSplitData` to
`ADVXXZR5CertificateSplitData` for the others), and `regionalBeta` routes the term `(r, u)` to
region `r`'s family, where `ADVXXZCertificateSplitData.certificateBeta` uses one family for every
region.  `dataR` is `ADVXXZCertificateGlobalData.certificateGlobalData regionalBeta`; only `beta`
differs from `ADVXXZCRows.dataE`, and `joint_eq` records that the joint weights agree by `rfl`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset Tensor3

namespace OmegaBound
namespace ADVXXZRA

open ADVXXZPaper (GlobalData Shape Side)
open ADVXXZHash (Pat)
open ADVXXZ (Chunk SplitDist)
open ADVXXZCRows (dataE)

/-! ## The re-anchored datum -/

/-- Region `r`'s **own** residual complete-split tables.  Region zero's is `ADVXXZRegionalCertificateSplitData`. -/
def regionalSplit (r : Fin 6) : Side → Pat (2 * 4) → SplitDist 4 :=
  match (r : ℕ) with
  | 0 => ADVXXZRegionalCertificateSplitData.certificateSplit
  | 1 => ADVXXZR1CertificateSplitData.certificateSplit
  | 2 => ADVXXZR2CertificateSplitData.certificateSplit
  | 3 => ADVXXZR3CertificateSplitData.certificateSplit
  | 4 => ADVXXZR4CertificateSplitData.certificateSplit
  | _ => ADVXXZR5CertificateSplitData.certificateSplit

/-- **THE RE-ANCHORED `beta`.**  Term `(r, u)` is routed to region `r`'s own tables, where
`ADVXXZCertificateSplitData.certificateBeta` discarded `r`. -/
def regionalBeta : Side → Fin 6 → Shape 4 → SplitDist 4 := fun S r u => regionalSplit r S u

/-- **THE RE-ANCHORED DATUM.**  Same constructor, same region and shape simplexes, same joint;
only `beta` moves. -/
noncomputable def dataR : GlobalData 4 :=
  ADVXXZCertificateGlobalData.certificateGlobalData regionalBeta


/-- The re-anchored datum at the endpoint's own unreduced width. -/
noncomputable def dataRE : GlobalData (2 * 2) := dataR

/-- **THE GRID DOES NOT MOVE.**  `beta` is not a factor of `joint`. -/
theorem joint_eq : dataRE.joint = dataE.joint := rfl

/-! ## Two constant words -/

section NonVacuity


/-- The all-`0` word. -/
def c0 : Chunk 4 := fun _ => 0

/-- The all-`2` (pure corner) word. -/
def c2 : Chunk 4 := fun _ => 2

end NonVacuity

end ADVXXZRA
end OmegaBound

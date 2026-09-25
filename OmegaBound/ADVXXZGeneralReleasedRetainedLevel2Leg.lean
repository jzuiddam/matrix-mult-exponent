import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows
import OmegaBound.ADVXXZCertClose

/-!
# The level-2 leg of the released retained-rate fit

`derivedRetainedRate releasedOrdinaryCertificatePhysical` splits (frozen `V17_I_Rows.8`, first
conjunct) into the legacy ordinary rate plus `symmetricRate releasedLevel2Terms`.  This module
proves the level-2 leg against the released retained row `R1`: the three released retained rows
are the certified `actualRetainedCapacity_1_d`, and `R1_le_actualRetainedCapacity_1` bounds `R1`
by their minimum.  No new numerics; the proof is three rewrites.
-/

namespace OmegaBound.ADVXXZGeneral

/-- The level-2 retained leg of the released fit. -/
def S_released_level2_retained_leg : Prop :=
  (OmegaBound.ADVXXZCert.R1 : ℝ) ≤
    OmegaBound.ADVXXZLevel2Closure.symmetricRate
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms

/-- The level-2 leg holds: `R1 ≤ symmetricRate releasedLevel2Terms`. -/
theorem released_level2_retained_leg : S_released_level2_retained_leg := by
  have h0 := OmegaBound.ADVXXZReleasedTree.released_retainedRow_0
  have h1 := OmegaBound.ADVXXZReleasedTree.released_retainedRow_1
  have h2 := OmegaBound.ADVXXZReleasedTree.released_retainedRow_2
  have hmin := OmegaBound.ADVXXZCert.R1_le_actualRetainedCapacity_1
  unfold S_released_level2_retained_leg OmegaBound.ADVXXZLevel2Closure.symmetricRate
  rw [h0, h1, h2]
  exact hmin

end OmegaBound.ADVXXZGeneral

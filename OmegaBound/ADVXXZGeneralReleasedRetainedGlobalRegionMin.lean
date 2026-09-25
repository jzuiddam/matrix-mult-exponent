import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalDualData

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

/-- Three directional bounds imply the correspondingly weighted paper-region minimum. -/
theorem released_global_region_lower_of_xyz (r : Fin 6) (R : ℝ)
    (hx : R ≤ Real.log 2 * physicalGlobalSpec.A.probR r *
      (entropy (marginal (physicalGlobalSpec.toPaper.alpha r)
          (physicalGlobalSpec.toPaper.perm r .X)) -
        penalty (physicalGlobalSpec.toPaper.alpha r)))
    (hy : R ≤ Real.log 2 * physicalGlobalSpec.A.probR r *
      (entropy (globalAverage physicalGlobalSpec.toPaper r
          (physicalGlobalSpec.toPaper.perm r .Y)) -
        globalEta physicalGlobalSpec.toPaper r
          (physicalGlobalSpec.toPaper.perm r .X)
          (physicalGlobalSpec.toPaper.perm r .Y)
          (physicalGlobalSpec.toPaper.perm r .Z)))
    (hz : R ≤ Real.log 2 * physicalGlobalSpec.A.probR r *
      (entropy (globalAverage physicalGlobalSpec.toPaper r
          (physicalGlobalSpec.toPaper.perm r .Z)) -
        globalLambda physicalGlobalSpec.toPaper r
          (physicalGlobalSpec.toPaper.perm r .X)
          (physicalGlobalSpec.toPaper.perm r .Y)
          (physicalGlobalSpec.toPaper.perm r .Z))) :
    R ≤ Real.log 2 * physicalGlobalSpec.A.probR r *
      globalRegionRate physicalGlobalSpec.toPaper r := by
  have hw : 0 ≤ Real.log 2 * physicalGlobalSpec.A.probR r :=
    mul_nonneg (Real.log_pos (by norm_num)).le
      (RatDist.probR_nonneg physicalGlobalSpec.A r)
  unfold globalRegionRate
  rw [mul_min_of_nonneg _ _ hw, mul_min_of_nonneg _ _ hw]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_region_lower_of_xyz

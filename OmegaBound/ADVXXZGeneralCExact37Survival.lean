import OmegaBound.ADVXXZGeneralCExact37Hash
import OmegaBound.ADVXXZGeneralPQExponentsParent25

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The X-rival debit is covered by the constituent demand once the actual stage-label
X-fibres are known to be uniform.  This isolates the one constituent-specific orbit count
from the generic affine-hash calculation. -/
theorem stage_hashXRivals_le_demand37 {w s b m : ℕ} (q floor : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (ε : ℚ) (r : Fin 6)
    (j : StageTargetLabel37 q p d b m r)
    (huniform :
      (hashXFiber27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j.val).card *
        (hashXImage27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))).card =
        Fintype.card (stagePopulationAt q p d b m r).Label) :
    4 * (hashXRivals27
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j.val).card ≤
      stageDemand25 p d b floor ε m r := by
  let P := rolePopulation (stagePopulationAt q p d b m r) (d.perm r)
  have h := hashXRivals_le_naturalDemand27 P
    (max floor (2 * (w + w) + 3))
    (((Finset.univ : Finset (stagePopulationAt q p d b m r).Label).image
      (fun k => (stagePopulationAt q p d b m r).coarse k (d.perm r .Y))).card)
    (((Finset.univ : Finset (stagePopulationAt q p d b m r).Label).image
      (fun k => (stagePopulationAt q p d b m r).coarse k (d.perm r .Z))).card)
    (stagePopulationAt q p d b m r).target.card
    ((cLength p b m)^2)
    (Parent25.pcompMax p d b ε m r 0)
    (Parent25.pcompMax p d b ε m r 1) j.val huniform
  simpa only [stageDemand25, P, rolePopulation] using h

/-- Exact `3/4` survival for a constituent target bucket, conditional only on the stage orbit
count and the displayed demand/modulus inequality. -/
theorem stageTargetBucket_survival_of_demand37 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (ε : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor ε m r ≤ M)
    (j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B)
    (huniform :
      (hashXFiber27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j.val).card *
        (hashXImage27
          (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))).card =
        Fintype.card (stagePopulationAt q p d b m r).Label) :
    (3 : ℝ) / 4 ≤ cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega => j ∈ stageSelectedTargets37 q p d r B omega) := by
  have hrivals := stage_hashXRivals_le_demand37 q floor p d ε r j huniform
  have hrivalsM : 4 * (hashXRivals27
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) j.val).card ≤ M := by
    omega
  have h := selected_cond_three_quarters_of_hashXRivals27
    (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
    (stage_role_tight37 q p d hd r) (stage_role_coarse_injective37 q p d hd r)
    M hprime hodd hfloor B j.val j.property z.val z.property hrivalsM
  simpa only [stageTargetBucket37, stageSelectedTargets37, Finset.mem_filter,
    Finset.mem_attach, true_and] using h

-- The unconditional specialization is placed in the orbit module, after the stage-fibre
-- partition identity has been established.

end
end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralCExact41DemandLabelCompat
import OmegaBound.ADVXXZGeneralCExact36GridPartition
import OmegaBound.ADVXXZGeneralCExact36Boundary

set_option autoImplicit false

/-!
# The full-grid demand cap

`constituent_full_grid_demand_cap41`: at every boundary-compatible exact constituent grid, the
stage demand is at most `constituentDemandCap40 p b floor m` times the exponential of the grid's
demand exponent plus `constituentPCompDelta40 p ε`, at scale `b * m`.
-/

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section

/-- The full-grid demand cap; the cap does not depend on the grid. -/
theorem constituent_full_grid_demand_cap41 {w s b m : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (h : ConstituentExactGrid27 d m) (hboundary : ConstituentGridBoundary28 h)
    (floor : ℕ) (hfloor : 2 * (w + w) + 3 ≤ floor)
    (ε : ℚ) (hε : 0 < ε) (hm : 0 < m) (r : Fin 6) :
    (stageDemand25 (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b floor ε m r : ℝ) ≤
      constituentDemandCap40 p b floor m *
        Real.exp ((demandExponent (constituentGridParent27 d hd m h)
          (constituentGridSpec27 d hd m h) r + constituentPCompDelta40 p ε) *
            (b * m : ℝ)) := by
  have hdg := constituent_grid_admissible28 d b m hd h hboundary
  have hbg := constituent_grid_integral36 d hd hb m h
  have hcap := constituent_grid_demand_paper_cap40_at_delta
    (constituentGridParent27 d hd m h) (constituentGridSpec27 d hd m h)
    hdg hbg floor hfloor ε hε hm r
  simpa only [constituentDemandCap40, constituentDemandLogLoss40,
    constituentPCompLoss40, constituentPCompPower40, constituentPCompDelta40,
    constituentGridParent27, constituentBaseTotal] using hcap

end
end OmegaBound.ADVXXZGeneral

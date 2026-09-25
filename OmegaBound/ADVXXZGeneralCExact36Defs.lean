import OmegaBound.ADVXXZGeneralCExact33ProducerCount
import OmegaBound.ADVXXZGeneralCExact33ProducerAssembly
import OmegaBound.ADVXXZGeneralGridInput29Facts
import OmegaBound.ADVXXZGeneralGridInput29Counts

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-!
# Integrality of a constituent grid at one scale

`ConstituentIntegral36 d b m`: the region and alpha masses are integral at scale `b`, and the
grid's child counts `stageCounts27` are exact at the grid's own scale `m`.
-/

-- P/constituent.tex:120,151-170;
-- H/analysis_constituent.tex:117-125,314-325. Integrality at ONE scale.
structure ConstituentIntegral36 {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b m : ℕ) : Prop where
  bpos : 0 < b
  regionIntegral : ∀ (t : Fin s) (r : Fin 6),
    integral ((b : ℚ) * p.baseN t * (d.A t).prob r)
  alphaIntegral : ∀ (t : Fin s) (r : Fin 6) (u : ChildShape p t),
    integral ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob u)
  countsExact : ∀ (r : Fin 6) (W : Side) (t : Fin s) (u : ChildShape p t) (σ : Chunk w),
    (stageCounts27 m p d r W t u σ : ℚ) =
      (m : ℚ) * d.outBase ⟨t,r,u⟩ * (d.betaChild W t r u).prob σ

end OmegaBound.ADVXXZGeneral

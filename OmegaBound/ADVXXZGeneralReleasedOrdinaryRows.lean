import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical
import OmegaBound.ADVXXZGeneralCertScaleV22
import OmegaBound.ADVXXZGeneralInventory
import OmegaBound.ADVXXZGeneralTensorAux
import OmegaBound.ADVXXZGeneralRatesFitV22
import OmegaBound.ADVXXZGeneralReleasedInventoryAux
import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round26CountingSpine
import OmegaBound.ADVXXZT6Round82RealDisintegration
import OmegaBound.ADVXXZLevel2Closure
import OmegaBound.ADVXXZReleasedTree

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000


noncomputable def ordinaryAtomRate (q : ℕ) (W : Side) (a : ℚ × AtomKey) : ℝ := by
  classical
  let u := a.2.2.1
  let beta := a.2.2.2
  let active := match W with
    | .X => coord .Y u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Z u
    | .Y => coord .Z u = 0 ∧ 0 < coord .X u ∧ 0 < coord .Y u
    | .Z => coord .X u = 0 ∧ 0 < coord .Y u ∧ 0 < coord .Z u
  let V : Side := match W with | .X => .X | .Y => .X | .Z => .Y
  exact if active then (a.1 : ℝ) *
    (entropyNats (fun σ => (beta V σ : ℝ)) + Real.log (q : ℝ) *
      ∑ σ : Chunk a.2.1, (beta V σ : ℝ) *
        ((Finset.univ.filter (fun i : Fin a.2.1 => (σ i).val = 1)).card : ℝ)) else 0

noncomputable def ordinaryInventoryRate (q : ℕ) (W : Side) (I : Inventory) : ℝ :=
  (I.map (ordinaryAtomRate q W)).sum

noncomputable def ordinary112Nats
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (W : Side) : ℝ :=
  if coord W (ordinaryOccurrence t).1.2.2.1 = 2 then
    OmegaBound.ADVXXZLevel2Closure.entropyMu ((ordinaryTarget t).muNum / (ordinaryD : ℝ))
  else Real.log 2

end OmegaBound.ADVXXZGeneral
end

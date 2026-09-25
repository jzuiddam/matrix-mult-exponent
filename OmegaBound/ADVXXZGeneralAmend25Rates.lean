import OmegaBound.ADVXXZGeneralAmend25Ordered
import OmegaBound.ADVXXZGeneralRatesFit
import OmegaBound.ADVXXZGeneralGridTensorV22
set_option autoImplicit false
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
noncomputable def stageDemand25 {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b floor : ℕ) (ε : ℚ) (m : ℕ) (r : Fin 6) : ℕ := by
  classical
  let P := stagePopulationAt 0 p d b m r
  let representedCount := fun W : Side =>
    ((Finset.univ : Finset P.Label).image (fun j => P.coarse j W)).card
  exact natural_demand (max floor (2*(w+w)+3)) (Fintype.card P.Label)
    (representedCount (d.perm r .X)) (representedCount (d.perm r .Y))
    (representedCount (d.perm r .Z)) P.target.card
    ((cLength p b m)^2) (Parent25.pcompMax p d b ε m r 0) (Parent25.pcompMax p d b ε m r 1)

noncomputable def demandExponent {w s : ℕ} (p : ConstituentInput w s)
    (d : ConstituentSpec p) (r : Fin 6) : ℝ :=
  let xSide := d.perm r .X
  let ySide := d.perm r .Y
  let zSide := d.perm r .Z
  let xDemand := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) + constituentPenalty d.toPaper t r -
      entropy (constituentMarginal d.toPaper t r xSide))
  let yDemand := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) + constituentEta d.toPaper t r xSide ySide zSide -
      splitEntropy (d.betaRegion ySide t r))
  let zDemand := ∑ t, (p.baseN t : ℝ) * d.toPaper.A t r *
    (entropy (d.toPaper.alpha t r) + constituentLambda d.toPaper t r xSide ySide zSide -
      splitEntropy (d.betaRegion zSide t r))
  Real.log 2 * max xDemand (max yDemand zDemand)

noncomputable def globalPcompMax {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) (r : Fin 6) (which : Fin 2) : ℝ := by
  classical
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g n ξ r which)).image
    (globalPcomp g n ξ r which)
  exact if h : values.Nonempty then values.max' h else 0

noncomputable def globalDemand {w : ℕ} (g : GlobalSpec w) (b floor m : ℕ)
    (ξ : ExactGrid g (b*m)) (r : Fin 6) : ℕ := by
  classical
  let P := globalPopulation g (b*m) ξ r
  let representedCount := fun W : Side =>
    ((Finset.univ : Finset P.Label).image (fun j => P.coarse j W)).card
  exact natural_demand (max floor (2*w+3)) (Fintype.card P.Label)
    (representedCount (g.perm r .X)) (representedCount (g.perm r .Y))
    (representedCount (g.perm r .Z)) P.target.card (80*(w*(b*m)))
    (globalPcompMax g (b*m) ξ r 0) (globalPcompMax g (b*m) ξ r 1)

noncomputable def exactGridTensor (q : ℕ) {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) : ITensor := by
  classical
  let e := (Fintype.equivFin (Fin 6 × Shape w)).symm
  let k := fun t => ((n : ℚ) * g.joint.prob (e t)).floor.toNat
  let L := (t : Fin (Fintype.card (Fin 6 × Shape w))) →
    Fin (k t) → Fin w → CW90.Idx7 q
  let keep := fun (W : Side) (x : L) =>
    ∀ t σ, typeCnt (chunkSeq (x t)) σ = ξ.count W (e t).1 (e t).2 σ
  exact
    { X := L
      Y := L
      Z := L
      tensor := zoP (keep .X) (keep .Y) (keep .Z)
        (fun x y z => ∏ t,
          tensorPower (conZ q w (coord .X (e t).2) (coord .Y (e t).2)
            (coord .Z (e t).2)) (k t) (x t) (y t) (z t)) }

noncomputable def gridRate {w : ℕ} (g : GlobalSpec w) (n : ℕ)
    (ξ : ExactGrid g n) : ℝ := by
  classical
  let beta : Side → Fin 6 → Shape w → SplitDist w := fun W r u =>
    let k := (n * g.joint.prob (r, u)).floor.toNat
    if hk : 0 < k then
      { num := ξ.count W r u
        den := k
        den_pos := hk
        sum_num := ξ.total W r u }
    else
      g.beta W r u
  let data : GlobalData w := { g.toPaper with beta := beta }
  exact Real.log 2 * ∑ r, g.A.probR r * globalRegionRate data r

end
end OmegaBound.ADVXXZGeneral


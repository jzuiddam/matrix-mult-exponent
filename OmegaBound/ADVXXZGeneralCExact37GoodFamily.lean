import OmegaBound.ADVXXZGeneralCExact37Target
import OmegaBound.ADVXXZGeneralCExact36Repair

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private def stageTargetValEmbedding37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) :
    StageTargetLabel37 q p d b m r ↪
      (stagePopulationAt q p d b m r).Label where
  toFun j := j.val
  inj' _ _ h := Subtype.ext h

private theorem target_exactPartsAt_card_eq37 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j k : StageTargetLabel37 q p d b m r) (W : Side) :
    (exactPartsAt q b m p d r j.val W).card =
      (exactPartsAt q b m p d r k.val W).card := by
  classical
  obtain ⟨e, _⟩ := CExact36RepairAux.coarse_transport_parent36 q m p d r j k W
  have hcard : Fintype.card (RepresentedParts p d b m j W) =
      Fintype.card (RepresentedParts p d b m k W) := Fintype.card_congr e
  change Fintype.card {a // a ∈ exactPartsAt q b m p d r j.val W} =
      Fintype.card {a // a ∈ exactPartsAt q b m p d r k.val W} at hcard
  simpa only [Fintype.card_coe] using hcard

/-- A selected-gated hole count, so unselected hash outcomes incur no first-moment charge. -/
def stageSelectedHoleCount37 {w s b m M : ℕ} (q : ℕ) (ε : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : StageTargetLabel37 q p d b m r) (W : Side) : ℕ :=
  if j ∈ stageSelectedTargets37 q p d r B omega then
    (holesAt25 q b m M ε p d r B omega j.val W).card else 0

set_option maxHeartbeats 2000000 in
-- The selected-label subtype and the dependent exact-part cardinalities are normalized together.
/-- The generic first-moment selection theorem specialized to a constituent stage region.
The only quantitative premise left is the selected-gated per-side hole tail. -/
theorem stage_good_family_of_failures37 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b)
    (ε : ℚ) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor ε m r ≤ M)
    (j0 : StageTargetLabel37 q p d b m r)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0) (debit : Side → ℝ)
    (hfailure : ∀ j z W,
      cond (stageTargetBucket37 q p d r B j z)
        (Finset.univ.filter fun omega =>
          j ∈ stageSelectedTargets37 q p d r B omega ∧
            (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
                (exactPartsAt q b m p d r j0.val W).card <
              (holesAt25 q b m M ε p d r B omega j.val W).card) ≤ debit W)
    (hmargin : 0 < (3 : ℝ) / 4 - ∑ W, debit W) :
    ∃ (omega : HashOutcome (stagePopulationAt q p d b m r) M)
      (J : Finset (stagePopulationAt q p d b m r).Label),
      (∀ j, j ∈ J → stageGood25 q p d b ε m r M B omega j) ∧
      ((3 : ℝ) / 4 - ∑ W, debit W) *
          Fintype.card (StageTargetLabel37 q p d b m r) *
          Fintype.card (StageBucketLabel37 B) / (M : ℝ) ^ 2 ≤ (J.card : ℝ) := by
  classical
  let N := (stagePopulationAt q p d b m r).n
  let threshold : Side → ℝ := fun _ => 1 / (4 * N : ℝ)
  let parts : Side → ℕ := fun W => (exactPartsAt q b m p d r j0.val W).card
  let holes := fun omega (j : StageTargetLabel37 q p d b m r) W =>
    stageSelectedHoleCount37 q ε p d r B omega j W
  have hevent (j : StageTargetLabel37 q p d b m r) (W : Side) :
      (Finset.univ.filter fun omega =>
        threshold W * (parts W : ℝ) < (holes omega j W : ℝ)) =
      Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * N) : ℝ) * (parts W : ℝ) <
            (holesAt25 q b m M ε p d r B omega j.val W).card := by
    ext omega
    by_cases hj : j ∈ stageSelectedTargets37 q p d r B omega
    · simp [holes, stageSelectedHoleCount37, threshold, hj]
    · simp [holes, stageSelectedHoleCount37, threshold, hj]
      positivity
  have hfailure' : ∀ j z W,
      cond (stageTargetBucket37 q p d r B j z)
        (Finset.univ.filter fun omega =>
          threshold W * (parts W : ℝ) < (holes omega j W : ℝ)) ≤ debit W := by
    intro j z W
    rw [hevent]
    exact hfailure j z W
  letI : Nonempty (StageTargetLabel37 q p d b m r) := ⟨j0⟩
  obtain ⟨omega, hgood⟩ := exists_good_subfamily
    (stageTargetBucket37 q p d r B)
    (stageSelectedTargets37 q p d r B) holes parts threshold M hprime.pos
    ((3 : ℝ) / 4) debit
    (fun j z => by
      exact_mod_cast stageTargetBucket_card37 q p d hd r B hprime hodd hfloor j z)
    (stageTargetBucket_pairwise37 q p d r B)
    (stageTargetBucket_survival37 q floor p d hd ε r B hprime hodd hfloor hdemand)
    hfailure' hmargin
  let G := (stageSelectedTargets37 q p d r B omega).filter fun j =>
    ∀ W, (holes omega j W : ℝ) ≤ threshold W * (parts W : ℝ)
  let J := G.map (stageTargetValEmbedding37 q p d r)
  refine ⟨omega, J, ?_, ?_⟩
  · intro j hj
    obtain ⟨j', hjG, rfl⟩ := Finset.mem_map.mp hj
    have hjSelected : j'.val ∈ selected
        (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M B omega := by
      have h := (Finset.mem_filter.mp hjG).1
      simpa only [stageSelectedTargets37, Finset.mem_filter, Finset.mem_attach,
        true_and] using h
    refine ⟨hjSelected, fun W => ?_⟩
    have hjBound := (Finset.mem_filter.mp hjG).2 W
    have hjSubtype : j' ∈ stageSelectedTargets37 q p d r B omega :=
      (Finset.mem_filter.mp hjG).1
    rw [show holes omega j' W =
        (holesAt25 q b m M ε p d r B omega j'.val W).card by
      simp [holes, stageSelectedHoleCount37, hjSubtype]] at hjBound
    have hparts := target_exactPartsAt_card_eq37 q m p d r j' j0 W
    dsimp only [threshold, parts, N] at hjBound
    rw [← hparts] at hjBound
    have hN : 0 < (stagePopulationAt q p d b m r).n := Nat.pos_of_ne_zero hn
    have hden : 0 < (4 * (stagePopulationAt q p d b m r).n : ℝ) := by
      exact_mod_cast Nat.mul_pos (by norm_num) hN
    have hdiv :
        ((holesAt25 q b m M ε p d r B omega j'.val W).card : ℝ) ≤
          ((exactPartsAt q b m p d r j'.val W).card : ℝ) /
            (4 * (stagePopulationAt q p d b m r).n : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hjBound
    have hmul := (le_div_iff₀ hden).mp hdiv
    exact_mod_cast (show
      ((4 * (stagePopulationAt q p d b m r).n *
        (holesAt25 q b m M ε p d r B omega j'.val W).card : ℕ) : ℝ) ≤
          (exactPartsAt q b m p d r j'.val W).card by
      push_cast
      nlinarith)
  · simpa [J, G] using hgood

end
end OmegaBound.ADVXXZGeneral

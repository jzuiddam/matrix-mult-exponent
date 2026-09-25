import OmegaBound.ADVXXZGeneralCExact38CollisionMoment

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

set_option maxHeartbeats 1000000 in
-- The total-hole event is split into input-bad and input-good exact parts.
/-- Combining the deterministic input half-reserve and the collision first moment gives
the exact selected-gated Y/Z tail at the full `1/(4N)` threshold. -/
theorem stageSelectedExactHoles_YZ_cond38 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor epsilon m r ≤ M)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hscale : 40 * (stagePopulationAt q p d b m r).n ≤ (cLength p b m) ^ 2)
    (which : Fin 2) (j0 j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B)
    (hbad : (((exactPartsAt q b m p d r j.val (Parent25.side d r which)).filter
        fun a => ¬ Parent25.inputPartKeep p d b m epsilon r
          (Parent25.side d r which) a).card : ℝ) ≤
      (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
        (exactPartsAt q b m p d r j0.val (Parent25.side d r which)).card)
    (hparts : 0 < (exactPartsAt q b m p d r j0.val
      (Parent25.side d r which)).card) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
              (exactPartsAt q b m p d r j0.val (Parent25.side d r which)).card <
            (holesAt25 q b m M epsilon p d r B omega j.val
              (Parent25.side d r which)).card) ≤ (1 / 10 : ℝ) := by
  let P := stagePopulationAt q p d b m r
  let W := Parent25.side d r which
  let E := stageTargetBucket37 q p d r B j z
  let parts := (exactPartsAt q b m p d r j0.val W).card
  let threshold : ℝ := (1 / (8 * P.n) : ℝ) * parts
  let collision := fun omega =>
    stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which
  have hthreshold : 0 < threshold := by
    have hN : (0 : ℝ) < P.n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hp : (0 : ℝ) < parts := by exact_mod_cast hparts
    dsimp only [threshold]
    positivity
  have hmoment := stageSelectedCollisionHoles_paper_moment38 q floor p d hd epsilon r B
    hprime hodd hfloor hdemand hn hscale which j0 j z
  have hmarkov : cond E (Finset.univ.filter fun omega =>
      threshold < (collision omega : ℝ)) ≤ (1 / 10 : ℝ) := by
    apply conditional_nat_markov27 E
      (stageTargetBucket_nonempty37 q p d hd r B hprime hodd hfloor j z)
      collision threshold (1 / 10) hthreshold
    simpa only [E, collision, threshold, P, W, parts] using hmoment
  have hthresholdDouble :
      (1 / (4 * P.n) : ℝ) * parts = 2 * threshold := by
    have hN : (P.n : ℝ) ≠ 0 := by exact_mod_cast hn
    dsimp only [threshold]
    field_simp
    ring
  have hsub : E ∩ (Finset.univ.filter fun omega =>
      j ∈ stageSelectedTargets37 q p d r B omega ∧
        (1 / (4 * P.n) : ℝ) * parts <
          (holesAt25 q b m M epsilon p d r B omega j.val W).card) ⊆
      E ∩ (Finset.univ.filter fun omega => threshold < (collision omega : ℝ)) := by
    intro omega homega
    have hdata := (Finset.mem_filter.mp (Finset.mem_inter.mp homega).2).2
    let holes := holesAt25 q b m M epsilon p d r B omega j.val W
    let good : (stagePopulationAt q p d b m r).Part W → Prop := fun a =>
      Parent25.inputPartKeep p d b m epsilon r W a
    have hbadSub : holes.filter (¬ good ·) ⊆
        (exactPartsAt q b m p d r j.val W).filter (¬ good ·) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨
        holesAt25_subset_exactPartsAt38 q b m M epsilon p d r B omega j.val W
          (Finset.mem_filter.mp ha).1,
        (Finset.mem_filter.mp ha).2⟩
    have hbadHole : ((holes.filter (¬ good ·)).card : ℝ) ≤ threshold := by
      have hc := Finset.card_le_card hbadSub
      exact (Nat.cast_le.mpr hc).trans (by simpa only [threshold, parts, P, W] using hbad)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := holes) (p := good)
    have hsplitR : ((holes.filter good).card : ℝ) +
        ((holes.filter (¬ good ·)).card : ℝ) = holes.card := by
      exact_mod_cast hsplit
    have hcollision : collision omega = (holes.filter good).card := by
      simp [collision, stageSelectedCollisionHoleCount38, hdata.1, holes, good, W]
      rfl
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp homega).1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hcollision]
    rw [hthresholdDouble] at hdata
    nlinarith
  calc
    cond E (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          (1 / (4 * P.n) : ℝ) * parts <
            (holesAt25 q b m M epsilon p d r B omega j.val W).card) ≤
        cond E (Finset.univ.filter fun omega =>
          threshold < (collision omega : ℝ)) := by
      unfold cond
      gcongr
    _ ≤ (1 / 10 : ℝ) := hmarkov

end
end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralCExact38GridHoleTails
import OmegaBound.ADVXXZGeneralCExact38InputReserve
import OmegaBound.ADVXXZGeneralCExact37GoodFamily

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The population-length condition needed by the collision moment holds uniformly over
every empirical grid beyond one threshold chosen before the grid. -/
theorem constituent_grid_hole_scale_threshold39 (q : ℕ) {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ (h : ConstituentExactGrid27 d m) (r : Fin 6),
      40 * (stagePopulationAt q (constituentGridParent27 d hd m h)
        (constituentGridSpec27 d hd m h) b m r).n ≤ (cLength p b m) ^ 2 := by
  refine ⟨80, ?_⟩
  intro m hm h r
  let pg := constituentGridParent27 d hd m h
  let dg := constituentGridSpec27 d hd m h
  let L := cLength p b m
  let N := (stagePopulationAt q pg dg b m r).n
  have hN : N ≤ 2 * L := by
    have hraw := stagePopulation_n_le q pg dg b m r
    simpa only [N, L, pg, dg, constituentGridParent27, cLength,
      constituentBaseTotal] using hraw
  have hmL : m ≤ L := le_cLength q p d b m hb.1
  have h80L : 80 ≤ L := hm.trans hmL
  calc
    40 * N ≤ 40 * (2 * L) := Nat.mul_le_mul_left 40 hN
    _ = 80 * L := by ring
    _ ≤ L * L := Nat.mul_le_mul_right L h80L
    _ = L ^ 2 := by ring

set_option maxHeartbeats 2000000 in
/-- The three premise-shaped hole tails of the `CExact38` modules instantiate the constituent good-family theorem.
The debit is zero on the physical X role and `1/10` on the other two roles, hence the exact
surviving coefficient is `11/20`. -/
theorem stage_good_family_paper39 {w s b m M : ℕ} [NeZero M]
    (q floor : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b)
    (hdInput : InputAdm29 d b) (hbInput : InputInt29 d b m)
    (epsilon : ℚ) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (hdemand : 2 * stageDemand25 p d b floor epsilon m r ≤ M)
    (j0 : StageTargetLabel37 q p d b m r)
    (hn : (stagePopulationAt q p d b m r).n ≠ 0)
    (hscale : 40 * (stagePopulationAt q p d b m r).n ≤ (cLength p b m) ^ 2)
    (hinputHalf : ∀ (k : StageTargetLabel37 q p d b m r) (W : Side),
      (((exactPartsAt q b m p d r k.val W).filter fun a =>
        ¬ Parent25.inputPartKeep p d b m epsilon r W a).card : ℝ) ≤
        (1 / (8 * (stagePopulationAt q p d b m r).n) : ℝ) *
          (exactPartsAt q b m p d r k.val W).card) :
    ∃ (omega : HashOutcome (stagePopulationAt q p d b m r) M)
      (J : Finset (stagePopulationAt q p d b m r).Label),
      (∀ j, j ∈ J → stageGood25 q p d b epsilon m r M B omega j) ∧
      (11 / 20 : ℝ) * Fintype.card (StageTargetLabel37 q p d b m r) *
          Fintype.card (StageBucketLabel37 B) / (M : ℝ) ^ 2 ≤ (J.card : ℝ) := by
  let debit : Side → ℝ := fun W => if W = d.perm r .X then 0 else 1 / 10
  let e : Side ≃ Side := Equiv.ofBijective (d.perm r) (hd.roles.1 r)
  have hsum_perm : (∑ W, debit (d.perm r W)) = ∑ W, debit W := by
    simpa only [e, Equiv.ofBijective_apply] using Equiv.sum_comp e debit
  have hYX : d.perm r .Y ≠ d.perm r .X :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hZX : d.perm r .Z ≠ d.perm r .X :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hsum : ∑ W, debit W = (1 / 5 : ℝ) := by
    rw [← hsum_perm]
    have hside : (Finset.univ : Finset Side) = {.X, .Y, .Z} := by decide +kernel
    rw [hside]
    simp [debit, Finset.sum_insert, hYX, hZX]
    norm_num
  have hcoefficient : (3 : ℝ) / 4 - ∑ W, debit W = 11 / 20 := by
    rw [hsum]
    norm_num
  have hmargin : 0 < (3 : ℝ) / 4 - ∑ W, debit W := by
    rw [hsum]
    norm_num
  have hfailure : ∀ j z W,
      cond (stageTargetBucket37 q p d r B j z)
        (Finset.univ.filter fun omega =>
          j ∈ stageSelectedTargets37 q p d r B omega ∧
            (1 / (4 * (stagePopulationAt q p d b m r).n) : ℝ) *
                (exactPartsAt q b m p d r j0.val W).card <
              (holesAt25 q b m M epsilon p d r B omega j.val W).card) ≤ debit W := by
    intro j z W
    obtain ⟨S, rfl⟩ := (hd.roles.1 r).2 W
    cases S with
    | X =>
        rw [stageSelectedExactHoles_X_paper_cond38 q p d hd epsilon r B hn
          j0 j z hinputHalf]
        simp [debit]
    | Y =>
        have htail := stageSelectedExactHoles_Y_paper_cond38 q floor p d hd
          hdInput hbInput epsilon r B hprime hodd hfloor hdemand hn hscale
          j0 j z hinputHalf
        simpa [debit, hYX] using htail
    | Z =>
        have htail := stageSelectedExactHoles_Z_paper_cond38 q floor p d hd
          hdInput hbInput epsilon r B hprime hodd hfloor hdemand hn hscale
          j0 j z hinputHalf
        simpa [debit, hZX] using htail
  obtain ⟨omega, J, hgood, hcount⟩ := stage_good_family_of_failures37
    q floor p d hd epsilon r B hprime hodd hfloor hdemand j0 hn debit
      hfailure hmargin
  refine ⟨omega, J, hgood, ?_⟩
  rw [hcoefficient] at hcount
  exact hcount

end
end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralGlobalExactFirstMoment

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Every exact X-role part of a selected target label survives all ordered deletions. -/
theorem globalPartKeep_of_selected_X27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (g.perm r .X))
    (hjselected : j ∈ globalSelectedTargets27 g xi r B omega) :
    globalPartKeep g n xi r M B omega .zUseful (g.perm r .X) a.val := by
  let P := globalPopulation g n xi r
  let RP := rolePopulation P (g.perm r)
  let S := selected RP M B omega
  let matching := S.filter fun k =>
    globalCoarseContains g n xi r (g.perm r .X) k a.val
  have hjS : j.val ∈ S := by
    simpa only [S, RP, P, globalSelectedTargets27, Finset.mem_filter,
      Finset.mem_attach, true_and] using hjselected
  have hjcoarse := globalIncidence_coarseContains27 g xi r
    (g.perm r .X) j.val a.val a.property
  have hjmatching : j.val ∈ matching :=
    Finset.mem_filter.mpr ⟨hjS, hjcoarse⟩
  have hXY : g.perm r .X ≠ g.perm r .Y :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hXZ : g.perm r .X ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  unfold globalPartKeep
  dsimp only
  refine ⟨⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    exact ⟨j.val, hjmatching, a.property⟩
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXY h).elim
  · intro h
    exact (hXZ h).elim
  · intro h
    exact (hXZ h).elim
  · intro h
    exact (hXZ h).elim

/-- A selected target label has no deleted exact parts on its physical X role. -/
theorem globalExactHoles_X_eq_empty27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j : GlobalTargetLabel27 g xi r)
    (hjselected : j ∈ globalSelectedTargets27 g xi r B omega) :
    globalExactHoles27 g xi r B omega j (g.perm r .X) = ∅ := by
  ext a
  constructor
  · intro ha
    exact ((Finset.mem_filter.mp ha).2
      (globalPartKeep_of_selected_X27 g hg xi r B omega j a hjselected)).elim
  · simp

/-- The selected X-role hole event is empty for every nonnegative threshold. -/
theorem globalSelectedExactHoles_X_cond27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (j0 j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B) (t : ℝ) (ht : 0 ≤ t) :
    cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          t * (Fintype.card (GlobalExactPart27 g n xi r j0.val
            (g.perm r .X)) : ℝ) <
            ((globalExactHoles27 g xi r B omega j (g.perm r .X)).card : ℝ))) = 0 := by
  have hfilter :
      Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          t * (Fintype.card (GlobalExactPart27 g n xi r j0.val
            (g.perm r .X)) : ℝ) <
            ((globalExactHoles27 g xi r B omega j (g.perm r .X)).card : ℝ)) = ∅ := by
    ext omega
    by_cases hj : j ∈ globalSelectedTargets27 g xi r B omega
    · have hholes := globalExactHoles_X_eq_empty27 g hg xi r B omega j hj
      have hnonneg : 0 ≤ t *
          (Fintype.card (GlobalExactPart27 g n xi r j0.val (g.perm r .X)) : ℝ) :=
        mul_nonneg ht (Nat.cast_nonneg _)
      simp [hj, hholes, not_lt_of_ge hnonneg]
    · simp [hj]
  rw [hfilter]
  simp [cond]

/-- The selected targets satisfying all three paper hole thresholds. -/
def globalPaperGoodTargets27 {w b M : ℕ} (g : GlobalSpec w)
    (m : ℕ) (xi : ExactGrid g (b * m)) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g (b * m) xi r) M)
    (j0 : GlobalTargetLabel27 g xi r) : Finset (GlobalTargetLabel27 g xi r) :=
  (globalSelectedTargets27 g xi r B omega).filter fun j =>
    ∀ W, ((globalExactHoles27 g xi r B omega j W).card : ℝ) ≤
      (1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
        Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val W)

set_option maxHeartbeats 1000000 in
-- The dependent good-family conclusion requires extra elaboration time.
/--
The three paper gates assembled on one compatible exact grid: `3/4` target-bucket survival,
zero selected X holes, and the two `1/10` selected Y/Z first-moment tails leave `11/20` of the
bucket expectation.  The chosen hash outcome and every side remain inside the finite conclusion.
-/
theorem global_compatible_grid_good_family_paper27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (floor m : ℕ) (hm : 0 < m) (xi : ExactGrid g (b * m))
    (hxi : GridBoundaryCompatible xi) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (hb : 0 < b) (j0 : GlobalTargetLabel27 g xi r)
    (b0 : GlobalBucketLabel27 B) :
    ∃ omega : HashOutcome (globalPopulation g (b * m) xi r) M,
      (11 / 20 : ℝ) * Fintype.card (GlobalTargetLabel27 g xi r) *
          Fintype.card (GlobalBucketLabel27 B) / (M : ℝ)^2 ≤
        (globalPaperGoodTargets27 g m xi r B omega j0).card := by
  let t : Side → ℝ := fun _ => 1 / (8 * (w * (b * m) : ℕ))
  let debit : Side → ℝ := fun W => if W = g.perm r .X then 0 else 1 / 10
  have ht : ∀ W, 0 ≤ t W := by
    intro W
    dsimp only [t]
    positivity
  let e : Side ≃ Side := Equiv.ofBijective (g.perm r) (hg.roles.1 r)
  have hsum_perm : (∑ W, debit (g.perm r W)) = ∑ W, debit W := by
    simpa only [e, Equiv.ofBijective_apply] using Equiv.sum_comp e debit
  have hYX : g.perm r .Y ≠ g.perm r .X :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hZX : g.perm r .Z ≠ g.perm r .X :=
    (hg.roles.1 r).1.ne (by decide +kernel)
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
  have hsurvival : ∀ j bucketIndex, (3 : ℝ) / 4 ≤
      cond (globalTargetBucket27 g xi r B j bucketIndex)
        (Finset.univ.filter fun omega =>
          j ∈ globalSelectedTargets27 g xi r B omega) := by
    intro j bucketIndex
    exact globalTargetBucket_survival27 g hg floor m xi r B hprime hodd hfloor
      hdemand j bucketIndex
  have hfailure : ∀ j bucketIndex W,
      cond (globalTargetBucket27 g xi r B j bucketIndex)
        (Finset.univ.filter (fun omega =>
          j ∈ globalSelectedTargets27 g xi r B omega ∧
            t W * (Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val W) : ℝ) <
              ((globalExactHoles27 g xi r B omega j W).card : ℝ))) ≤ debit W := by
    intro j bucketIndex W
    obtain ⟨S, rfl⟩ := (hg.roles.1 r).2 W
    cases S with
    | X =>
        rw [globalSelectedExactHoles_X_cond27 g hg xi r B j0 j bucketIndex
          (t (g.perm r .X)) (ht (g.perm r .X))]
        simp [debit]
    | Y =>
        have h := globalSelectedExactHoles_paper_cond27 g hg hw floor m hm xi r B
          hprime hodd hfloor hdemand 0 j0 j bucketIndex hb
        simpa [t, debit, hYX, GlobalBridge25.side] using h
    | Z =>
        have h := globalSelectedExactHoles_paper_cond27 g hg hw floor m hm xi r B
          hprime hodd hfloor hdemand 1 j0 j bucketIndex hb
        simpa [t, debit, hZX, GlobalBridge25.side] using h
  obtain ⟨omega, homega⟩ := global_compatible_grid_good_family_selected27
    g hg xi hxi r B j0 b0 t ((3 : ℝ) / 4) debit ht hprime hodd hfloor
    hsurvival hfailure hmargin
  refine ⟨omega, ?_⟩
  rw [hcoefficient] at homega
  simpa [t, globalPaperGoodTargets27] using homega

end
end OmegaBound.ADVXXZGeneral
end

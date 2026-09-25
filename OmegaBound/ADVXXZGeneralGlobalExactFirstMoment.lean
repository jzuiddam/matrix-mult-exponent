import OmegaBound.ADVXXZGeneralGlobalExactMoments
import OmegaBound.ADVXXZGeneralGlobalPQ
import OmegaBound.ADVXXZGeneralPQExponentsParent25
import OmegaBound.ADVXXZGeneralGlobalExactRepairApplication

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

/-- Split a filtered cardinality into the fibres of a finite-valued map. -/
theorem global_card_filter_by_fibers27
    {I U A : Type*} [Fintype I] [Fintype U]
    [DecidableEq I] [DecidableEq U] [DecidableEq A]
    (f : I → U) (a : I → A) (P : U → Prop) [DecidablePred P] (x : A) :
    (Finset.univ.filter (fun i ↦ P (f i) ∧ a i = x)).card =
      ∑ u : U, if P u then
        (Finset.univ.filter (fun i ↦ f i = u ∧ a i = x)).card else 0 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f)
    (s := (Finset.univ : Finset I).filter (fun i ↦ P (f i) ∧ a i = x))
    (t := (Finset.univ : Finset U).filter P)]
  · simp only [Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro u _
    split
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      aesop
    · simp_all
  · intro i hi
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2.1⟩)

/-- Full global incidence implies physical coarse containment. -/
theorem globalIncidence_coarseContains27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Side)
    (j : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part W)
    (ha : (globalPopulation g n xi r).incidence W j a) :
    globalCoarseContains g n xi r W j a := by
  exact ha.1

/-- Every exact incident part has the grid's full physical empirical histogram. -/
theorem globalIncidence_empiricalLaw27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (W : Side)
    (j : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part W)
    (ha : (globalPopulation g n xi r).incidence W j a) :
    globalEmpiricalLaw g n xi r W a =
      fun sigma ↦ ∑ u : Shape w, xi.count W r u sigma := by
  funext sigma
  change typeCnt a sigma = _
  unfold typeCnt
  have hsplit := global_card_filter_by_fibers27 j.val a (fun _ ↦ True) sigma
  have hsplit' : (Finset.univ.filter (fun i ↦ a i = sigma)).card =
      ∑ u : Shape w,
        (Finset.univ.filter (fun i ↦ j.val i = u ∧ a i = sigma)).card := by
    simpa only [true_and, if_true] using hsplit
  rw [hsplit']
  apply Finset.sum_congr rfl
  intro u _
  exact ha.2 u sigma

/-- Full global incidence implies each of the paper's Y/Z compatibility tests. -/
theorem globalIncidence_compatible27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (ha : (globalPopulation g n xi r).incidence
      (GlobalBridge25.side g r which) j a) :
    globalCompatible g n xi r which j a := by
  unfold GlobalBridge25.side at a ha
  have hside : (if which = 0 then g.perm r .Y else g.perm r .Z) =
      g.perm r (if which = 0 then .Y else .Z) := by
    by_cases h : which = 0 <;> simp [h]
  unfold globalCompatible
  dsimp only
  constructor
  · intro u _hu sigma
    rw [hside]
    unfold globalCellCount
    exact Eq.trans (b := _) (by
      congr 1
      ext i
      simp) (ha.2 u sigma)
  · intro k sigma
    rw [hside]
    unfold globalCellCount
    have hsplit := global_card_filter_by_fibers27 j.val a
      (fun u ↦ coord (g.perm r (if which = 0 then .Y else .Z)) u = k.val) sigma
    calc
      _ = ∑ u : Shape w,
          if coord (g.perm r (if which = 0 then .Y else .Z)) u = k.val then
            (Finset.univ.filter (fun i ↦ j.val i = u ∧ a i = sigma)).card else 0 := by
              exact Eq.trans (b := _) (by
                congr 1
                ext i
                simp) (Eq.trans hsplit (by
                apply Finset.sum_congr rfl
                intro u _
                by_cases hu : coord (g.perm r (if which = 0 then .Y else .Z)) u = k.val
                · simp only [hu, if_true]
                · simp only [hu, if_false]))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : coord (g.perm r (if which = 0 then .Y else .Z)) u = k.val
        · simp only [hu, if_true]
          exact Eq.trans (b := _) (by congr 1) (ha.2 u sigma)
        · simp only [hu, if_false]

/-- The represented law carried by any exact incident Y/Z part. -/
noncomputable def globalExactRepresentedLaw27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    GlobalRepresentedLaw g n xi r which := by
  classical
  unfold GlobalBridge25.side at a
  let S := g.perm r (if which = 0 then .Y else .Z)
  let law := globalEmpiricalLaw g n xi r S a.val
  refine ⟨law, ?_⟩
  unfold globalLawFinset
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_image.mpr
    let z : GlobalLawSample g n xi r which := (j, a.val)
    refine ⟨z, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [S] using
      globalIncidence_coarseContains27 g xi r S j.val a.val a.property
  · intro sigma
    exact congrFun (globalIncidence_empiricalLaw27 g xi r S j.val a.val a.property) sigma

/-- Hole count gated by the event that the target label is actually selected. -/
def globalSelectedExactHoleCount27 {w n M : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j : GlobalTargetLabel27 g xi r) (W : Side) : ℕ :=
  if j ∈ globalSelectedTargets27 g xi r B omega then
    (globalExactHoles27 g xi r B omega j W).card else 0

set_option maxHeartbeats 1000000 in
-- The dependent exact-part cardinal makes this declaration expensive to elaborate.
theorem globalSelectedExactHoles_cond_le_of_sum27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (j0 j : GlobalTargetLabel27 g xi r) (bucketIndex : GlobalBucketLabel27 B)
    (W : Side) (t debit : ℝ)
    (hthreshold : 0 < t * Fintype.card (GlobalExactPart27 g n xi r j0.val W))
    (hmoment : ∑ omega ∈ globalTargetBucket27 g xi r B j bucketIndex,
        (globalSelectedExactHoleCount27 g xi r B omega j W : ℝ) ≤
      debit * (t * Fintype.card (GlobalExactPart27 g n xi r j0.val W)) *
        (globalTargetBucket27 g xi r B j bucketIndex).card) :
    cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          t * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
            ((globalExactHoles27 g xi r B omega j W).card : ℝ))) ≤ debit := by
  have hmarkov := conditional_nat_markov27
    (globalTargetBucket27 g xi r B j bucketIndex)
    (globalTargetBucket_nonempty27 g hg xi r B hprime hodd hfloor j bucketIndex)
    (fun omega => globalSelectedExactHoleCount27 g xi r B omega j W)
    (t * Fintype.card (GlobalExactPart27 g n xi r j0.val W)) debit hthreshold hmoment
  have hevent :
      (Finset.univ.filter (fun omega =>
        t * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
          (globalSelectedExactHoleCount27 g xi r B omega j W : ℝ))) =
      Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          t * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
            ((globalExactHoles27 g xi r B omega j W).card : ℝ)) := by
    ext omega
    by_cases hj : j ∈ globalSelectedTargets27 g xi r B omega
    · simp [globalSelectedExactHoleCount27, hj]
    · have hnlt : ¬ t * (Fintype.card
          (GlobalExactPart27 g n xi r j0.val W) : ℝ) < 0 :=
        not_lt_of_ge hthreshold.le
      simp [globalSelectedExactHoleCount27, hj, hnlt]
  rw [hevent] at hmarkov
  exact hmarkov

/--
The paper-faithful global good-family wrapper: first moments are charged only on outcomes where
the label is present.  Its conclusion is identical to the ungated wrapper because the final
filter already requires selection.
-/
theorem global_compatible_grid_good_family_selected27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g)
    (xi : ExactGrid g n) (_hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (B : Finset (ZMod M))
    (j0 : GlobalTargetLabel27 g xi r) (b0 : GlobalBucketLabel27 B)
    (t : Side → ℝ) (a : ℝ) (debit : Side → ℝ)
    (ht : ∀ W, 0 ≤ t W)
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (survival : ∀ j b, a ≤ cond (globalTargetBucket27 g xi r B j b)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega)))
    (failure : ∀ j b W, cond (globalTargetBucket27 g xi r B j b)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          t W * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
            ((globalExactHoles27 g xi r B omega j W).card : ℝ))) ≤ debit W)
    (margin : 0 < a - ∑ W, debit W) :
    ∃ omega : HashOutcome (globalPopulation g n xi r) M,
      (a - ∑ W, debit W) * Fintype.card (GlobalTargetLabel27 g xi r) *
          Fintype.card (GlobalBucketLabel27 B) / (M : ℝ)^2 ≤
        (((globalSelectedTargets27 g xi r B omega).filter (fun j =>
          ∀ W, ((globalExactHoles27 g xi r B omega j W).card : ℝ) ≤
            t W * Fintype.card (GlobalExactPart27 g n xi r j0.val W))).card : ℝ) := by
  letI : Nonempty (GlobalTargetLabel27 g xi r) := ⟨j0⟩
  letI : Nonempty (GlobalBucketLabel27 B) := ⟨b0⟩
  let hfun := fun omega (j : GlobalTargetLabel27 g xi r) W =>
    globalSelectedExactHoleCount27 g xi r B omega j W
  have hfailure : ∀ j b W, cond (globalTargetBucket27 g xi r B j b)
      (Finset.univ.filter (fun omega =>
        t W * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
          (hfun omega j W : ℝ))) ≤ debit W := by
    intro j b W
    have hevent :
        (Finset.univ.filter (fun omega =>
          t W * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
            (hfun omega j W : ℝ))) =
        Finset.univ.filter (fun omega =>
          j ∈ globalSelectedTargets27 g xi r B omega ∧
            t W * (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) <
              ((globalExactHoles27 g xi r B omega j W).card : ℝ)) := by
      ext omega
      by_cases hj : j ∈ globalSelectedTargets27 g xi r B omega
      · simp [hfun, globalSelectedExactHoleCount27, hj]
      · have hnonneg : 0 ≤ t W *
            (Fintype.card (GlobalExactPart27 g n xi r j0.val W) : ℝ) :=
          mul_nonneg (ht W) (Nat.cast_nonneg _)
        simp [hfun, globalSelectedExactHoleCount27, hj, not_lt_of_ge hnonneg]
    rw [hevent]
    exact failure j b W
  obtain ⟨omega, homega⟩ := exists_good_subfamily
    (globalTargetBucket27 g xi r B)
    (globalSelectedTargets27 g xi r B)
    hfun
    (fun W => Fintype.card (GlobalExactPart27 g n xi r j0.val W))
    t M hprime.pos a debit
    (fun j b => by exact_mod_cast
      globalTargetBucket_card27 g hg xi r B hprime hodd hfloor j b)
    (globalTargetBucket_pairwise27 g xi r B) survival hfailure margin
  refine ⟨omega, ?_⟩
  have hfilter :
      (globalSelectedTargets27 g xi r B omega).filter (fun j =>
        ∀ W, (hfun omega j W : ℝ) ≤
          t W * Fintype.card (GlobalExactPart27 g n xi r j0.val W)) =
      (globalSelectedTargets27 g xi r B omega).filter (fun j =>
        ∀ W, ((globalExactHoles27 g xi r B omega j W).card : ℝ) ≤
          t W * Fintype.card (GlobalExactPart27 g n xi r j0.val W)) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hall⟩
      refine ⟨hj, fun W => ?_⟩
      simpa [hfun, globalSelectedExactHoleCount27, hj] using hall W
    · rintro ⟨hj, hall⟩
      refine ⟨hj, fun W => ?_⟩
      simpa [hfun, globalSelectedExactHoleCount27, hj] using hall W
  rw [← hfilter]
  exact homega

/-- Compatible target rivals of one exact Y/Z part, excluding its owning label. -/
def globalExactRivals27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    Finset (globalPopulation g n xi r).Label :=
  (globalPopulation g n xi r).target.filter fun k =>
    k ≠ j.val ∧
      globalCoarseContains g n xi r (GlobalBridge25.side g r which) k a.val ∧
      globalCompatible g n xi r which k a.val

/-- Two labels containing the same physical part have equal role-side coarse words. -/
theorem globalRoleCoarse_eq_of_contains27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j k : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (hj : globalCoarseContains g n xi r (GlobalBridge25.side g r which) j a)
    (hk : globalCoarseContains g n xi r (GlobalBridge25.side g r which) k a) :
    (rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse j
        (if which = 0 then .Y else .Z) =
      (rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse k
        (if which = 0 then .Y else .Z) := by
  funext i
  apply Fin.ext
  unfold rolePopulation
  dsimp only
  unfold GlobalBridge25.side at a hj hk
  unfold globalPopulation
  dsimp only
  have hh := (hj i).symm.trans (hk i)
  generalize hS : g.perm r (if which = 0 then .Y else .Z) = S at hh ⊢
  cases S <;> simpa [coord] using hh

/-- A surviving label with one equal affine role hash lies in the owner's bucket. -/
theorem mem_bucket_of_survives_role_eq27 (P : RawPopulation) (M : ℕ) [NeZero M]
    (B : Finset (ZMod M)) (omega : HashOutcome P M) (j k : P.Label)
    (role : Side) (b : ZMod M) (hj : omega ∈ bucket P M j b)
    (hk : hashSurvives27 P M B omega k)
    (hcoarse : P.coarse j role = P.coarse k role) :
    omega ∈ bucket P M k b := by
  have hjhash := (mem_bucket_iff_hash27 P M j b omega).1 hj
  apply (mem_bucket_iff_hash27 P M k b omega).2
  rcases hk with ⟨hkXY, hkYZ, _⟩
  cases role with
  | X =>
      have heq : hashX27 P M omega j = hashX27 P M omega k := by
        unfold hashX27
        rw [hcoarse]
      have hkX : hashX27 P M omega k = b := heq.symm.trans hjhash.1
      exact ⟨hkX, hkXY.symm.trans hkX, hkYZ.symm.trans (hkXY.symm.trans hkX)⟩
  | Y =>
      have heq : hashY27 P M omega j = hashY27 P M omega k := by
        unfold hashY27
        rw [hcoarse]
      have hkY : hashY27 P M omega k = b := heq.symm.trans hjhash.2.1
      exact ⟨hkXY.trans hkY, hkY, hkYZ.symm.trans hkY⟩
  | Z =>
      have heq : hashZ27 P M omega j = hashZ27 P M omega k := by
        unfold hashZ27
        rw [hcoarse]
      have hkZ : hashZ27 P M omega k = b := heq.symm.trans hjhash.2.2
      exact ⟨hkXY.trans (hkYZ.trans hkZ), hkYZ.trans hkZ, hkZ⟩

/-- A selected exact Y/Z part survives whenever it has no other selected compatible label. -/
theorem globalPartKeep_of_selected_no_rivals27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (which : Fin 2) (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which))
    (hjselected : j ∈ globalSelectedTargets27 g xi r B omega)
    (hno : ∀ k ∈ globalExactRivals27 g xi r which j a,
      k ∉ selected (rolePopulation (globalPopulation g n xi r) (g.perm r)) M B omega) :
    globalPartKeep g n xi r M B omega .zUseful
      (GlobalBridge25.side g r which) a.val := by
  let P := globalPopulation g n xi r
  let RP := rolePopulation P (g.perm r)
  let S := selected RP M B omega
  have hjS : j.val ∈ S := by
    simpa only [S, RP, P, globalSelectedTargets27, Finset.mem_filter,
      Finset.mem_attach, true_and] using hjselected
  have hjcoarse := globalIncidence_coarseContains27 g xi r
    (GlobalBridge25.side g r which) j.val a.val a.property
  have hjcompat := globalIncidence_compatible27 g xi r which j.val a.val a.property
  fin_cases which
  · let matching := S.filter fun k =>
      globalCoarseContains g n xi r (g.perm r .Y) k a.val
    let ys := matching.filter fun k => globalCompatible g n xi r 0 k a.val
    let zs := matching.filter fun k => globalCompatible g n xi r 1 k a.val
    have hjmatching : j.val ∈ matching :=
      Finset.mem_filter.mpr ⟨hjS, by simpa [GlobalBridge25.side] using hjcoarse⟩
    have hjys : j.val ∈ ys :=
      Finset.mem_filter.mpr ⟨hjmatching, by simpa using hjcompat⟩
    have hys : ys = {j.val} := by
      ext k
      constructor
      · intro hk
        have hkmatching := (Finset.mem_filter.mp hk).1
        have hkS := (Finset.mem_filter.mp hkmatching).1
        by_cases hkj : k = j.val
        · simpa [hkj]
        · exfalso
          have hktarget := (mem_selected_iff_hashSurvives27 RP M B omega k).mp hkS |>.1
          have hkR : k ∈ globalExactRivals27 g xi r 0 j a := by
            apply Finset.mem_filter.mpr
            exact ⟨hktarget, hkj,
              (Finset.mem_filter.mp hkmatching).2, (Finset.mem_filter.mp hk).2⟩
          exact hno k hkR hkS
      · intro hk
        simpa only [Finset.mem_singleton.mp hk] using hjys
    have hycard : ys.card = 1 := by simp [hys]
    have hYX : g.perm r .Y ≠ g.perm r .X :=
      (hg.roles.1 r).1.ne (by decide +kernel)
    have hYZ : g.perm r .Y ≠ g.perm r .Z :=
      (hg.roles.1 r).1.ne (by decide +kernel)
    unfold globalPartKeep
    dsimp only
    refine ⟨⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact (hYX h).elim
    · intro _
      exact ⟨j.val, hjys⟩
    · intro _
      simpa [matching, ys, GlobalBridge25.side] using hycard
    · intro _
      exact ⟨j.val, hjys, a.property⟩
    · intro h
      exact (hYZ h).elim
    · intro h
      exact (hYZ h).elim
    · intro h
      exact (hYZ h).elim
  · let matching := S.filter fun k =>
      globalCoarseContains g n xi r (g.perm r .Z) k a.val
    let ys := matching.filter fun k => globalCompatible g n xi r 0 k a.val
    let zs := matching.filter fun k => globalCompatible g n xi r 1 k a.val
    have hjmatching : j.val ∈ matching :=
      Finset.mem_filter.mpr ⟨hjS, by simpa [GlobalBridge25.side] using hjcoarse⟩
    have hjzs : j.val ∈ zs :=
      Finset.mem_filter.mpr ⟨hjmatching, by simpa using hjcompat⟩
    have hzs : zs = {j.val} := by
      ext k
      constructor
      · intro hk
        have hkmatching := (Finset.mem_filter.mp hk).1
        have hkS := (Finset.mem_filter.mp hkmatching).1
        by_cases hkj : k = j.val
        · simpa [hkj]
        · exfalso
          have hktarget := (mem_selected_iff_hashSurvives27 RP M B omega k).mp hkS |>.1
          have hkR : k ∈ globalExactRivals27 g xi r 1 j a := by
            apply Finset.mem_filter.mpr
            exact ⟨hktarget, hkj,
              (Finset.mem_filter.mp hkmatching).2, (Finset.mem_filter.mp hk).2⟩
          exact hno k hkR hkS
      · intro hk
        simpa only [Finset.mem_singleton.mp hk] using hjzs
    have hzcard : zs.card = 1 := by simp [hzs]
    have hZX : g.perm r .Z ≠ g.perm r .X :=
      (hg.roles.1 r).1.ne (by decide +kernel)
    have hZY : g.perm r .Z ≠ g.perm r .Y :=
      (hg.roles.1 r).1.ne (by decide +kernel)
    unfold globalPartKeep
    dsimp only
    refine ⟨⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact (hZX h).elim
    · intro h
      exact (hZY h).elim
    · intro h
      exact (hZY h).elim
    · intro h
      exact (hZY h).elim
    · intro _
      exact ⟨j.val, hjzs⟩
    · intro _
      simpa [matching, zs, GlobalBridge25.side] using hzcard
    · intro _
      exact ⟨j.val, hjzs, a.property⟩

/-- A selected-label hole is covered by the bucket of a compatible rival. -/
theorem globalSelectedExactHole_mem_rivalBuckets27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (which : Fin 2) (j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which))
    (homega : omega ∈ globalTargetBucket27 g xi r B j bucketIndex)
    (hjselected : j ∈ globalSelectedTargets27 g xi r B omega)
    (hahole : a ∈ globalExactHoles27 g xi r B omega j
      (GlobalBridge25.side g r which)) :
    omega ∈ (globalExactRivals27 g xi r which j a).biUnion (fun k =>
      bucket (rolePopulation (globalPopulation g n xi r) (g.perm r)) M k bucketIndex.val) := by
  let P := globalPopulation g n xi r
  let RP := rolePopulation P (g.perm r)
  by_contra hcover
  have hno : ∀ k ∈ globalExactRivals27 g xi r which j a, k ∉ selected RP M B omega := by
    intro k hkR hkS
    have hkdata := (Finset.mem_filter.mp hkR).2
    have hksurv := (mem_selected_iff_hashSurvives27 RP M B omega k).mp hkS |>.2.1
    have hcoarse := globalRoleCoarse_eq_of_contains27 g xi r which j.val k a.val
      (globalIncidence_coarseContains27 g xi r (GlobalBridge25.side g r which)
        j.val a.val a.property) hkdata.2.1
    have hjbucket : omega ∈ bucket RP M j.val bucketIndex.val := by
      exact homega
    have hkbucket := mem_bucket_of_survives_role_eq27 RP M B omega j.val k
      (if which = 0 then .Y else .Z) bucketIndex.val hjbucket hksurv hcoarse
    apply hcover
    exact Finset.mem_biUnion.mpr ⟨k, hkR, hkbucket⟩
  have hkeep := globalPartKeep_of_selected_no_rivals27 g hg xi r B omega which j a
    hjselected hno
  exact (Finset.mem_filter.mp hahole).2 hkeep

private theorem div_eq_inv_of_mul_eq27 (x e m : ℝ) (he : 0 < e) (hm : 0 < m)
    (h : x * m = e) : x / e = 1 / m := by
  have hx : x = e / m := (eq_div_iff hm.ne').2 h
  rw [hx]
  field_simp

set_option maxHeartbeats 1000000 in
-- The dependent exact-part event makes this declaration expensive to elaborate.
theorem globalSelectedExactPart_cond_le_rivals27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (which : Fin 2) (j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          a ∈ globalExactHoles27 g xi r B omega j
            (GlobalBridge25.side g r which))) ≤
      ((globalExactRivals27 g xi r which j a).card : ℝ) / M := by
  let P := globalPopulation g n xi r
  let RP := rolePopulation P (g.perm r)
  let E := globalTargetBucket27 g xi r B j bucketIndex
  let rivals := globalExactRivals27 g xi r which j a
  let hits : P.Label → Finset (HashOutcome P M) := fun k => bucket RP M k bucketIndex.val
  have hE : E.Nonempty :=
    globalTargetBucket_nonempty27 g hg xi r B hprime hodd hfloor j bucketIndex
  have hpair : ∀ k ∈ rivals, cond E (hits k) ≤ 1 / (M : ℝ) := by
    intro k hk
    have hkdata := (Finset.mem_filter.mp hk).2
    have hcoarse := globalRoleCoarse_eq_of_contains27 g xi r which j.val k a.val
      (globalIncidence_coarseContains27 g xi r (GlobalBridge25.side g r which)
        j.val a.val a.property) hkdata.2.1
    have hcardNat := (asymmetric_hash RP (global_role_tight27 g hg xi r)
      (global_role_coarse_injective27 g hg xi r) M hprime hodd hfloor).2
        j.val k hkdata.1.symm (if which = 0 then .Y else .Z) hcoarse bucketIndex.val
    have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
    have hcardReal : (((E ∩ hits k).card : ℕ) : ℝ) * (M : ℝ) = E.card := by
      exact_mod_cast hcardNat
    unfold cond
    exact (div_eq_inv_of_mul_eq27 _ _ _ hEreal hMreal hcardReal).le
  have hunion := conditional_collision_union E hE rivals hits M hprime.pos hpair
  have hsub : E ∩ (Finset.univ.filter (fun omega =>
      j ∈ globalSelectedTargets27 g xi r B omega ∧
        a ∈ globalExactHoles27 g xi r B omega j
          (GlobalBridge25.side g r which))) ⊆ E ∩ rivals.biUnion hits := by
    intro omega homega
    have hdata := Finset.mem_inter.mp homega
    have hevent := (Finset.mem_filter.mp hdata.2).2
    exact Finset.mem_inter.mpr ⟨hdata.1,
      globalSelectedExactHole_mem_rivalBuckets27 g hg xi r B omega which j bucketIndex a
        hdata.1 hevent.1 hevent.2⟩
  calc
    cond E (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          a ∈ globalExactHoles27 g xi r B omega j
            (GlobalBridge25.side g r which))) ≤
        cond E (rivals.biUnion hits) := by
          unfold cond
          gcongr
    _ ≤ ((rivals.card : ℝ) / M) := hunion

/-- Finite double-counting for a family of predicates. -/
theorem sum_card_filter_comm27 {Omega A : Type*} [Fintype A]
    [DecidableEq Omega] [DecidableEq A] (E : Finset Omega) (p : Omega → A → Prop)
    [∀ omega a, Decidable (p omega a)] :
    ∑ omega ∈ E, ((Finset.univ.filter fun a => p omega a).card : ℝ) =
      ∑ a : A, ((E.filter fun omega => p omega a).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_comm]

set_option maxHeartbeats 1000000 in
-- The statement contains two dependent exact-part sums and needs extra elaboration time.
theorem globalSelectedExactHoles_sum_le_rivals27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (which : Fin 2) (j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B) :
    ∑ omega ∈ globalTargetBucket27 g xi r B j bucketIndex,
        (globalSelectedExactHoleCount27 g xi r B omega j
          (GlobalBridge25.side g r which) : ℝ) ≤
      ∑ a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which),
        ((globalExactRivals27 g xi r which j a).card : ℝ) / M *
          (globalTargetBucket27 g xi r B j bucketIndex).card := by
  let E := globalTargetBucket27 g xi r B j bucketIndex
  let A := GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)
  let event := fun omega (a : A) =>
    j ∈ globalSelectedTargets27 g xi r B omega ∧
      a ∈ globalExactHoles27 g xi r B omega j (GlobalBridge25.side g r which)
  have hcount (omega : HashOutcome (globalPopulation g n xi r) M) :
      (globalSelectedExactHoleCount27 g xi r B omega j
        (GlobalBridge25.side g r which) : ℝ) =
      ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
    by_cases hj : j ∈ globalSelectedTargets27 g xi r B omega
    · simp [globalSelectedExactHoleCount27, event, hj, globalExactHoles27, A]
    · simp [globalSelectedExactHoleCount27, event, hj]
  calc
    ∑ omega ∈ E, (globalSelectedExactHoleCount27 g xi r B omega j
        (GlobalBridge25.side g r which) : ℝ) =
        ∑ omega ∈ E, ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro omega _
          exact hcount omega
    _ = ∑ a : A, ((E.filter fun omega => event omega a).card : ℝ) :=
      sum_card_filter_comm27 E event
    _ ≤ ∑ a : A, ((globalExactRivals27 g xi r which j a).card : ℝ) / M * E.card := by
      apply Finset.sum_le_sum
      intro a _
      have hcond := globalSelectedExactPart_cond_le_rivals27 g hg xi r B hprime hodd
        hfloor which j bucketIndex a
      have hE : E.Nonempty :=
        globalTargetBucket_nonempty27 g hg xi r B hprime hodd hfloor j bucketIndex
      have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
      have hfilter : (E.filter fun omega => event omega a) =
          E ∩ (Finset.univ.filter fun omega => event omega a) := by
        ext omega
        simp
      rw [hfilter]
      apply (div_le_iff₀ hEreal).mp
      simpa only [E, event, cond] using hcond

/-- Target labels whose physical coarse word contains a given Y/Z fine part. -/
def globalContainingTargets27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which)) :
    Finset (globalPopulation g n xi r).Label :=
  (globalPopulation g n xi r).target.filter fun j =>
    globalCoarseContains g n xi r (GlobalBridge25.side g r which) j a

/-- Target labels compatible with a given Y/Z fine part. -/
def globalCompatibleTargets27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which)) :
    Finset (globalPopulation g n xi r).Label :=
  (globalPopulation g n xi r).target.filter fun j =>
    globalCoarseContains g n xi r (GlobalBridge25.side g r which) j a ∧
      globalCompatible g n xi r which j a

private theorem filter_card_eq_of_permFM27 {I : Type*} [Fintype I]
    [DecidableEq I] (e : Equiv.Perm I) (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij' (fun i _ => e i) (fun i _ => e.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (h i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (h (e.symm i)).mpr (by simpa using (Finset.mem_filter.mp hi).2)
  · intro i _
    exact e.symm_apply_apply i
  · intro i _
    exact e.apply_symm_apply i

private theorem exists_perm_of_typeCntFM27
    {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (x y : Fin n → A) (h : ∀ a, typeCnt x a = typeCnt y a) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, y (e i) = x i := by
  obtain ⟨e⟩ : Nonempty (∀ a : A, {i // x i = a} ≃ {i // y i = a}) :=
    ⟨fun a => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)⟩
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), fun i => ?_⟩
  exact (e (x i) ⟨i, rfl⟩).2

set_option maxHeartbeats 1000000 in
-- The dependent target-label permutation needs extra elaboration time.
private noncomputable def globalTargetLabelPermFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n)) :
    {j // j ∈ (globalPopulation g n xi r).target} ≃
      {j // j ∈ (globalPopulation g n xi r).target} := by
  classical
  unfold globalPopulation at e ⊢
  dsimp only
  refine
    { toFun := fun j => ⟨⟨fun i => j.val.val (e.symm i), ?_⟩, ?_⟩
      invFun := fun j => ⟨⟨fun i => j.val.val (e i), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro W a
    cases W with
    | X => exact ((filter_card_eq_of_permFM27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .X a))
    | Y => exact ((filter_card_eq_of_permFM27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .Y a))
    | Z => exact ((filter_card_eq_of_permFM27 e.symm _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .Z a))
  · apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_univ]
    intro u
    exact (filter_card_eq_of_permFM27 e.symm _ _ (fun _ => Iff.rfl)).trans
      ((Finset.mem_filter.mp j.property).2 u)
  · intro W a
    cases W with
    | X => exact ((filter_card_eq_of_permFM27 e _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .X a))
    | Y => exact ((filter_card_eq_of_permFM27 e _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .Y a))
    | Z => exact ((filter_card_eq_of_permFM27 e _ _ (fun _ => Iff.rfl)).trans
        (j.val.property .Z a))
  · apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_univ]
    intro u
    exact (filter_card_eq_of_permFM27 e _ _ (fun _ => Iff.rfl)).trans
      ((Finset.mem_filter.mp j.property).2 u)
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp

set_option maxHeartbeats 1000000 in
-- This computation rule unfolds the dependent target-label equivalence once.
private theorem globalTargetLabelPermFM27_apply {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (j : {j // j ∈ (globalPopulation g n xi r).target}) (i : Fin _) :
    ((globalTargetLabelPermFM27 g xi r e) j).val.val (e i) = j.val.val i := by
  classical
  change j.val.val (e.symm (e i)) = j.val.val i
  simp

private theorem target_filter_card_eq_of_equivFM27 {A : Type*} [DecidableEq A]
    (S : Finset A) (e : {x // x ∈ S} ≃ {x // x ∈ S})
    (P Q : A → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x.val ↔ Q (e x).val) :
    (S.filter P).card = (S.filter Q).card := by
  refine Finset.card_bij'
    (fun x hx => (e ⟨x, (Finset.mem_filter.mp hx).1⟩).val)
    (fun x hx => (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h ⟨x, (Finset.mem_filter.mp hx).1⟩).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩).property,
      (h (e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩)).mpr (by
        simpa using (Finset.mem_filter.mp hx).2)⟩
  · intro x hx
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)
  · intro x hx
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)

private theorem globalCoarseContains_permFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n xi r).Part S)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    globalCoarseContains g n xi r S j.val x ↔
      globalCoarseContains g n xi r S (globalTargetLabelPermFM27 g xi r e j).val y := by
  unfold globalCoarseContains
  constructor
  · intro h k
    have hy : y k = x (e.symm k) := by simpa using he (e.symm k)
    have hj := globalTargetLabelPermFM27_apply g xi r e j (e.symm k)
    simpa [hy] using (h (e.symm k)).trans (congrArg (coord S) hj.symm)
  · intro h i
    have hi := h (e i)
    rw [he i, globalTargetLabelPermFM27_apply g xi r e j i] at hi
    exact hi

private theorem globalCellCount_permFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (S : Side)
    (x y : (globalPopulation g n xi r).Part S)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n xi r).target})
    (cell : Shape w → Prop) (sigma : Chunk w) :
    globalCellCount g n xi r S j.val x cell sigma =
      globalCellCount g n xi r S (globalTargetLabelPermFM27 g xi r e j).val y cell sigma := by
  classical
  unfold globalCellCount
  exact filter_card_eq_of_permFM27 e _ _ (fun i => by
    rw [he i, globalTargetLabelPermFM27_apply g xi r e j i])

private theorem globalCompatible_permFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (x y : (globalPopulation g n xi r).Part
      (g.perm r (if which = 0 then .Y else .Z)))
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (he : ∀ i, y (e i) = x i)
    (j : {j // j ∈ (globalPopulation g n xi r).target}) :
    globalCompatible g n xi r which j.val x ↔
      globalCompatible g n xi r which (globalTargetLabelPermFM27 g xi r e j).val y := by
  unfold globalCompatible
  dsimp only
  constructor
  · rintro ⟨hboundary, hresidual⟩
    constructor
    · intro u hu sigma
      calc
        _ = globalCellCount g n xi r (g.perm r (if which = 0 then .Y else .Z))
            j.val x (fun v => v = u) sigma := by
          symm
          exact globalCellCount_permFM27 g xi r _ x y e he j _ _
        _ = _ := hboundary u hu sigma
    · intro k sigma
      calc
        _ = globalCellCount g n xi r (g.perm r (if which = 0 then .Y else .Z))
            j.val x
              (fun u => coord (if which = 0 then g.perm r .Y else g.perm r .Z) u = k.val)
              sigma := by
          symm
          exact globalCellCount_permFM27 g xi r _ x y e he j _ _
        _ = _ := hresidual k sigma
  · rintro ⟨hboundary, hresidual⟩
    constructor
    · intro u hu sigma
      calc
        _ = globalCellCount g n xi r (g.perm r (if which = 0 then .Y else .Z))
            (globalTargetLabelPermFM27 g xi r e j).val y (fun v => v = u) sigma :=
          globalCellCount_permFM27 g xi r _ x y e he j _ _
        _ = _ := hboundary u hu sigma
    · intro k sigma
      calc
        _ = globalCellCount g n xi r (g.perm r (if which = 0 then .Y else .Z))
            (globalTargetLabelPermFM27 g xi r e j).val y
              (fun u => coord (if which = 0 then g.perm r .Y else g.perm r .Z) u = k.val)
              sigma := globalCellCount_permFM27 g xi r _ x y e he j _ _
        _ = _ := hresidual k sigma

private theorem global_exists_perm_of_empirical_eqFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (x y : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (hxy : globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) x =
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) y) :
    ∃ e : Equiv.Perm (Fin (globalPopulation g n xi r).n), ∀ i, y (e i) = x i := by
  apply exists_perm_of_typeCntFM27 x y
  intro sigma
  exact congrFun hxy sigma

/-- Containing-target cardinality depends only on the fine empirical law. -/
theorem globalContainingTargets_card_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (x y : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (hxy : globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) x =
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) y) :
    (globalContainingTargets27 g xi r which x).card =
      (globalContainingTargets27 g xi r which y).card := by
  classical
  obtain ⟨e, he⟩ := global_exists_perm_of_empirical_eqFM27 g xi r which x y hxy
  unfold globalContainingTargets27
  exact target_filter_card_eq_of_equivFM27 (globalPopulation g n xi r).target
    (globalTargetLabelPermFM27 g xi r e)
    (fun j => globalCoarseContains g n xi r (GlobalBridge25.side g r which) j x)
    (fun j => globalCoarseContains g n xi r (GlobalBridge25.side g r which) j y)
    (globalCoarseContains_permFM27 g xi r _ x y e he)

/-- Compatible-target cardinality depends only on the fine empirical law. -/
theorem globalCompatibleTargets_card_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (x y : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (hxy : globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) x =
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) y) :
    (globalCompatibleTargets27 g xi r which x).card =
      (globalCompatibleTargets27 g xi r which y).card := by
  classical
  obtain ⟨e, he⟩ := global_exists_perm_of_empirical_eqFM27 g xi r which x y hxy
  unfold globalCompatibleTargets27
  exact target_filter_card_eq_of_equivFM27 (globalPopulation g n xi r).target
    (globalTargetLabelPermFM27 g xi r e)
    (fun j => globalCoarseContains g n xi r (GlobalBridge25.side g r which) j x ∧
      globalCompatible g n xi r which j x)
    (fun j => globalCoarseContains g n xi r (GlobalBridge25.side g r which) j y ∧
      globalCompatible g n xi r which j y)
    (fun j => and_congr (globalCoarseContains_permFM27 g xi r _ x y e he j)
      (globalCompatible_permFM27 g xi r which x y e he j))

private theorem globalLawSamples_nonemptyFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    (globalLawSamples g n xi r which beta).Nonempty := by
  have hmem := (Finset.mem_filter.mp beta.property).1
  rcases Finset.mem_image.mp hmem with ⟨z, hz, heq⟩
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩

private theorem globalFirstLawSample_memFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    globalFirstLawSample g n xi r which beta ∈ globalLawSamples g n xi r which beta := by
  classical
  let candidates := globalLawSamples g n xi r which beta
  have hcandidates : candidates.Nonempty := globalLawSamples_nonemptyFM27 g xi r which beta
  let e := Fintype.equivFin (GlobalLawSample g n xi r which)
  letI := LinearOrder.lift' e e.injective
  change candidates.min' hcandidates ∈ candidates
  exact Finset.min'_mem _ _

/-- The representative `globalPcomp` is the compatible/containing ratio at an exact part. -/
theorem globalPcomp_eq_exact_ratio27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    globalPcomp g n xi r which (globalExactRepresentedLaw27 g xi r which j a) =
      ((globalCompatibleTargets27 g xi r which a.val).card : ℝ) /
        (globalContainingTargets27 g xi r which a.val).card := by
  classical
  let beta := globalExactRepresentedLaw27 g xi r which j a
  let first := (globalFirstLawSample g n xi r which beta).2
  have hmem := globalFirstLawSample_memFM27 g xi r which beta
  have hfirst : globalEmpiricalLaw g n xi r
      (g.perm r (if which = 0 then .Y else .Z)) first = beta.val :=
    (Finset.mem_filter.mp hmem).2
  have hxy : globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) first =
      globalEmpiricalLaw g n xi r (GlobalBridge25.side g r which) a.val := by
    calc
      _ = beta.val := by simpa [GlobalBridge25.side] using hfirst
      _ = _ := by rfl
  have hcont := globalContainingTargets_card_eq27 g xi r which first a.val hxy
  have hcompat := globalCompatibleTargets_card_eq27 g xi r which first a.val hxy
  unfold globalPcomp
  dsimp only
  rw [Finset.filter_filter]
  change ((globalCompatibleTargets27 g xi r which first).card : ℝ) /
      (globalContainingTargets27 g xi r which first).card = _
  rw [hcont, hcompat]

/-- Every represented global compatibility ratio is below `globalPcompMax`. -/
theorem globalPcomp_le_max27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g n xi r which) :
    globalPcomp g n xi r which beta ≤ globalPcompMax g n xi r which := by
  classical
  unfold globalPcompMax
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g n xi r which)).image
    (globalPcomp g n xi r which)
  have hmem : globalPcomp g n xi r which beta ∈ values :=
    Finset.mem_image.mpr ⟨beta, Finset.mem_univ _, rfl⟩
  have hvalues : values.Nonempty := ⟨_, hmem⟩
  rw [dif_pos hvalues]
  exact Finset.le_max' values _ hmem

/-- Compatible rivals of an exact part obey the `globalPcompMax` cardinal bound. -/
theorem globalExactRivals_card_le_pcompMax27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    ((globalExactRivals27 g xi r which j a).card : ℝ) ≤
      globalPcompMax g n xi r which *
        (globalContainingTargets27 g xi r which a.val).card := by
  have hjcont : j.val ∈ globalContainingTargets27 g xi r which a.val := by
    apply Finset.mem_filter.mpr
    exact ⟨j.property, globalIncidence_coarseContains27 g xi r
      (GlobalBridge25.side g r which) j.val a.val a.property⟩
  have hcontReal : 0 < ((globalContainingTargets27 g xi r which a.val).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨j.val, hjcont⟩
  have hrsub : globalExactRivals27 g xi r which j a ⊆
      globalCompatibleTargets27 g xi r which a.val := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, h.2⟩
  have hcard : ((globalExactRivals27 g xi r which j a).card : ℝ) ≤
      (globalCompatibleTargets27 g xi r which a.val).card := by
    exact_mod_cast Finset.card_le_card hrsub
  have hpcomp := globalPcomp_le_max27 g xi r which
    (globalExactRepresentedLaw27 g xi r which j a)
  rw [globalPcomp_eq_exact_ratio27 g xi r which j a] at hpcomp
  have hcompat : ((globalCompatibleTargets27 g xi r which a.val).card : ℝ) ≤
      globalPcompMax g n xi r which *
        (globalContainingTargets27 g xi r which a.val).card :=
    (div_le_iff₀ hcontReal).mp hpcomp
  exact hcard.trans hcompat

private theorem globalLabel_coarse_typeCnt_eqFM27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (j k : (globalPopulation g n xi r).Label) (W : Side)
    (a : Fin ((globalPopulation g n xi r).grade + 1)) :
    typeCnt ((globalPopulation g n xi r).coarse j W) a =
      typeCnt ((globalPopulation g n xi r).coarse k W) a := by
  classical
  unfold globalPopulation at j k ⊢
  dsimp only at j k ⊢
  exact (j.property W a).trans (k.property W a).symm

set_option maxHeartbeats 1000000 in
-- This computation rule unfolds the dependent target permutation once.
private theorem globalTargetLabelPermFM27_coarse {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6)
    (e : Equiv.Perm (Fin (globalPopulation g n xi r).n))
    (j : {j // j ∈ (globalPopulation g n xi r).target}) (W : Side) (i : Fin _) :
    (globalPopulation g n xi r).coarse (globalTargetLabelPermFM27 g xi r e j).val W i =
      (globalPopulation g n xi r).coarse j.val W (e.symm i) := by
  classical
  unfold globalPopulation globalTargetLabelPermFM27
  rfl

/-- The target-label fibre over one physical role-side coarse word. -/
def globalRoleTargetFiber27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : (globalPopulation g n xi r).Label) :
    Finset (globalPopulation g n xi r).Label :=
  (globalPopulation g n xi r).target.filter fun k =>
    (globalPopulation g n xi r).coarse k (GlobalBridge25.side g r which) =
      (globalPopulation g n xi r).coarse j (GlobalBridge25.side g r which)

/-- All raw global role-side coarse words. -/
def globalRoleCoarseImage27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    Finset (Fin (globalPopulation g n xi r).n →
      Fin ((globalPopulation g n xi r).grade + 1)) :=
  (Finset.univ : Finset (globalPopulation g n xi r).Label).image fun k =>
    (globalPopulation g n xi r).coarse k (GlobalBridge25.side g r which)

/-- Role-side coarse words represented by target labels. -/
def globalRoleTargetCoarseImage27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2) :
    Finset (Fin (globalPopulation g n xi r).n →
      Fin ((globalPopulation g n xi r).grade + 1)) :=
  (globalPopulation g n xi r).target.image fun k =>
    (globalPopulation g n xi r).coarse k (GlobalBridge25.side g r which)

/-- Target fibres have equal cardinality over all represented role-side coarse words. -/
theorem globalRoleTargetFiber_card_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j k : GlobalTargetLabel27 g xi r) :
    (globalRoleTargetFiber27 g xi r which j.val).card =
      (globalRoleTargetFiber27 g xi r which k.val).card := by
  classical
  let P := globalPopulation g n xi r
  let W := GlobalBridge25.side g r which
  obtain ⟨e, he⟩ := exists_perm_of_typeCntFM27 (P.coarse j.val W) (P.coarse k.val W)
    (fun a => globalLabel_coarse_typeCnt_eqFM27 g xi r j.val k.val W a)
  let phi := globalTargetLabelPermFM27 g xi r e
  unfold globalRoleTargetFiber27
  apply target_filter_card_eq_of_equivFM27 P.target phi
  intro l
  change P.coarse l.val W = P.coarse j.val W ↔
    P.coarse (phi l).val W = P.coarse k.val W
  constructor
  · intro hl
    funext i
    rw [globalTargetLabelPermFM27_coarse g xi r e l W i, congrFun hl (e.symm i)]
    simpa using (he (e.symm i)).symm
  · intro hl
    funext i
    have hi := congrFun hl (e i)
    rw [globalTargetLabelPermFM27_coarse g xi r e l W (e i)] at hi
    have hi' := hi.trans (he i)
    rw [e.symm_apply_apply] at hi'
    exact hi'

/-- Every raw role-side coarse word is represented by a target label. -/
theorem globalRoleTargetCoarseImage_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r) :
    globalRoleTargetCoarseImage27 g xi r which =
      globalRoleCoarseImage27 g xi r which := by
  classical
  let P := globalPopulation g n xi r
  let W := GlobalBridge25.side g r which
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · intro x hx
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he⟩ := exists_perm_of_typeCntFM27 (P.coarse j.val W) (P.coarse k W)
      (fun a => globalLabel_coarse_typeCnt_eqFM27 g xi r j.val k W a)
    let phi := globalTargetLabelPermFM27 g xi r e
    have hcoarse : P.coarse (phi j).val W = P.coarse k W := by
      funext i
      rw [globalTargetLabelPermFM27_coarse g xi r e j W i]
      simpa using (he (e.symm i)).symm
    exact Finset.mem_image.mpr ⟨(phi j).val, (phi j).property, hcoarse⟩

/-- Uniform target fibres partition the target-label set. -/
theorem globalRoleTargetFiber_mul_image27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r) :
    (globalRoleTargetFiber27 g xi r which j.val).card *
        (globalRoleCoarseImage27 g xi r which).card =
      (globalPopulation g n xi r).target.card := by
  classical
  let P := globalPopulation g n xi r
  let W := GlobalBridge25.side g r which
  let image := globalRoleTargetCoarseImage27 g xi r which
  have hpartition : P.target.card = ∑ x ∈ image,
      (P.target.filter fun k => P.coarse k W = x).card := by
    simpa only using (Finset.card_eq_sum_card_fiberwise
      (s := P.target) (t := image) (f := fun k => P.coarse k W)
      (fun k hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩))
  rw [← globalRoleTargetCoarseImage_eq27 g xi r which j]
  calc
    (globalRoleTargetFiber27 g xi r which j.val).card * image.card =
        ∑ _x ∈ image, (globalRoleTargetFiber27 g xi r which j.val).card := by
          simp [Nat.mul_comm]
    _ = ∑ x ∈ image, (P.target.filter fun k => P.coarse k W = x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
      subst x
      exact globalRoleTargetFiber_card_eq27 g xi r which j ⟨k, hk⟩
    _ = P.target.card := hpartition.symm

/-- Equal role-side coarse words preserve physical containment of a fixed part. -/
theorem globalCoarseContains_of_roleCoarse_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j k : (globalPopulation g n xi r).Label)
    (a : (globalPopulation g n xi r).Part (GlobalBridge25.side g r which))
    (hj : globalCoarseContains g n xi r (GlobalBridge25.side g r which) j a)
    (hcoarse : (rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse j
        (if which = 0 then .Y else .Z) =
      (rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse k
        (if which = 0 then .Y else .Z)) :
    globalCoarseContains g n xi r (GlobalBridge25.side g r which) k a := by
  intro i
  have hc := congrArg Fin.val (congrFun hcoarse i)
  have hj' := hj i
  unfold rolePopulation at hc
  dsimp only at hc
  unfold GlobalBridge25.side at a hj' ⊢
  unfold globalPopulation at hc
  dsimp only at hc
  generalize hS : g.perm r (if which = 0 then .Y else .Z) = S at hc hj' ⊢
  cases S <;> simpa [coord] using hj'.trans hc

/-- An exact part's containing targets are precisely its owner's target coarse fibre. -/
theorem globalContainingTargets_eq_roleFiber27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    globalContainingTargets27 g xi r which a.val =
      globalRoleTargetFiber27 g xi r which j.val := by
  ext k
  simp only [globalContainingTargets27, globalRoleTargetFiber27, Finset.mem_filter]
  constructor
  · rintro ⟨hktarget, hkcontains⟩
    exact ⟨hktarget, (globalRoleCoarse_eq_of_contains27 g xi r which j.val k a.val
      (globalIncidence_coarseContains27 g xi r (GlobalBridge25.side g r which)
        j.val a.val a.property) hkcontains).symm⟩
  · rintro ⟨hktarget, hkcoarse⟩
    exact ⟨hktarget, globalCoarseContains_of_roleCoarse_eq27 g xi r which j.val k a.val
      (globalIncidence_coarseContains27 g xi r (GlobalBridge25.side g r which)
        j.val a.val a.property) hkcoarse.symm⟩

/-- Exact containing-target cardinality times the represented coarse count is the target count. -/
theorem globalExactContaining_mul_image27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (j : GlobalTargetLabel27 g xi r)
    (a : GlobalExactPart27 g n xi r j.val (GlobalBridge25.side g r which)) :
    (globalContainingTargets27 g xi r which a.val).card *
        (globalRoleCoarseImage27 g xi r which).card =
      (globalPopulation g n xi r).target.card := by
  rw [globalContainingTargets_eq_roleFiber27 g xi r which j a]
  exact globalRoleTargetFiber_mul_image27 g xi r which j

/-- The Y/Z ceiling used by `globalDemand` dominates the corresponding exact-grid term. -/
theorem globalDemand_role_ceiling_le27 {w b : ℕ} (g : GlobalSpec w)
    (floor m : ℕ) (xi : ExactGrid g (b * m)) (r : Fin 6) (which : Fin 2) :
    Nat.ceil (((80 * (w * (b * m)) : ℕ) : ℝ) *
      (globalPopulation g (b * m) xi r).target.card *
      globalPcompMax g (b * m) xi r which /
      (globalRoleCoarseImage27 g xi r which).card) ≤
        globalDemand g b floor m xi r := by
  classical
  let P := globalPopulation g (b * m) xi r
  let NX := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .X)).card
  let NY := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Y)).card
  let NZ := ((Finset.univ : Finset P.Label).image fun k => P.coarse k (g.perm r .Z)).card
  fin_cases which
  · unfold globalDemand natural_demand
    dsimp only
    change Nat.ceil (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
      globalPcompMax g (b * m) xi r 0 / NY) ≤
        max (max floor (2 * w + 3))
          (max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX))
            (max (if NY = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 0 / NY))
              (if NZ = 0 then 0 else Nat.ceil
                (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                  globalPcompMax g (b * m) xi r 1 / NZ))))
    by_cases hNY : NY = 0
    · simp [hNY]
    · calc
        _ = if NY = 0 then 0 else Nat.ceil
            (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
              globalPcompMax g (b * m) xi r 0 / NY) := by simp [hNY]
        _ ≤ max (if NY = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 0 / NY))
            (if NZ = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 1 / NZ)) := le_max_left _ _
        _ ≤ max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX)) _ :=
          le_max_right _ _
        _ ≤ max (max floor (2 * w + 3)) _ := le_max_right _ _
  · unfold globalDemand natural_demand
    dsimp only
    change Nat.ceil (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
      globalPcompMax g (b * m) xi r 1 / NZ) ≤
        max (max floor (2 * w + 3))
          (max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX))
            (max (if NY = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 0 / NY))
              (if NZ = 0 then 0 else Nat.ceil
                (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                  globalPcompMax g (b * m) xi r 1 / NZ))))
    by_cases hNZ : NZ = 0
    · simp [hNZ]
    · calc
        _ = if NZ = 0 then 0 else Nat.ceil
            (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
              globalPcompMax g (b * m) xi r 1 / NZ) := by simp [hNZ]
        _ ≤ max (if NY = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 0 / NY))
            (if NZ = 0 then 0 else Nat.ceil
              (((80 * (w * (b * m)) : ℕ) : ℝ) * P.target.card *
                globalPcompMax g (b * m) xi r 1 / NZ)) := le_max_right _ _
        _ ≤ max (if NX = 0 then 0 else Nat.ceil (8 * (Fintype.card P.Label : ℝ) / NX)) _ :=
          le_max_right _ _
        _ ≤ max (max floor (2 * w + 3)) _ := le_max_right _ _

private theorem rival_ratio_from_demand27 (rival containing image target H p demand M : ℝ)
    (himage : 0 < image) (hH : 0 < H) (hM : 0 < M)
    (hrival : rival ≤ p * containing) (hcount : containing * image = target)
    (hdemand : H * target * p / image ≤ demand)
    (hmodulus : 2 * demand ≤ M) :
    rival / M ≤ 1 / (2 * H) := by
  have hrival' : rival * image ≤ p * target := by
    calc
      rival * image ≤ (p * containing) * image :=
        mul_le_mul_of_nonneg_right hrival himage.le
      _ = p * (containing * image) := by ring
      _ = p * target := by rw [hcount]
  have hrivalH : H * (rival * image) ≤ H * (p * target) :=
    mul_le_mul_of_nonneg_left hrival' hH.le
  have hdemand' : H * target * p ≤ demand * image :=
    (div_le_iff₀ himage).mp hdemand
  have hmodulus' : 2 * demand * image ≤ M * image :=
    mul_le_mul_of_nonneg_right hmodulus himage.le
  have hcross : (2 * H * rival) * image ≤ M * image := by
    calc
      (2 * H * rival) * image = 2 * (H * (rival * image)) := by ring
      _ ≤ 2 * (H * (p * target)) := by gcongr
      _ = 2 * (H * target * p) := by ring
      _ ≤ 2 * (demand * image) := by gcongr
      _ = 2 * demand * image := by ring
      _ ≤ M * image := hmodulus'
  have hsmall : 2 * H * rival ≤ M := by
    nlinarith [hcross]
  apply (div_le_div_iff₀ hM (mul_pos (by norm_num) hH)).2
  nlinarith

private theorem half_global_hole_debit27 (A E L : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hL : 0 < L) :
    A * (1 / (2 * (80 * L)) * E) ≤
      (1 / 10) * (1 / (8 * L) * A) * E := by
  field_simp
  nlinarith

set_option maxHeartbeats 1000000 in
-- The dependent exact-part sum and literal global demand require extra elaboration time.
theorem globalSelectedExactHoles_paper_moment27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (floor m : ℕ) (hm : 0 < m) (xi : ExactGrid g (b * m))
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (which : Fin 2) (j0 j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B) (hb : 0 < b) :
    ∑ omega ∈ globalTargetBucket27 g xi r B j bucketIndex,
        (globalSelectedExactHoleCount27 g xi r B omega j
          (GlobalBridge25.side g r which) : ℝ) ≤
      (1 / 10 : ℝ) *
        ((1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
          Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
            (GlobalBridge25.side g r which))) *
        (globalTargetBucket27 g xi r B j bucketIndex).card := by
  let P := globalPopulation g (b * m) xi r
  let image := globalRoleCoarseImage27 g xi r which
  let H : ℝ := (80 * (w * (b * m)) : ℕ)
  let E := globalTargetBucket27 g xi r B j bucketIndex
  have hbase := globalSelectedExactHoles_sum_le_rivals27 g hg xi r B hprime hodd
    hfloor which j bucketIndex
  have himage : 0 < (image.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨P.coarse j.val (GlobalBridge25.side g r which),
      Finset.mem_image.mpr ⟨j.val, Finset.mem_univ _, rfl⟩⟩
  have hH : 0 < H := by
    dsimp only [H]
    positivity
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
  have hdemandReal : (2 : ℝ) * globalDemand g b floor m xi r ≤ M := by
    exact_mod_cast hdemand
  have hceil := globalDemand_role_ceiling_le27 g floor m xi r which
  let demandTerm : ℝ := H * P.target.card * globalPcompMax g (b * m) xi r which /
    image.card
  have hdemandTerm : demandTerm ≤ globalDemand g b floor m xi r := by
    have hleceil : demandTerm ≤ Nat.ceil demandTerm := Nat.le_ceil demandTerm
    have hceil' : Nat.ceil demandTerm ≤ globalDemand g b floor m xi r := by
      simpa [demandTerm, H, P, image] using hceil
    have hceilReal : ((Nat.ceil demandTerm : ℕ) : ℝ) ≤
        globalDemand g b floor m xi r := by
      exact_mod_cast hceil'
    exact hleceil.trans hceilReal
  have hpart (a : GlobalExactPart27 g (b * m) xi r j.val
      (GlobalBridge25.side g r which)) :
      ((globalExactRivals27 g xi r which j a).card : ℝ) / M ≤ 1 / (2 * H) := by
    have hrival := globalExactRivals_card_le_pcompMax27 g xi r which j a
    have hcountNat := globalExactContaining_mul_image27 g xi r which j a
    have hcountReal : ((globalContainingTargets27 g xi r which a.val).card : ℝ) *
        image.card = P.target.card := by
      exact_mod_cast hcountNat
    exact rival_ratio_from_demand27 _ _ _ _ _ _ _ _ himage hH hMreal hrival
      hcountReal hdemandTerm hdemandReal
  have hsum :
      ∑ a : GlobalExactPart27 g (b * m) xi r j.val (GlobalBridge25.side g r which),
          ((globalExactRivals27 g xi r which j a).card : ℝ) / M * E.card ≤
        ∑ _a : GlobalExactPart27 g (b * m) xi r j.val (GlobalBridge25.side g r which),
          (1 / (2 * H)) * E.card := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_right (hpart a) (Nat.cast_nonneg _)
  have hcard : Fintype.card (GlobalExactPart27 g (b * m) xi r j.val
      (GlobalBridge25.side g r which)) =
      Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
        (GlobalBridge25.side g r which)) :=
    Fintype.card_congr (globalLabelExactPartEquiv27 0 g xi r j.val j0.val
      j.property j0.property (GlobalBridge25.side g r which))
  calc
    _ ≤ ∑ a : GlobalExactPart27 g (b * m) xi r j.val
        (GlobalBridge25.side g r which),
          ((globalExactRivals27 g xi r which j a).card : ℝ) / M * E.card := hbase
    _ ≤ ∑ _a : GlobalExactPart27 g (b * m) xi r j.val
        (GlobalBridge25.side g r which), (1 / (2 * H)) * E.card := hsum
    _ = (Fintype.card (GlobalExactPart27 g (b * m) xi r j.val
          (GlobalBridge25.side g r which)) : ℝ) * ((1 / (2 * H)) * E.card) := by simp
    _ = (Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
          (GlobalBridge25.side g r which)) : ℝ) * ((1 / (2 * H)) * E.card) := by rw [hcard]
    _ ≤ (1 / 10 : ℝ) *
        ((1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
          Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
            (GlobalBridge25.side g r which))) * E.card := by
      have hL : 0 < ((w * (b * m) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hw (Nat.mul_pos hb hm)
      have hdebit := half_global_hole_debit27
        (Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
          (GlobalBridge25.side g r which)) : ℝ)
        (E.card : ℝ) ((w * (b * m) : ℕ) : ℝ)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hL
      simpa [H] using hdebit

/-- The selected Y/Z hole tail has the paper debit once the exact-part threshold is nonzero. -/
theorem globalSelectedExactHoles_paper_cond27 {w b M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hw : 0 < w)
    (floor m : ℕ) (hm : 0 < m) (xi : ExactGrid g (b * m))
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g (b * m) xi r).grade < M)
    (hdemand : 2 * globalDemand g b floor m xi r ≤ M)
    (which : Fin 2) (j0 j : GlobalTargetLabel27 g xi r)
    (bucketIndex : GlobalBucketLabel27 B) (hb : 0 < b) :
    cond (globalTargetBucket27 g xi r B j bucketIndex)
      (Finset.univ.filter (fun omega =>
        j ∈ globalSelectedTargets27 g xi r B omega ∧
          (1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
              Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
                (GlobalBridge25.side g r which)) <
            ((globalExactHoles27 g xi r B omega j
              (GlobalBridge25.side g r which)).card : ℝ))) ≤ (1 / 10 : ℝ) := by
  have hcardNat : 0 < Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
      (GlobalBridge25.side g r which)) :=
    Fintype.card_pos_iff.mpr
      (globalExactPart_nonempty27 0 g xi r j0.val j0.property
        (GlobalBridge25.side g r which))
  have hcard : 0 < (Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
      (GlobalBridge25.side g r which)) : ℝ) := by
    exact_mod_cast hcardNat
  have hthreshold : 0 < (1 / (8 * (w * (b * m) : ℕ)) : ℝ) *
      Fintype.card (GlobalExactPart27 g (b * m) xi r j0.val
        (GlobalBridge25.side g r which)) := by
    have hlength : 0 < ((w * (b * m) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hw (Nat.mul_pos hb hm)
    positivity
  apply globalSelectedExactHoles_cond_le_of_sum27 g hg xi r B hprime hodd hfloor
    j0 j bucketIndex (GlobalBridge25.side g r which)
    (1 / (8 * (w * (b * m) : ℕ))) (1 / 10) hthreshold
  exact globalSelectedExactHoles_paper_moment27 g hg hw floor m hm xi r B hprime hodd
    hfloor hdemand which j0 j bucketIndex hb

end
end OmegaBound.ADVXXZGeneral
end

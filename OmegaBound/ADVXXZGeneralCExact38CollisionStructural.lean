import OmegaBound.ADVXXZGeneralCExact38InputReserve
import OmegaBound.ADVXXZGeneralActiveEmbeddingsContinuation
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

/- The orbit module already proved the exact coordinate characterization of a stage role
coarse fibre.  Expose that kernel-checked private helper under this module's public name. -/
open Lean Elab Command in
private def findOrbitPrivate38 (env : Environment) (suffix : String) : CommandElabM Name := do
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    if name.toString.contains "_private.OmegaBound.ADVXXZGeneralCExact37Orbit." ∧
        name.toString.endsWith suffix then acc.push name else acc
  if h : names.size = 1 then return names[0]
  else throwError "expected one orbit declaration ending in '{suffix}', found {names.size}"

open Lean Elab Command in
elab "expose_orbit38 " id:ident " := " suffix:str : command => do
  let env ← getEnv
  let oldName ← findOrbitPrivate38 env suffix.getString
  let newName := (← getCurrNamespace) ++ id.getId
  let some info := env.find? oldName | throwError "orbit declaration vanished"
  let value := mkConst oldName (info.levelParams.map Level.param)
  match info with
  | .thmInfo d => liftCoreM <| addDecl <| .thmDecl {
      name := newName, levelParams := d.levelParams, type := d.type, value }
  | _ => throwError "expected theorem for {oldName}"

expose_orbit38 stage_role_coarse_eq_iff_coords38 :=
  ".OmegaBound.ADVXXZGeneral.stage_role_coarse_eq_iff_coords37"

/-- The amended hole set is a filter of the exact-part set. -/
theorem holesAt25_subset_exactPartsAt38 {w s : ℕ} (q b m M : ℕ) (epsilon : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : (stagePopulationAt q p d b m r).Label) (W : Side) :
    holesAt25 q b m M epsilon p d r B omega j W ⊆
      exactPartsAt q b m p d r j W := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

/-- Compatible target rivals of one exact constituent Y/Z part, excluding its owner. -/
def stageExactRivals38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which)) :
    Finset (stagePopulationAt q p d b m r).Label :=
  (stagePopulationAt q p d b m r).target.filter fun k =>
    k ≠ j.val ∧ Parent25.contains p d b m r which k a.val ∧
      Parent25.compatible p d b m r which k a.val

/-- Two labels containing the same physical constituent part have equal role-side coarse words. -/
theorem stageRoleCoarse_eq_of_contains38 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (which : Fin 2) (j k : (stagePopulationAt q p d b m r).Label)
    (a : (stagePopulationAt q p d b m r).Part (Parent25.side d r which))
    (hj : Parent25.contains p d b m r which j a)
    (hk : Parent25.contains p d b m r which k a) :
    (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j
        (if which = 0 then .Y else .Z) =
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse k
      (if which = 0 then .Y else .Z) := by
  apply (stage_role_coarse_eq_iff_coords38 q p d r j k
    (if which = 0 then .Y else .Z)).2
  intro z
  simpa only [Parent25.side] using (hj z).symm.trans (hk z)

set_option maxHeartbeats 2000000 in
-- Normalizing the two dependent physical-role cases needs extra elaboration time.
/-- A selected input-typical exact Y/Z part survives if it has no selected rival. -/
theorem stagePartKeep_of_selected_no_rivals38 {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which))
    (hinput : Parent25.inputPartKeep p d b m epsilon r
      (Parent25.side d r which) a.val)
    (hjselected : j ∈ stageSelectedTargets37 q p d r B omega)
    (hno : ∀ k ∈ stageExactRivals38 q p d r which j a,
      k ∉ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
        M B omega) :
    stagePartKeepAt25 q b m M epsilon p d r B omega .zUseful
      (Parent25.side d r which) a.val := by
  let P := stagePopulationAt q p d b m r
  let RP := rolePopulation P (d.perm r)
  let S := selected RP M B omega
  have hjS : j.val ∈ S := by
    simpa only [S, RP, P, stageSelectedTargets37, Finset.mem_filter,
      Finset.mem_attach, true_and] using hjselected
  have hinc : P.incidence (Parent25.side d r which) j.val a.val := by
    simpa only [P, exactPartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] using a.property
  have hjcoarse : Parent25.contains p d b m r which j.val a.val := by
    simpa only [Parent25.contains, Parent25.side] using hinc.1
  have hjcompat : Parent25.compatible p d b m r which j.val a.val :=
    (embedding_compatible_iff_parent25 q b m p d r which j.val a.val).mp
      (embedding_incidence_compatible q b m p d r which j.val a.val hinc)
  fin_cases which
  · let matching := S.filter fun k =>
      Parent25.containsSide p d b m r (d.perm r .Y) k a.val
    let ys := matching.filter fun k => Parent25.compatible p d b m r 0 k a.val
    have hjmatching : j.val ∈ matching :=
      Finset.mem_filter.mpr ⟨hjS, by
        simpa [Parent25.contains, Parent25.containsSide, Parent25.side] using hjcoarse⟩
    have hjys : j.val ∈ ys := Finset.mem_filter.mpr ⟨hjmatching, hjcompat⟩
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
          have hkR : k ∈ stageExactRivals38 q p d r 0 j a := by
            apply Finset.mem_filter.mpr
            exact ⟨hktarget, hkj,
              by simpa [Parent25.contains, Parent25.containsSide, Parent25.side] using
                (Finset.mem_filter.mp hkmatching).2,
              (Finset.mem_filter.mp hk).2⟩
          exact hno k hkR hkS
      · intro hk
        simpa only [Finset.mem_singleton.mp hk] using hjys
    have hycard : ys.card = 1 := by simp [hys]
    have hYX : d.perm r .Y ≠ d.perm r .X :=
      (hd.roles.1 r).1.ne (by decide +kernel)
    have hYZ : d.perm r .Y ≠ d.perm r .Z :=
      (hd.roles.1 r).1.ne (by decide +kernel)
    unfold stagePartKeepAt25
    dsimp only
    refine ⟨hinput, ⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact (hYX h).elim
    · intro _
      exact ⟨j.val, hjys⟩
    · intro _
      simpa [matching, ys, Parent25.side] using hycard
    · intro _
      exact ⟨j.val, hjys, hinc⟩
    · intro h
      exact (hYZ h).elim
    · intro h
      exact (hYZ h).elim
    · intro h
      exact (hYZ h).elim
  · let matching := S.filter fun k =>
      Parent25.containsSide p d b m r (d.perm r .Z) k a.val
    let zs := matching.filter fun k => Parent25.compatible p d b m r 1 k a.val
    have hjmatching : j.val ∈ matching :=
      Finset.mem_filter.mpr ⟨hjS, by
        simpa [Parent25.contains, Parent25.containsSide, Parent25.side] using hjcoarse⟩
    have hjzs : j.val ∈ zs := Finset.mem_filter.mpr ⟨hjmatching, hjcompat⟩
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
          have hkR : k ∈ stageExactRivals38 q p d r 1 j a := by
            apply Finset.mem_filter.mpr
            exact ⟨hktarget, hkj,
              by simpa [Parent25.contains, Parent25.containsSide, Parent25.side] using
                (Finset.mem_filter.mp hkmatching).2,
              (Finset.mem_filter.mp hk).2⟩
          exact hno k hkR hkS
      · intro hk
        simpa only [Finset.mem_singleton.mp hk] using hjzs
    have hzcard : zs.card = 1 := by simp [hzs]
    have hZX : d.perm r .Z ≠ d.perm r .X :=
      (hd.roles.1 r).1.ne (by decide +kernel)
    have hZY : d.perm r .Z ≠ d.perm r .Y :=
      (hd.roles.1 r).1.ne (by decide +kernel)
    unfold stagePartKeepAt25
    dsimp only
    refine ⟨hinput, ⟨j.val, hjmatching⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      simpa [matching, zs, Parent25.side] using hzcard
    · intro _
      exact ⟨j.val, hjzs, hinc⟩

/-- An input-typical selected hole is covered by a compatible rival bucket. -/
theorem stageSelectedExactHole_mem_rivalBuckets38 {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which))
    (homega : omega ∈ stageTargetBucket37 q p d r B j z)
    (hjselected : j ∈ stageSelectedTargets37 q p d r B omega)
    (hinput : Parent25.inputPartKeep p d b m epsilon r
      (Parent25.side d r which) a.val)
    (hahole : a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
      (Parent25.side d r which)) :
    omega ∈ (stageExactRivals38 q p d r which j a).biUnion fun k =>
      bucket (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
        M k z.val := by
  let P := stagePopulationAt q p d b m r
  let RP := rolePopulation P (d.perm r)
  have hinc : P.incidence (Parent25.side d r which) j.val a.val := by
    simpa only [P, exactPartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] using a.property
  by_contra hcover
  have hno : ∀ k ∈ stageExactRivals38 q p d r which j a,
      k ∉ selected RP M B omega := by
    intro k hkR hkS
    have hkdata := (Finset.mem_filter.mp hkR).2
    have hksurv := (mem_selected_iff_hashSurvives27 RP M B omega k).mp hkS |>.2.1
    have hcoarse := stageRoleCoarse_eq_of_contains38 q p d r which j.val k a.val
      (by simpa only [Parent25.contains, Parent25.side] using hinc.1) hkdata.2.1
    have hjbucket : omega ∈ bucket RP M j.val z.val := homega
    have hkbucket := mem_bucket_of_survives_role_eq27 RP M B omega j.val k
      (if which = 0 then .Y else .Z) z.val hjbucket hksurv hcoarse
    apply hcover
    exact Finset.mem_biUnion.mpr ⟨k, hkR, hkbucket⟩
  have hkeep := stagePartKeep_of_selected_no_rivals38 q p d hd epsilon r B omega
    which j a hinput hjselected hno
  exact (Finset.mem_filter.mp hahole).2 hkeep

set_option maxHeartbeats 1000000 in
-- The dependent exact-part event and affine collision fibre need extra elaboration time.
/-- Conditional collision probability for one fixed input-typical exact part. -/
theorem stageSelectedExactPart_cond_le_rivals38 {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B)
    (a : StageExactPart27 q b m p d r j.val (Parent25.side d r which))
    (hinput : Parent25.inputPartKeep p d b m epsilon r
      (Parent25.side d r which) a.val) :
    cond (stageTargetBucket37 q p d r B j z)
      (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
            (Parent25.side d r which)) ≤
      ((stageExactRivals38 q p d r which j a).card : ℝ) / M := by
  let P := stagePopulationAt q p d b m r
  let RP := rolePopulation P (d.perm r)
  let E := stageTargetBucket37 q p d r B j z
  let rivals := stageExactRivals38 q p d r which j a
  let hits : P.Label → Finset (HashOutcome P M) := fun k => bucket RP M k z.val
  have hinc : P.incidence (Parent25.side d r which) j.val a.val := by
    simpa only [P, exactPartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] using a.property
  have hE : E.Nonempty := stageTargetBucket_nonempty37 q p d hd r B hprime hodd hfloor j z
  have hpair : ∀ k ∈ rivals, cond E (hits k) ≤ 1 / (M : ℝ) := by
    intro k hk
    have hkdata := (Finset.mem_filter.mp hk).2
    have hcoarse := stageRoleCoarse_eq_of_contains38 q p d r which j.val k a.val
      (by simpa only [Parent25.contains, Parent25.side] using hinc.1) hkdata.2.1
    have hcardNat := (asymmetric_hash RP (stage_role_tight37 q p d hd r)
      (stage_role_coarse_injective37 q p d hd r) M hprime hodd hfloor).2
        j.val k hkdata.1.symm (if which = 0 then .Y else .Z) hcoarse z.val
    have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hprime.pos
    have hcardReal : (((E ∩ hits k).card : ℕ) : ℝ) * (M : ℝ) = E.card := by
      exact_mod_cast hcardNat
    unfold cond
    have hx : (((E ∩ hits k).card : ℕ) : ℝ) = (E.card : ℝ) / M :=
      (eq_div_iff hMreal.ne').2 hcardReal
    rw [hx]
    field_simp
    norm_num
  have hunion := conditional_collision_union E hE rivals hits M hprime.pos hpair
  have hsub : E ∩ (Finset.univ.filter fun omega =>
      j ∈ stageSelectedTargets37 q p d r B omega ∧
        a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
          (Parent25.side d r which)) ⊆ E ∩ rivals.biUnion hits := by
    intro omega homega
    have hdata := Finset.mem_inter.mp homega
    have hevent := (Finset.mem_filter.mp hdata.2).2
    exact Finset.mem_inter.mpr ⟨hdata.1,
      stageSelectedExactHole_mem_rivalBuckets38 q p d hd epsilon r B omega which j z a
        hdata.1 hevent.1 hinput hevent.2⟩
  calc
    cond E (Finset.univ.filter fun omega =>
        j ∈ stageSelectedTargets37 q p d r B omega ∧
          a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
            (Parent25.side d r which)) ≤ cond E (rivals.biUnion hits) := by
      unfold cond
      gcongr
    _ ≤ ((rivals.card : ℝ) / M) := hunion

/-- Selected input-typical collision holes, gated by owner selection. -/
def stageSelectedCollisionHoleCount38 {w s b m M : ℕ} (q : ℕ) (epsilon : ℚ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M))
    (omega : HashOutcome (stagePopulationAt q p d b m r) M)
    (j : StageTargetLabel37 q p d b m r) (which : Fin 2) : ℕ :=
  if j ∈ stageSelectedTargets37 q p d r B omega then
    ((holesAt25 q b m M epsilon p d r B omega j.val
      (Parent25.side d r which)).filter fun a =>
        Parent25.inputPartKeep p d b m epsilon r
          (Parent25.side d r which) a).card else 0

set_option maxHeartbeats 1000000 in
-- Double-counting two dependent exact-part sums needs extra elaboration time.
/-- Sum of selected collision holes is bounded by the sum of per-part rival probabilities. -/
theorem stageSelectedCollisionHoles_sum_le_rivals38 {w s b m M : ℕ} [NeZero M]
    (q : ℕ) (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (epsilon : ℚ) (r : Fin 6)
    (B : Finset (ZMod M)) (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (which : Fin 2) (j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B) :
    ∑ omega ∈ stageTargetBucket37 q p d r B j z,
        (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) ≤
      ∑ a : StageExactPart27 q b m p d r j.val (Parent25.side d r which),
        ((stageExactRivals38 q p d r which j a).card : ℝ) / M *
          (stageTargetBucket37 q p d r B j z).card := by
  let E := stageTargetBucket37 q p d r B j z
  let A := StageExactPart27 q b m p d r j.val (Parent25.side d r which)
  let event := fun omega (a : A) =>
    j ∈ stageSelectedTargets37 q p d r B omega ∧
      Parent25.inputPartKeep p d b m epsilon r (Parent25.side d r which) a.val ∧
      a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
        (Parent25.side d r which)
  have hcount (omega : HashOutcome (stagePopulationAt q p d b m r) M) :
      (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) =
        ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
    by_cases hj : j ∈ stageSelectedTargets37 q p d r B omega
    · let H := holesAt25 q b m M epsilon p d r B omega j.val
        (Parent25.side d r which)
      let good : (stagePopulationAt q p d b m r).Part
          (Parent25.side d r which) → Prop := fun a =>
        Parent25.inputPartKeep p d b m epsilon r (Parent25.side d r which) a
      let e : {a : A // good a.val ∧ a.val ∈ H} ≃ ↥(H.filter good) :=
        { toFun := fun a => ⟨a.val.val,
            Finset.mem_filter.mpr ⟨a.property.2, a.property.1⟩⟩
          invFun := fun a => ⟨⟨a.val, (holesAt25_subset_exactPartsAt38 q b m M epsilon
              p d r B omega j.val (Parent25.side d r which))
                (by simpa only [H] using (Finset.mem_filter.mp a.property).1)⟩,
            (Finset.mem_filter.mp a.property).2,
            (Finset.mem_filter.mp a.property).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hcard : (H.filter good).card =
          (Finset.univ.filter fun a : A => good a.val ∧ a.val ∈ H).card := by
        calc
          (H.filter good).card = Fintype.card ↥(H.filter good) :=
            (Fintype.card_coe _).symm
          _ = Fintype.card {a : A // good a.val ∧ a.val ∈ H} :=
            (Fintype.card_congr e).symm
          _ = (Finset.univ.filter fun a : A => good a.val ∧ a.val ∈ H).card := by
            rw [Fintype.card_subtype]
      exact_mod_cast (by simpa [stageSelectedCollisionHoleCount38, event, hj, H, good]
        using hcard)
    · simp [stageSelectedCollisionHoleCount38, event, hj]
  calc
    ∑ omega ∈ E,
        (stageSelectedCollisionHoleCount38 q epsilon p d r B omega j which : ℝ) =
      ∑ omega ∈ E, ((Finset.univ.filter fun a : A => event omega a).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro omega _
        exact hcount omega
    _ = ∑ a : A, ((E.filter fun omega => event omega a).card : ℝ) :=
      sum_card_filter_comm27 E event
    _ ≤ ∑ a : A, ((stageExactRivals38 q p d r which j a).card : ℝ) / M * E.card := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hi : Parent25.inputPartKeep p d b m epsilon r
          (Parent25.side d r which) a.val
      · have hcond' := stageSelectedExactPart_cond_le_rivals38 q p d hd epsilon r B
          hprime hodd hfloor which j z a hi
        have hE : E.Nonempty :=
          stageTargetBucket_nonempty37 q p d hd r B hprime hodd hfloor j z
        have hEreal : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
        have hfilter : (E.filter fun omega => event omega a) =
            E ∩ (Finset.univ.filter fun omega =>
              j ∈ stageSelectedTargets37 q p d r B omega ∧
                a.val ∈ holesAt25 q b m M epsilon p d r B omega j.val
                  (Parent25.side d r which)) := by
          ext omega
          simp [event, hi]
        rw [hfilter]
        apply (div_le_iff₀ hEreal).mp
        simpa only [E, cond] using hcond'
      · have hempty : (E.filter fun omega => event omega a) = ∅ := by
          ext omega
          simp [event, hi]
        rw [hempty]
        simp
        positivity

end
end OmegaBound.ADVXXZGeneral
end

import OmegaBound.ADVXXZGeneralCExact33Population
import OmegaBound.ADVXXZGeneralGlobalExactMoments

set_option autoImplicit false
noncomputable section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

abbrev StageTargetLabel37 {w s : ℕ} (q : ℕ) (p : ConstituentInput w s)
    (d : ConstituentSpec p) (b m : ℕ) (r : Fin 6) :=
  {j : (stagePopulationAt q p d b m r).Label //
    j ∈ (stagePopulationAt q p d b m r).target}

abbrev StageBucketLabel37 {M : ℕ} (B : Finset (ZMod M)) :=
  {z : ZMod M // z ∈ B}

def stageTargetBucket37 {w s b m M : ℕ} [NeZero M] (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (j : StageTargetLabel37 q p d b m r)
    (z : StageBucketLabel37 B) :
    Finset (HashOutcome (stagePopulationAt q p d b m r) M) :=
  bucket (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)) M j.val z.val

def stageSelectedTargets37 {w s b m M : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (omega : HashOutcome (stagePopulationAt q p d b m r) M) :
    Finset (StageTargetLabel37 q p d b m r) :=
  (stagePopulationAt q p d b m r).target.attach.filter fun j =>
    j.val ∈ selected (rolePopulation (stagePopulationAt q p d b m r) (d.perm r))
      M B omega

set_option maxHeartbeats 2000000 in
-- The dependent stage-position equivalence and the six role cases need extra elaboration time.
theorem stage_role_tight37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (i : Fin (stagePopulationAt q p d b m r).n) :
    ∑ W, (((rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse j W i).val) =
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).grade := by
  letI : Fintype (StageCandidateRaw.StagePos b m p d r) := Fintype.ofFinite _
  dsimp [rolePopulation, stagePopulationAt] at j i ⊢
  let u := j.val ((Fintype.equivFin
    (StageCandidateRaw.StagePos b m p d r)).symm i)
  let e : Side ≃ Side := Equiv.ofBijective (d.perm r) (hd.roles.1 r)
  have he := Equiv.sum_comp e (fun W => coord W u.val)
  have hside : (Finset.univ : Finset Side) = {.X, .Y, .Z} := by decide +kernel
  have hplain : (∑ W, coord W u.val) = 2*w := by
    rw [hside]
    simpa [coord, add_assoc] using u.val.property
  have hh := he.trans hplain
  rw [hside] at hh ⊢
  dsimp only [e, Equiv.ofBijective_apply] at hh
  dsimp [u] at hh
  have hXY : d.perm r .X ≠ d.perm r .Y :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hXZ : d.perm r .X ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  have hYZ : d.perm r .Y ≠ d.perm r .Z :=
    (hd.roles.1 r).1.ne (by decide +kernel)
  cases hX : d.perm r .X <;>
    cases hY : d.perm r .Y <;>
      cases hZ : d.perm r .Z <;>
        simp_all [u, StageCandidateRaw.StagePos, StageCandidateRaw.stageParentCount,
          StageCandidateRaw.stageAlphaCount, coord, add_assoc] <;> omega

set_option maxHeartbeats 2000000 in
-- Reconstructing a dependent child-shape word from all three coordinates is elaboration-heavy.
private theorem stage_shape_word_role_coarse_injective37 {w s b m n : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6)
    {E : Parent25.Pos p d b m r ≃ Fin n} :
    Function.Injective (fun j : (z : Parent25.Pos p d b m r) → ChildShape p z.1 =>
      fun W i => Parent25.coordFin (d.perm r W) (j (E.symm i)).val) := by
  intro j k h
  funext z
  let e : Side ≃ Side := Equiv.ofBijective (d.perm r) (hd.roles.1 r)
  have hcoord (S : Side) : coord S (j z).val = coord S (k z).val := by
    have hs := congrArg Fin.val
      (congrFun (congrFun h (e.symm S)) (E z))
    have heS : d.perm r (e.symm S) = S := e.apply_symm_apply S
    have hz : E.symm (E z) = z := E.symm_apply_apply z
    dsimp only at hs
    rw [heS, hz] at hs
    cases S <;> simpa [Parent25.coordFin, coord] using hs
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hcoord .X
  · apply Prod.ext
    · apply Fin.ext
      exact hcoord .Y
    · apply Fin.ext
      exact hcoord .Z

set_option maxHeartbeats 2000000 in
-- The public population coercions unfold the dependent word representation once more.
theorem stage_role_coarse_injective37 {w s b m : ℕ} (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6) :
    Function.Injective
      (rolePopulation (stagePopulationAt q p d b m r) (d.perm r)).coarse := by
  intro j k h
  apply Subtype.ext
  dsimp [rolePopulation, stagePopulationAt] at h
  exact stage_shape_word_role_coarse_injective37 p d hd r h

theorem stageTargetBucket_card37 {w s b m M : ℕ} [NeZero M] (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B) :
    (stageTargetBucket37 q p d r B j z).card * M^2 =
      Fintype.card (HashOutcome (stagePopulationAt q p d b m r) M) := by
  let P := rolePopulation (stagePopulationAt q p d b m r) (d.perm r)
  have hhash := asymmetric_hash P (stage_role_tight37 q p d hd r)
    (stage_role_coarse_injective37 q p d hd r) M hprime hodd hfloor
  simpa only [stageTargetBucket37, P] using hhash.1 j.val z.val

theorem stageTargetBucket_pairwise37 {w s b m M : ℕ} [NeZero M] (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (B : Finset (ZMod M)) (j : StageTargetLabel37 q p d b m r) :
    Pairwise (fun z z' => Disjoint
      (stageTargetBucket37 q p d r B j z)
      (stageTargetBucket37 q p d r B j z')) := by
  intro z z' hzz
  rw [Finset.disjoint_left]
  intro omega hz hz'
  have hzv := (Finset.mem_filter.mp hz).2.1
  have hzv' := (Finset.mem_filter.mp hz').2.1
  apply hzz
  apply Subtype.ext
  exact hzv.symm.trans hzv'

theorem stageTargetBucket_nonempty37 {w s b m M : ℕ} [NeZero M] (q : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (stagePopulationAt q p d b m r).grade < M)
    (j : StageTargetLabel37 q p d b m r) (z : StageBucketLabel37 B) :
    (stageTargetBucket37 q p d r B j z).Nonempty := by
  have hcard := stageTargetBucket_card37 q p d hd r B hprime hodd hfloor j z
  have hout : 0 < Fintype.card (HashOutcome (stagePopulationAt q p d b m r) M) :=
    Fintype.card_pos
  have hprod : 0 < (stageTargetBucket37 q p d r B j z).card * M^2 := by
    rw [hcard]
    exact hout
  exact Finset.card_pos.mp (Nat.pos_of_ne_zero fun hzero => by simp [hzero] at hprod)

end OmegaBound.ADVXXZGeneral

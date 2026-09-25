import OmegaBound.ADVXXZGeneralGlobalExactRepairTransport
import OmegaBound.ADVXXZGeneralAmend25GlobalBridge
import OmegaBound.ADVXXZGeneralGlobalOrderedDeletions
import OmegaBound.ADVXXZGeneralAsymmetricHash
import OmegaBound.ADVXXZGeneralGood

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

/-- Target labels of one exact global region. -/
abbrev GlobalTargetLabel27 {w n : ℕ} (g : GlobalSpec w) (xi : ExactGrid g n)
    (r : Fin 6) :=
  {j : (globalPopulation g n xi r).Label // j ∈ (globalPopulation g n xi r).target}

/-- The bucket-index subtype used by the generic good-family theorem. -/
abbrev GlobalBucketLabel27 {M : ℕ} (B : Finset (ZMod M)) :=
  {b : ZMod M // b ∈ B}

/-- A target label's affine-hash bucket, restricted along both subtype maps. -/
def globalTargetBucket27 {w n M : ℕ} [NeZero M] (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (j : GlobalTargetLabel27 g xi r) (b : GlobalBucketLabel27 B) :
    Finset (HashOutcome (globalPopulation g n xi r) M) :=
  bucket (rolePopulation (globalPopulation g n xi r) (g.perm r)) M j.val b.val

/-- The selected family, restricted to the target-label subtype. -/
def globalSelectedTargets27 {w n M : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M) :
    Finset (GlobalTargetLabel27 g xi r) :=
  (globalPopulation g n xi r).target.attach.filter fun j =>
    j.val ∈ selected (rolePopulation (globalPopulation g n xi r) (g.perm r))
      M B omega

/-- Exact-interface parts deleted from one selected global label. -/
def globalExactHoles27 {w n M : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (B : Finset (ZMod M))
    (omega : HashOutcome (globalPopulation g n xi r) M)
    (j : GlobalTargetLabel27 g xi r) (W : Side) :
    Finset (GlobalExactPart27 g n xi r j.val W) :=
  Finset.univ.filter fun a =>
    ¬ globalPartKeep g n xi r M B omega .zUseful W a.val

set_option maxHeartbeats 2000000 in
-- The global population and role permutation are unfolded in this finite three-side calculation.
theorem global_role_tight27 {w n : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (xi : ExactGrid g n) (r : Fin 6)
    (j : (globalPopulation g n xi r).Label)
    (i : Fin (globalPopulation g n xi r).n) :
    ∑ W, (((rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse j W i).val) =
      (rolePopulation (globalPopulation g n xi r) (g.perm r)).grade := by
  dsimp [rolePopulation, globalPopulation] at j i ⊢
  let u := j.val i
  let e : Side ≃ Side := Equiv.ofBijective (g.perm r) (hg.roles.1 r)
  have he := Equiv.sum_comp e (fun W => coord W u)
  have hside : (Finset.univ : Finset Side) = {.X, .Y, .Z} := by decide +kernel
  have hplain : (∑ W, coord W u) = 2*w := by
    rw [hside]
    simpa [coord, add_assoc] using u.property
  have hh := he.trans hplain
  rw [hside] at hh ⊢
  dsimp only [e, Equiv.ofBijective_apply] at hh
  dsimp [u] at hh
  have hXY : g.perm r .X ≠ g.perm r .Y :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hXZ : g.perm r .X ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  have hYZ : g.perm r .Y ≠ g.perm r .Z :=
    (hg.roles.1 r).1.ne (by decide +kernel)
  cases hX : g.perm r .X <;>
    cases hY : g.perm r .Y <;>
      cases hZ : g.perm r .Z <;>
        simp_all [u, coord, add_assoc] <;> omega

set_option maxHeartbeats 2000000 in
-- The global population is unfolded once to recover all three physical coordinates.
theorem global_role_coarse_injective27 {w n : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (xi : ExactGrid g n) (r : Fin 6) :
    Function.Injective
      (rolePopulation (globalPopulation g n xi r) (g.perm r)).coarse := by
  intro j k h
  apply Subtype.ext
  funext i
  let e : Side ≃ Side := Equiv.ofBijective (g.perm r) (hg.roles.1 r)
  have hcoord (S : Side) : coord S (j.val i) = coord S (k.val i) := by
    have hs := congrArg Fin.val (congrFun (congrFun h (e.symm S)) i)
    dsimp [rolePopulation, globalPopulation] at hs
    have heS : g.perm r (e.symm S) = S := e.apply_symm_apply S
    cases hP : g.perm r (e.symm S) <;> cases S <;>
      simp_all [coord]
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hcoord .X
  · apply Prod.ext
    · apply Fin.ext
      exact hcoord .Y
    · apply Fin.ext
      exact hcoord .Z

/-- The asymmetric-hash theorem gives the exact cardinality of every target bucket. -/
theorem globalTargetBucket_card27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (xi : ExactGrid g n)
    (r : Fin 6) (B : Finset (ZMod M))
    (hprime : Nat.Prime M) (hodd : 2 < M)
    (hfloor : (globalPopulation g n xi r).grade < M)
    (j : GlobalTargetLabel27 g xi r) (b : GlobalBucketLabel27 B) :
    (globalTargetBucket27 g xi r B j b).card * M^2 =
      Fintype.card (HashOutcome (globalPopulation g n xi r) M) := by
  let P := rolePopulation (globalPopulation g n xi r) (g.perm r)
  have hhash := asymmetric_hash P
    (global_role_tight27 g hg xi r) (global_role_coarse_injective27 g hg xi r)
    M hprime hodd hfloor
  simpa only [globalTargetBucket27, P] using hhash.1 j.val b.val

/-- Distinct bucket indices for one target label are disjoint. -/
theorem globalTargetBucket_pairwise27 {w n M : ℕ} [NeZero M]
    (g : GlobalSpec w) (xi : ExactGrid g n) (r : Fin 6)
    (B : Finset (ZMod M)) (j : GlobalTargetLabel27 g xi r) :
    Pairwise (fun b c => Disjoint
      (globalTargetBucket27 g xi r B j b)
      (globalTargetBucket27 g xi r B j c)) := by
  intro b c hbc
  rw [Finset.disjoint_left]
  intro omega hb hc
  have hb' := (Finset.mem_filter.mp hb).2.1
  have hc' := (Finset.mem_filter.mp hc).2.1
  apply hbc
  apply Subtype.ext
  exact hb'.symm.trans hc'

end
end OmegaBound.ADVXXZGeneral
end

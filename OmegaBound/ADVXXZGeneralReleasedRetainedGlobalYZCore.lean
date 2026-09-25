import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalParentK5
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

/-! Kernel-clean finite transports used by the released physical-global Y/Z semantics. -/

private theorem released_row_x_lt_yz (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).1 < 9 := by
  revert c
  decide +kernel

private theorem released_row_y_lt_yz (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).2.1 < 9 := by
  revert c
  decide +kernel

private theorem released_row_z_lt_yz (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).2.2 < 9 := by
  revert c
  decide +kernel

private theorem released_row_sum_yz (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).1 +
      (OmegaBound.ADVXXZG1.rowShape c).2.1 +
        (OmegaBound.ADVXXZG1.rowShape c).2.2 = 8 := by
  revert c
  decide +kernel

/-- A local kernel-clean inverse image of one released physical shape row. -/
def releasedPhysicalShapeAtYZ (c : Fin 45) : Shape 4 :=
  ⟨(⟨(OmegaBound.ADVXXZG1.rowShape c).1, released_row_x_lt_yz c⟩,
      ⟨(OmegaBound.ADVXXZG1.rowShape c).2.1, released_row_y_lt_yz c⟩,
      ⟨(OmegaBound.ADVXXZG1.rowShape c).2.2, released_row_z_lt_yz c⟩),
    released_row_sum_yz c⟩

theorem releasedPhysicalShapeAtYZ_index (c : Fin 45) :
    OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex (releasedPhysicalShapeAtYZ c) = c := by
  revert c
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem releasedShapeIndex_bijective_yz : Function.Bijective
    (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex : Shape 4 → Fin 45) := by
  refine ⟨?_, ?_⟩
  · intro a b
    revert a b
    decide +kernel
  · intro n
    exact ⟨releasedPhysicalShapeAtYZ n, releasedPhysicalShapeAtYZ_index n⟩

/-- Kernel-clean physical shape equivalence local to the Y/Z bridge. -/
def releasedPhysicalShapeEquivYZ : Fin 45 ≃ Shape 4 where
  toFun := releasedPhysicalShapeAtYZ
  invFun := OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex
  left_inv := releasedPhysicalShapeAtYZ_index
  right_inv := by
    intro u
    apply releasedShapeIndex_bijective_yz.1
    rw [releasedPhysicalShapeAtYZ_index]

theorem released_physical_shape_den_yz (r : Fin 6) :
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist r).den =
      116056878683004400771792896 := by
  revert r
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem released_logRow_physRow_k : ∀ (r : Fin 6) (n : Fin 45),
    OmegaBound.ADVXXZT2.logRow r (OmegaBound.ADVXXZG1.physRow r n) = n := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem released_physRow_logRow_k : ∀ (r : Fin 6) (n : Fin 45),
    OmegaBound.ADVXXZG1.physRow r (OmegaBound.ADVXXZT2.logRow r n) = n := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem released_roleAt_physicalSide_k : ∀ (r : Fin 6) (W : Side),
    OmegaBound.ADVXXZG1.roleAt r
      (OmegaBound.ADVXXZCertRegionalSemantic.physicalSide r W) = W := by
  decide +kernel

theorem released_physicalSideIndex_paperSide_k (i : Fin 3) :
    physicalSideIndex (OmegaBound.ADVXXZT3.paperSide i) = i := by
  fin_cases i <;> rfl

theorem released_perm_physicalSideIndex_k (r : Fin 6) (W : Side) :
    physicalSideIndex (releasedPerm r W) =
      OmegaBound.ADVXXZCertRegionalSemantic.physicalSide r W := by
  unfold releasedPerm
  exact released_physicalSideIndex_paperSide_k _

/-- The kernel-clean finite permutation from logical released rows to physical rows. -/
def releasedPhysRowEquivK (r : Fin 6) : Fin 45 ≃ Fin 45 where
  toFun := OmegaBound.ADVXXZG1.physRow r
  invFun := OmegaBound.ADVXXZT2.logRow r
  left_inv := released_logRow_physRow_k r
  right_inv := released_physRow_logRow_k r

theorem released_physical_alpha_logical_index (r : Fin 6) (n : Fin 45) :
    physicalGlobalSpec.toPaper.alpha r
        (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) =
      (OmegaBound.ADVXXZG1.aw r n : ℝ) /
        116056878683004400771792896 := by
  change (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist r).probR
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) = _
  unfold RatDist.probR
  rw [← OmegaBound.ADVXXZG1.alphaIdx_eq_shapeDist r,
    releasedPhysicalShapeAtYZ_index, released_physical_shape_den_yz]
  rfl

theorem released_physical_beta_logical_index (r : Fin 6) (W : Side) (n : Fin 45) :
    physicalGlobalSpec.toPaper.beta (physicalGlobalSpec.toPaper.perm r W) r
        (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) =
      OmegaBound.ADVXXZG1.betaIdx r W n := by
  change physicalGlobalBeta (releasedPerm r W) r
      (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) = _
  unfold physicalGlobalBeta
  rw [released_perm_physicalSideIndex_k, released_roleAt_physicalSide_k,
    releasedPhysicalShapeAtYZ_index, released_logRow_physRow_k]

set_option maxHeartbeats 2000000 in
theorem released_physical_coord_logical_index : ∀ (r : Fin 6) (W : Side) (n : Fin 45),
    coord (physicalGlobalSpec.toPaper.perm r W)
        (releasedPhysicalShapeAtYZ (OmegaBound.ADVXXZG1.physRow r n)) =
      OmegaBound.ADVXXZG1.rowLvl W n := by
  decide +kernel

private theorem released_eq_div_of_cross {q : ℚ} {A M : ℕ} (hA : 0 < A)
    (h : q.num * (A : ℤ) = (M : ℤ) * (q.den : ℤ)) :
    q = (M : ℚ) / (A : ℚ) := by
  have hA' : ((A : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hd : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos q).ne'
  have h' : ((q.num : ℚ)) * (A : ℚ) = (M : ℚ) * (q.den : ℚ) := by
    exact_mod_cast h
  rw [eq_div_iff hA']
  calc
    q * (A : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * (A : ℚ) := by
      rw [Rat.num_div_den]
    _ = ((q.num : ℚ) * (A : ℚ)) / (q.den : ℚ) := by ring
    _ = ((M : ℚ) * (q.den : ℚ)) / (q.den : ℚ) := by rw [h']
    _ = (M : ℚ) := by field_simp

/-- Read a fresh `ParentOK` certificate using a supplied kernel-clean positivity witness. -/
theorem released_prob_parent_mixture_k
    (avg : Fin 6 → Fin (2 * 4 + 1) → Chunk 4 → ℚ) (S : Side)
    (r : Fin 6) (l : Fin (2 * 4 + 1)) (c : Chunk 4)
    (hA : 0 < OmegaBound.ADVXXZG1.Atot r S l)
    (h : OmegaBound.ADVXXZG1.ParentOK avg S r l c) :
    avg r l c =
      (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
          (OmegaBound.ADVXXZG1.aw r n : ℚ) *
            (OmegaBound.ADVXXZG1.betaIdx r S n).prob c) /
        (OmegaBound.ADVXXZG1.Atot r S l : ℚ) := by
  classical
  have hD : 0 < OmegaBound.ADVXXZG1.Dprod r S l :=
    OmegaBound.ADVXXZG1.Dprod_pos r S l
  have hA' : ((OmegaBound.ADVXXZG1.Atot r S l : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hA.ne'
  have hD' : ((OmegaBound.ADVXXZG1.Dprod r S l : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hD.ne'
  have hkey : ((OmegaBound.ADVXXZG1.MixNum r S l c : ℕ) : ℚ) =
      (OmegaBound.ADVXXZG1.Dprod r S l : ℚ) *
        ∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
          (OmegaBound.ADVXXZG1.aw r n : ℚ) *
            (OmegaBound.ADVXXZG1.betaIdx r S n).prob c := by
    simp only [OmegaBound.ADVXXZG1.MixNum]
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hdvd : (OmegaBound.ADVXXZG1.betaIdx r S n).den ∣
        OmegaBound.ADVXXZG1.Dprod r S l :=
      Finset.dvd_prod_of_mem
        (fun m => (OmegaBound.ADVXXZG1.betaIdx r S m).den) hn
    have hden : (((OmegaBound.ADVXXZG1.betaIdx r S n).den : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (OmegaBound.ADVXXZG1.betaIdx r S n).den_pos.ne'
    have hcast :
        ((OmegaBound.ADVXXZG1.Dprod r S l /
            (OmegaBound.ADVXXZG1.betaIdx r S n).den : ℕ) : ℚ) =
          (OmegaBound.ADVXXZG1.Dprod r S l : ℚ) /
            ((OmegaBound.ADVXXZG1.betaIdx r S n).den : ℚ) :=
      Nat.cast_div hdvd hden
    rw [Nat.cast_mul, Nat.cast_mul, hcast]
    simp only [RatDist.prob]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hcross :
      (avg r l c).num *
          ((OmegaBound.ADVXXZG1.Atot r S l *
              OmegaBound.ADVXXZG1.Dprod r S l : ℕ) : ℤ) =
        (OmegaBound.ADVXXZG1.MixNum r S l c : ℤ) *
          ((avg r l c).den : ℤ) := by
    rw [Nat.cast_mul]
    exact h
  have hq := released_eq_div_of_cross (Nat.mul_pos hA hD) hcross
  have hlast :
      (OmegaBound.ADVXXZG1.Dprod r S l : ℚ) *
          (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
            (OmegaBound.ADVXXZG1.aw r n : ℚ) *
              (OmegaBound.ADVXXZG1.betaIdx r S n).prob c) /
            ((OmegaBound.ADVXXZG1.Atot r S l : ℚ) *
              (OmegaBound.ADVXXZG1.Dprod r S l : ℚ)) =
        (∑ n ∈ OmegaBound.ADVXXZG1.grp S l,
            (OmegaBound.ADVXXZG1.aw r n : ℚ) *
              (OmegaBound.ADVXXZG1.betaIdx r S n).prob c) /
          (OmegaBound.ADVXXZG1.Atot r S l : ℚ) := by
    rw [div_eq_div_iff (mul_ne_zero hA' hD') hA']
    ring
  rw [hq, Nat.cast_mul, hkey, hlast]

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_logRow_physRow_k
#print axioms OmegaBound.ADVXXZGeneral.released_physRow_logRow_k
#print axioms OmegaBound.ADVXXZGeneral.released_roleAt_physicalSide_k
#print axioms OmegaBound.ADVXXZGeneral.released_physical_alpha_logical_index
#print axioms OmegaBound.ADVXXZGeneral.released_physical_beta_logical_index
#print axioms OmegaBound.ADVXXZGeneral.released_physical_coord_logical_index
#print axioms OmegaBound.ADVXXZGeneral.released_prob_parent_mixture_k

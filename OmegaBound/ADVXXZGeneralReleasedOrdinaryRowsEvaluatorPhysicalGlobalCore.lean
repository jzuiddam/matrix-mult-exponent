import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorDerivedRetained
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalTopLink

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 5000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

private theorem physical_row_x_lt32 (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).1 < 9 := by
  revert c
  decide +kernel

private theorem physical_row_y_lt32 (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).2.1 < 9 := by
  revert c
  decide +kernel

private theorem physical_row_z_lt32 (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).2.2 < 9 := by
  revert c
  decide +kernel

private theorem physical_row_sum32 (c : Fin 45) :
    (OmegaBound.ADVXXZG1.rowShape c).1 +
      (OmegaBound.ADVXXZG1.rowShape c).2.1 +
        (OmegaBound.ADVXXZG1.rowShape c).2.2 = 8 := by
  revert c
  decide +kernel

/-- The computable physical shape carried by a released global row. -/
def physicalShapeAt32 (c : Fin 45) : Shape 4 :=
  ⟨(⟨(OmegaBound.ADVXXZG1.rowShape c).1, physical_row_x_lt32 c⟩,
      ⟨(OmegaBound.ADVXXZG1.rowShape c).2.1, physical_row_y_lt32 c⟩,
      ⟨(OmegaBound.ADVXXZG1.rowShape c).2.2, physical_row_z_lt32 c⟩),
    physical_row_sum32 c⟩

theorem physicalShapeAt32_index (c : Fin 45) :
    OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex (physicalShapeAt32 c) = c := by
  revert c
  decide +kernel

theorem physicalShapeAt32_equiv (c : Fin 45) :
    OmegaBound.ADVXXZT4.shapeAt c = physicalShapeAt32 c := by
  apply OmegaBound.ADVXXZT1.shapeIndex_bijective.1
  rw [OmegaBound.ADVXXZT4.shapeIndex_shapeAt, physicalShapeAt32_index]

/-- The physical global mass at a released row, with the row transport exposed. -/
theorem physical_global_joint_index32 (r : Fin 6) (c : Fin 45) :
    physicalGlobalSpec.joint.prob (r, physicalShapeAt32 c) =
      ((OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist.num r : ℚ) /
          OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist.den) *
        ((OmegaBound.ADVXXZG1.alphaIdx r c : ℚ) /
          (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist r).den) := by
  rw [physical_global_joint_eq]
  simp only [physicalGlobalSpec]
  unfold RatDist.prob
  rw [← OmegaBound.ADVXXZG1.alphaIdx_eq_shapeDist r (physicalShapeAt32 c),
    physicalShapeAt32_index]

/-- Every released physical-global region has the same numerator. -/
theorem physical_global_region_num32 (r : Fin 6) :
    OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist.num r =
      19342813113834066795298816 := by
  revert r
  decide +kernel

/-- The released physical-global region denominator. -/
theorem physical_global_region_den32 :
    OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist.den =
      116056878683004400771792896 := by
  decide +kernel

/-- All six released physical-global shape distributions use the certificate denominator. -/
theorem physical_global_shape_den32 (r : Fin 6) :
    (OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist r).den =
      116056878683004400771792896 := by
  revert r
  decide +kernel

/-- Number of `1` symbols in the base-three word of a physical complete-split row. -/
def physicalOneCount4_32 (i : Fin 81) : ℕ :=
  (if i.1 / 27 = 1 then 1 else 0) +
    (if (i.1 / 9) % 3 = 1 then 1 else 0) +
      (if (i.1 / 3) % 3 = 1 then 1 else 0) +
        (if i.1 % 3 = 1 then 1 else 0)

theorem physical_one_count4_32 (i : Fin 81) :
    ((Finset.univ.filter (fun p : Fin 4 =>
      ((OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) p).val = 1)).card : ℕ) =
        physicalOneCount4_32 i := by
  revert i
  decide +kernel

/-- The ordinary atom evaluator is linear in the rational inventory weight. -/
theorem ordinaryAtomRate_mul_weight32 (q : ℕ) (W : Side) (c x : ℚ) (key : AtomKey) :
    ordinaryAtomRate q W (c * x, key) =
      (c : ℝ) * ordinaryAtomRate q W (x, key) := by
  unfold ordinaryAtomRate
  cases W
  · by_cases h : coord .Y key.2.1 = 0 ∧ 0 < coord .X key.2.1 ∧
        0 < coord .Z key.2.1
    · rw [if_pos h, if_pos h]
      push_cast
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  · by_cases h : coord .Z key.2.1 = 0 ∧ 0 < coord .X key.2.1 ∧
        0 < coord .Y key.2.1
    · rw [if_pos h, if_pos h]
      push_cast
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  · by_cases h : coord .X key.2.1 = 0 ∧ 0 < coord .Y key.2.1 ∧
        0 < coord .Z key.2.1
    · rw [if_pos h, if_pos h]
      push_cast
      ring
    · rw [if_neg h, if_neg h, mul_zero]

/-- A global inventory's mapped sum is the finite sum over its region/shape addresses. -/
theorem globalInventory_map_sum32 {w : ℕ} (g : GlobalSpec w)
    {M : Type*} [AddCommMonoid M] (f : ℚ × AtomKey → M) :
    ((globalInventory g).map f).sum =
      ∑ ru : Fin 6 × Shape w, f (g.joint.prob ru,
        ⟨w, ru.2, fun W sigma => (g.beta W ru.1 ru.2).prob sigma⟩) := by
  rw [← Equiv.sum_comp (Fintype.equivFin (Fin 6 × Shape w)).symm
    (fun ru : Fin 6 × Shape w => f (g.joint.prob ru,
      ⟨w, ru.2, fun W sigma => (g.beta W ru.1 ru.2).prob sigma⟩)),
    Fin.sum_univ_def]
  unfold globalInventory
  rw [List.map_map]
  rfl

/-- One physical global region, after cancelling the certificate's single `D^4` scale. -/
noncomputable def physicalGlobalRegionalMatrixRate32 (r : Fin 6) (W : Side) : ℝ :=
  ∑ u : Shape 4, ordinaryAtomRate 5 W
    (physicalGlobalSpec.joint.prob (r, u),
      ⟨4, u, fun V sigma => (physicalGlobalSpec.beta V r u).prob sigma⟩)

/-- One unscaled physical-global atom, addressed by its physical table row. -/
noncomputable def physicalGlobalCellMatrixRate32
    (r : Fin 6) (W : Side) (c : Fin 45) : ℝ :=
  ordinaryAtomRate 5 W
    (physicalGlobalSpec.joint.prob (r, physicalShapeAt32 c),
      ⟨4, physicalShapeAt32 c, fun V sigma =>
        (physicalGlobalSpec.beta V r (physicalShapeAt32 c)).prob sigma⟩)

/-- The seven physical boundary rows active in a matrix direction. -/
def physicalGlobalBoundaryCell32 (W : Side) : Fin 7 → Fin 45 :=
  match W with
  | .X => ![9, 17, 24, 30, 35, 39, 42]
  | .Y => ![16, 23, 29, 34, 38, 41, 43]
  | .Z => ![1, 2, 3, 4, 5, 6, 7]

def PhysicalGlobalBoundaryRow32 (W : Side) (c : Fin 45) : Prop :=
  OrdinaryActiveAt W (physicalShapeAt32 c)

instance instDecidablePhysicalGlobalBoundaryRow32 (W : Side) (c : Fin 45) :
    Decidable (PhysicalGlobalBoundaryRow32 W c) := by
  unfold PhysicalGlobalBoundaryRow32
  infer_instance

def physicalGlobalBoundaryMap32 (W : Side) (i : Fin 7) :
    {c : Fin 45 // PhysicalGlobalBoundaryRow32 W c} :=
  ⟨physicalGlobalBoundaryCell32 W i, by
    cases W <;> fin_cases i <;>
      decide +kernel⟩

private theorem physicalGlobalBoundaryMap32_injective (W : Side) :
    Function.Injective (physicalGlobalBoundaryMap32 W) := by
  intro i j
  cases W <;> revert i j <;> decide +kernel

private theorem physicalGlobalBoundaryRow32_card (W : Side) :
    Fintype.card {c : Fin 45 // PhysicalGlobalBoundaryRow32 W c} = 7 := by
  cases W <;> decide +kernel

private theorem physicalGlobalBoundaryMap32_bijective (W : Side) :
    Function.Bijective (physicalGlobalBoundaryMap32 W) := by
  apply (Fintype.bijective_iff_injective_and_card
    (physicalGlobalBoundaryMap32 W)).2
  refine ⟨physicalGlobalBoundaryMap32_injective W, ?_⟩
  simpa using (physicalGlobalBoundaryRow32_card W).symm

noncomputable def physicalGlobalBoundaryEquiv32 (W : Side) :
    Fin 7 ≃ {c : Fin 45 // PhysicalGlobalBoundaryRow32 W c} :=
  Equiv.ofBijective (physicalGlobalBoundaryMap32 W)
    (physicalGlobalBoundaryMap32_bijective W)

private theorem ordinaryAtomRate_inactive32 (q : ℕ) (W : Side) (a : ℚ × AtomKey)
    (h : ¬ OrdinaryActiveAt W a.2.2.1) : ordinaryAtomRate q W a = 0 := by
  unfold OrdinaryActiveAt at h
  unfold ordinaryAtomRate
  cases W <;> rw [if_neg h]

/-- Reindex one global regional row by the released physical row number. -/
theorem physical_global_regional_reindex32 (r : Fin 6) (W : Side) :
    physicalGlobalRegionalMatrixRate32 r W =
      ∑ c : Fin 45, ordinaryAtomRate 5 W
        (physicalGlobalSpec.joint.prob (r, physicalShapeAt32 c),
          ⟨4, physicalShapeAt32 c, fun V sigma =>
            (physicalGlobalSpec.beta V r (physicalShapeAt32 c)).prob sigma⟩) := by
  unfold physicalGlobalRegionalMatrixRate32
  rw [← Equiv.sum_comp
    (Equiv.ofBijective OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex
      OmegaBound.ADVXXZT1.shapeIndex_bijective).symm]
  apply Finset.sum_congr rfl
  intro c _
  have hc := physicalShapeAt32_equiv c
  change
    (Equiv.ofBijective OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex
      OmegaBound.ADVXXZT1.shapeIndex_bijective).symm c = physicalShapeAt32 c at hc
  rw [hc]

set_option maxHeartbeats 2000000 in
-- Use the active-row equivalence, without opening any released beta table.
theorem physical_global_regional_support32 (r : Fin 6) (W : Side) :
    physicalGlobalRegionalMatrixRate32 r W =
      ∑ i : Fin 7,
        physicalGlobalCellMatrixRate32 r W (physicalGlobalBoundaryCell32 W i) := by
  rw [physical_global_regional_reindex32]
  unfold physicalGlobalCellMatrixRate32
  let f := fun c : Fin 45 => ordinaryAtomRate 5 W
    (physicalGlobalSpec.joint.prob (r, physicalShapeAt32 c),
      ⟨4, physicalShapeAt32 c, fun V sigma =>
        (physicalGlobalSpec.beta V r (physicalShapeAt32 c)).prob sigma⟩)
  change (∑ c : Fin 45, f c) =
    ∑ i : Fin 7, f (physicalGlobalBoundaryCell32 W i)
  rw [show (∑ c : Fin 45, f c) =
      ∑ c : Fin 45, if PhysicalGlobalBoundaryRow32 W c then f c else 0 by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : PhysicalGlobalBoundaryRow32 W c
    · rw [if_pos hc]
    · rw [if_neg hc]
      exact ordinaryAtomRate_inactive32 5 W _ hc]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := PhysicalGlobalBoundaryRow32 W)
    (F := (inferInstance : Fintype {c : Fin 45 // PhysicalGlobalBoundaryRow32 W c}))
    (Finset.univ.filter (PhysicalGlobalBoundaryRow32 W))
    (fun c => by simp)
    (fun c => f c)]
  exact (Equiv.sum_comp (physicalGlobalBoundaryEquiv32 W)
    (fun c => f c.1)).symm

set_option maxHeartbeats 1000000 in
/-- The scaled physical global inventory, divided once by `D^4`, is the sum of its six
regional rows. -/
theorem physical_global_inventory_rate32 (W : Side) :
    ordinaryInventoryRate 5 W (G releasedOrdinaryCertificatePhysical) /
        (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 4 =
      ∑ r : Fin 6, physicalGlobalRegionalMatrixRate32 r W := by
  have hDnat : releasedOrdinaryCertificatePhysical.D ≠ 0 := by
    change ordinaryD ^ 2 ≠ 0
    exact pow_ne_zero _ (ne_of_gt (show 0 < ordinaryD by decide +kernel))
  have hDR : (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 4 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast hDnat)
  unfold ordinaryInventoryRate G scaleInventory
  rw [List.map_map, globalInventory_map_sum32]
  simp only [Function.comp_apply]
  rw [Fintype.sum_prod_type]
  simp only [ordinaryAtomRate_mul_weight32]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_div]
  unfold physicalGlobalRegionalMatrixRate32
  apply Finset.sum_congr rfl
  intro u _
  simp only [releasedOrdinaryCertificatePhysical]
  exact mul_div_cancel_left₀ _ (by
    exact_mod_cast (pow_ne_zero 4
      (pow_ne_zero 2 (ne_of_gt (show 0 < ordinaryD by decide +kernel)))))

end OmegaBound.ADVXXZGeneral
end

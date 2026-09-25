import OmegaBound.ADVXXZGeneralAmend31AccumulatedBoundaryLowerRate

set_option autoImplicit false
set_option maxRecDepth 10000

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem inventory_nonzero_partition_perm31 (I : Inventory)
    (hI : ∀ a ∈ I, 0 ≤ a.1) :
    InventoryEq (interior I ++ boundaryOccurrences27 I) I := by
  unfold InventoryEq
  induction I with
  | nil => simp [interior, boundaryOccurrences27]
  | cons a I ih =>
      have ha_nonneg := hI a (by simp)
      have htail : ∀ x ∈ I, 0 ≤ x.1 := by
        intro x hx
        exact hI x (by simp [hx])
      have hih := ih htail
      rw [List.filter_append] at hih
      by_cases ha0 : a.1 = 0
      · simpa [interior, boundaryOccurrences27, ha0] using hih
      · have hapos : 0 < a.1 := lt_of_le_of_ne ha_nonneg (Ne.symm ha0)
        by_cases hx : coord .X a.2.2.1 = 0
        · simpa [interior, boundaryOccurrences27, ha0, hapos, hx] using
            (List.perm_middle.trans (hih.cons a))
        · by_cases hy : coord .Y a.2.2.1 = 0
          · simpa [interior, boundaryOccurrences27, ha0, hapos, hx, hy] using
              (List.perm_middle.trans (hih.cons a))
          · by_cases hz : coord .Z a.2.2.1 = 0
            · simpa [interior, boundaryOccurrences27, ha0, hapos, hx, hy, hz] using
                (List.perm_middle.trans (hih.cons a))
            · have hxpos : 0 < coord .X a.2.2.1 := Nat.pos_of_ne_zero hx
              have hypos : 0 < coord .Y a.2.2.1 := Nat.pos_of_ne_zero hy
              have hzpos : 0 < coord .Z a.2.2.1 := Nat.pos_of_ne_zero hz
              simpa [interior, boundaryOccurrences27, ha0, hapos, hx, hy, hz,
                hxpos, hypos, hzpos] using hih.cons a

private theorem inventoryTensorZ_equiv_of_inventoryEq31
    (q : ℕ) (I J : Inventory) (n : ℕ) (ε : ℚ) (h : InventoryEq I J) :
    ∃ (eX : (inventoryTensorZ q I n ε).X ≃ (inventoryTensorZ q J n ε).X)
      (eY : (inventoryTensorZ q I n ε).Y ≃ (inventoryTensorZ q J n ε).Y)
      (eZ : (inventoryTensorZ q I n ε).Z ≃ (inventoryTensorZ q J n ε).Z),
      ∀ x y z, (inventoryTensorZ q J n ε).tensor (eX x) (eY y) (eZ z) =
        (inventoryTensorZ q I n ε).tensor x y z := by
  rcases inventoryTensorZ_filter_ne_zero q I n ε with ⟨eXI, eYI, eZI, hI⟩
  rcases inventoryTensorZ_perm q n ε h with ⟨eXP, eYP, eZP, hP⟩
  rcases inventoryTensorZ_filter_ne_zero q J n ε with ⟨eXJ, eYJ, eZJ, hJ⟩
  refine ⟨eXI.trans (eXP.trans eXJ.symm), eYI.trans (eYP.trans eYJ.symm),
    eZI.trans (eZP.trans eZJ.symm), ?_⟩
  intro x y z
  calc
    (inventoryTensorZ q J n ε).tensor
        ((eXI.trans (eXP.trans eXJ.symm)) x)
        ((eYI.trans (eYP.trans eYJ.symm)) y)
        ((eZI.trans (eZP.trans eZJ.symm)) z) =
      (inventoryTensorZ q (J.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXP (eXI x)) (eYP (eYI y)) (eZP (eZI z)) := by
          symm
          simpa using hJ (eXJ.symm (eXP (eXI x))) (eYJ.symm (eYP (eYI y)))
            (eZJ.symm (eZP (eZI z)))
    _ = (inventoryTensorZ q (I.filter (fun a => decide (a.1 ≠ 0))) n ε).tensor
        (eXI x) (eYI y) (eZI z) := hP _ _ _
    _ = (inventoryTensorZ q I n ε).tensor x y z := hI _ _ _

private theorem inventoryTensorZ_append31 (q : ℕ) (I J : Inventory) (n : ℕ) (ε : ℚ) :
    ∃ (eX : (inventoryTensorZ q I n ε).X × (inventoryTensorZ q J n ε).X ≃
          (inventoryTensorZ q (I ++ J) n ε).X)
      (eY : (inventoryTensorZ q I n ε).Y × (inventoryTensorZ q J n ε).Y ≃
          (inventoryTensorZ q (I ++ J) n ε).Y)
      (eZ : (inventoryTensorZ q I n ε).Z × (inventoryTensorZ q J n ε).Z ≃
          (inventoryTensorZ q (I ++ J) n ε).Z),
      ∀ x y z, (inventoryTensorZ q (I ++ J) n ε).tensor (eX x) (eY y) (eZ z) =
        tensorProd (inventoryTensorZ q I n ε).tensor
          (inventoryTensorZ q J n ε).tensor x y z := by
  induction I with
  | nil =>
      let eX : (inventoryTensorZ q [] n ε).X × (inventoryTensorZ q J n ε).X ≃
          (inventoryTensorZ q J n ε).X :=
        { toFun := fun x => x.2
          invFun := fun x => ((), x)
          left_inv := by rintro ⟨x, y⟩; cases x; rfl
          right_inv := fun _ => rfl }
      let eY : (inventoryTensorZ q [] n ε).Y × (inventoryTensorZ q J n ε).Y ≃
          (inventoryTensorZ q J n ε).Y :=
        { toFun := fun x => x.2
          invFun := fun x => ((), x)
          left_inv := by rintro ⟨x, y⟩; cases x; rfl
          right_inv := fun _ => rfl }
      let eZ : (inventoryTensorZ q [] n ε).Z × (inventoryTensorZ q J n ε).Z ≃
          (inventoryTensorZ q J n ε).Z :=
        { toFun := fun x => x.2
          invFun := fun x => ((), x)
          left_inv := by rintro ⟨x, y⟩; cases x; rfl
          right_inv := fun _ => rfl }
      refine ⟨eX, eY, eZ, ?_⟩
      rintro ⟨x₀, x⟩ ⟨y₀, y⟩ ⟨z₀, z⟩
      cases x₀; cases y₀; cases z₀
      simp [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ, tensorProd, eX, eY, eZ]
  | cons a I ih =>
      rcases ih with ⟨fX, fY, fZ, hf⟩
      let eX : (inventoryTensorZ q (a :: I) n ε).X ×
            (inventoryTensorZ q J n ε).X ≃
          (inventoryTensorZ q ((a :: I) ++ J) n ε).X :=
        { toFun := fun x => (x.1.1, fX (x.1.2, x.2))
          invFun := fun x => ((x.1, (fX.symm x.2).1), (fX.symm x.2).2)
          left_inv := by rintro ⟨⟨x, y⟩, z⟩; simp
          right_inv := by rintro ⟨x, yz⟩; simp }
      let eY : (inventoryTensorZ q (a :: I) n ε).Y ×
            (inventoryTensorZ q J n ε).Y ≃
          (inventoryTensorZ q ((a :: I) ++ J) n ε).Y :=
        { toFun := fun x => (x.1.1, fY (x.1.2, x.2))
          invFun := fun x => ((x.1, (fY.symm x.2).1), (fY.symm x.2).2)
          left_inv := by rintro ⟨⟨x, y⟩, z⟩; simp
          right_inv := by rintro ⟨x, yz⟩; simp }
      let eZ : (inventoryTensorZ q (a :: I) n ε).Z ×
            (inventoryTensorZ q J n ε).Z ≃
          (inventoryTensorZ q ((a :: I) ++ J) n ε).Z :=
        { toFun := fun x => (x.1.1, fZ (x.1.2, x.2))
          invFun := fun x => ((x.1, (fZ.symm x.2).1), (fZ.symm x.2).2)
          left_inv := by rintro ⟨⟨x, y⟩, z⟩; simp
          right_inv := by rintro ⟨x, yz⟩; simp }
      refine ⟨eX, eY, eZ, ?_⟩
      rintro ⟨⟨x₀, x⟩, xJ⟩ ⟨⟨y₀, y⟩, yJ⟩ ⟨⟨z₀, z⟩, zJ⟩
      dsimp [eX, eY, eZ]
      simp only [inventoryTensorZ, P2M.V17_D_Inventory.inventoryTensorZ, tensorProd,
        List.cons_append]
      change _ * (inventoryTensorZ q (I ++ J) n ε).tensor
          (fX (x, xJ)) (fY (y, yJ)) (fZ (z, zJ)) =
        (_ * (inventoryTensorZ q I n ε).tensor x y z) *
          (inventoryTensorZ q J n ε).tensor xJ yJ zJ
      rw [hf]
      simp only [tensorProd]
      exact (mul_assoc _ _ _).symm

private theorem restricts_both_of_tensor_equiv31
    {X Y Z X' Y' Z' : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor3 ℤ X Y Z) (U : Tensor3 ℤ X' Y' Z')
    (eX : X' ≃ X) (eY : Y' ≃ Y) (eZ : Z' ≃ Z)
    (h : ∀ x y z, T (eX x) (eY y) (eZ z) = U x y z) :
    Restricts U T ∧ Restricts T U := by
  classical
  constructor
  · exact OmegaBound.Restricts.of_eq (OmegaBound.precomp_restricts eX eY eZ T)
      (by funext x y z; exact (h x y z).symm)
  · exact OmegaBound.Restricts.of_eq
      (OmegaBound.precomp_restricts eX.symm eY.symm eZ.symm U)
      (by
        funext x y z
        simpa using h (eX.symm x) (eY.symm y) (eZ.symm z))

/-- Paper clauses:
`P/constituent.tex:120,169,341` and `P/numerical.tex:19–22`. -/
theorem inventory_boundary_split31 (q : ℕ) (I : Inventory) (n : ℕ) (ε : ℚ)
    (hI : ∀ a ∈ I, 0 ≤ a.1) :
  Restricts (tensorProd (inventoryTensorZ q (interior I) n ε).tensor
      (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor)
    (inventoryTensorZ q I n ε).tensor ∧
  Restricts (inventoryTensorZ q I n ε).tensor
    (tensorProd (inventoryTensorZ q (interior I) n ε).tensor
      (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor) := by
  let A := interior I ++ boundaryOccurrences27 I
  rcases inventoryTensorZ_append31 q (interior I) (boundaryOccurrences27 I) n ε with
    ⟨aX, aY, aZ, ha⟩
  rcases inventoryTensorZ_equiv_of_inventoryEq31 q A I n ε
    (inventory_nonzero_partition_perm31 I hI) with ⟨bX, bY, bZ, hb⟩
  apply restricts_both_of_tensor_equiv31
    (inventoryTensorZ q I n ε).tensor
    (tensorProd (inventoryTensorZ q (interior I) n ε).tensor
      (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor)
    (aX.trans bX) (aY.trans bY) (aZ.trans bZ)
  intro x y z
  exact (hb (aX x) (aY y) (aZ z)).trans (ha x y z)

end
end OmegaBound.ADVXXZGeneral
end

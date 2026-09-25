import OmegaBound.ADVXXZGeneralAmend31InventoryBoundarySplit

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- A stage inventory link transports the entire dependent physical `AtomKey` (width, shape,
and all three split distributions) and exposes the source inventory as the linked interior
tensor times its occurrence-preserving boundary tensor.  Both directions are supplied because
successive stage assembly needs reindexing, not merely equality of pooled masses. -/
theorem inventory_link_boundary_reindex
    (q : ℕ) (I J : Inventory) (n : ℕ) (ε : ℚ)
    (hlink : InventoryEq (interior I) J)
    (hI : ∀ a ∈ I, 0 ≤ a.1)
    (hint : ∀ a ∈ interior I, ∃ k : ℕ, a.1 * (n : ℚ) = k)
    (hJ : ∀ a ∈ J, ∃ k : ℕ, a.1 * (n : ℚ) = k) :
    Restricts
        (tensorProd (inventoryTensorZ q J n ε).tensor
          (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor)
        (inventoryTensorZ q I n ε).tensor ∧
      Restricts (inventoryTensorZ q I n ε).tensor
        (tensorProd (inventoryTensorZ q J n ε).tensor
          (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor) := by
  classical
  obtain ⟨eX, eY, eZ, he⟩ := inventory_transport q (interior I) J n ε hlink hint hJ
  have hIJ : Restricts (inventoryTensorZ q (interior I) n ε).tensor
      (inventoryTensorZ q J n ε).tensor := by
    refine ADVXXZ.restricts_of_sub eX eY eZ ?_
    intro x y z
    exact (he x y z).symm
  have hJI : Restricts (inventoryTensorZ q J n ε).tensor
      (inventoryTensorZ q (interior I) n ε).tensor := by
    refine ADVXXZ.restricts_of_sub eX.symm eY.symm eZ.symm ?_
    intro x y z
    simpa using he (eX.symm x) (eY.symm y) (eZ.symm z)
  obtain ⟨hsplit, hjoin⟩ := inventory_boundary_split31 q I n ε hI
  constructor
  · exact Tensor3.Restricts.trans
      (OmegaBound.Restricts.tensorProd_right hJI
        (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor) hsplit
  · exact Tensor3.Restricts.trans hjoin
      (OmegaBound.Restricts.tensorProd_right hIJ
        (inventoryTensorZ q (boundaryOccurrences27 I) n ε).tensor)

/-- Top-link specialization: the stage caller supplies only the two scale-integrality facts
needed by the public inventory transport API. -/
theorem top_link_boundary_reindex
    (C : Certificate) (hC : AdmissibleAt C) (l : Stage C.top) (hl : l.val = C.top)
    (n : ℕ) (ε : ℚ)
    (hG : ∀ a ∈ G C, 0 ≤ a.1)
    (hint : ∀ a ∈ interior (G C), ∃ k : ℕ, a.1 * (n : ℚ) = k)
    (hP : ∀ a ∈ P C l, ∃ k : ℕ, a.1 * (n : ℚ) = k) :
    Restricts
        (tensorProd (inventoryTensorZ C.q (P C l) n ε).tensor
          (inventoryTensorZ C.q (boundaryOccurrences27 (G C)) n ε).tensor)
        (inventoryTensorZ C.q (G C) n ε).tensor ∧
      Restricts (inventoryTensorZ C.q (G C) n ε).tensor
        (tensorProd (inventoryTensorZ C.q (P C l) n ε).tensor
          (inventoryTensorZ C.q (boundaryOccurrences27 (G C)) n ε).tensor) :=
  inventory_link_boundary_reindex C.q (G C) (P C l) n ε (hC.top_link l hl) hG hint hP

/-- Successive-stage specialization for `next_link`, retaining the boundary occurrences of the
earlier child output exactly once. -/
theorem next_link_boundary_reindex
    (C : Certificate) (hC : AdmissibleAt C) (l h : Stage C.top)
    (hlh : l.val + 1 = h.val) (n : ℕ) (ε : ℚ)
    (hQ : ∀ a ∈ QAt C h, 0 ≤ a.1)
    (hint : ∀ a ∈ interior (QAt C h), ∃ k : ℕ, a.1 * (n : ℚ) = k)
    (hP : ∀ a ∈ P C l, ∃ k : ℕ, a.1 * (n : ℚ) = k) :
    Restricts
        (tensorProd (inventoryTensorZ C.q (P C l) n ε).tensor
          (inventoryTensorZ C.q (boundaryOccurrences27 (QAt C h)) n ε).tensor)
        (inventoryTensorZ C.q (QAt C h) n ε).tensor ∧
      Restricts (inventoryTensorZ C.q (QAt C h) n ε).tensor
        (tensorProd (inventoryTensorZ C.q (P C l) n ε).tensor
          (inventoryTensorZ C.q (boundaryOccurrences27 (QAt C h)) n ε).tensor) :=
  inventory_link_boundary_reindex C.q (QAt C h) (P C l) n ε
    (hC.next_link l h hlh) hQ hint hP

end OmegaBound.ADVXXZGeneral
end

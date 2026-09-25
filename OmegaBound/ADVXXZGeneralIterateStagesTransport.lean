import OmegaBound.ADVXXZGeneralIterateInfraGlobal
import OmegaBound.ADVXXZGeneralIterateInfraLinks
import OmegaBound.ADVXXZGeneralIterateInfraCopies

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

/-- An ordinary carrier transport supplies the forward restriction. -/
theorem ordinaryTensorTransport_restricts {U V : ITensor}
    (h : OrdinaryTensorTransport U V) : Restricts U.tensor V.tensor := by
  obtain ⟨eX, eY, eZ, he⟩ := h
  exact ADVXXZ.restricts_of_sub eX eY eZ he

/-- An ordinary carrier transport also supplies its inverse restriction. -/
theorem ordinaryTensorTransport_restricts_reverse {U V : ITensor}
    (h : OrdinaryTensorTransport U V) : Restricts V.tensor U.tensor := by
  obtain ⟨eX, eY, eZ, he⟩ := h
  refine ADVXXZ.restricts_of_sub eX.symm eY.symm eZ.symm ?_
  intro x y z
  simpa using (he (eX.symm x) (eY.symm y) (eZ.symm z)).symm

/-- Restriction is preserved by a labelled family of identical copies. -/
theorem copiesZ_restricts_of_restricts (k : ℕ) {U V : ITensor}
    (h : Restricts U.tensor V.tensor) :
    Restricts (copiesZ k U).tensor (copiesZ k V).tensor := by
  simpa only [copiesZ] using
    OmegaBound.ADVXXZStage.famDS_const_mono
      (R := ℤ) (Finset.univ : Finset (Fin k)) h

private theorem floor_three_nat_casts_iterate (b m n : ℕ) :
    ((b : ℚ) * ((m : ℚ) * (n : ℚ))).floor.toNat = b * (m * n) := by
  have hq : (b : ℚ) * ((m : ℚ) * (n : ℚ)) = ((b * (m * n) : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hq]
  have hf : (((b * (m * n) : ℕ) : ℚ).floor) = (b * (m * n) : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (b * (m * n)) 1
  rw [hf]
  have hz : (b : ℤ) * ((m : ℤ) * (n : ℤ)) = ((b * (m * n) : ℕ) : ℤ) := by
    norm_num
  rw [hz, Int.toNat_natCast]

/-- The scaled parent inventory is the plain constituent input at that scale. -/
theorem scaledParentInventory_plain_transport (q b m : ℕ) (ε : ℚ) {w s : ℕ}
    (p : ConstituentInput w s) :
    OrdinaryTensorTransport
      (inventoryTensorZ q (scaleInventory (b : ℚ) (parentInventory p)) m ε)
      (constituentPlainInputZ q p (b * m) ε) := by
  simpa [scaleInventory, parentInventory, constituentPlainInputZ, List.map_map,
      Function.comp_def, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm,
      floor_three_nat_casts_iterate] using
    (finRange_inventory_plain_transport q m ε
      (fun t => (b : ℚ) * p.baseN t) (parentShape p) p.beta)

/-- `P` at a present stage is its plain constituent input carrier. -/
theorem stageParent_plain_transport (C : Certificate) (l : Stage C.top)
    {d : Step (wid (l.val - 1))} (hs : C.stage l = some d) (m : ℕ) (ε : ℚ) :
    OrdinaryTensorTransport (inventoryTensorZ C.q (P C l) m ε)
      (constituentPlainInputZ C.q d.input (C.D ^ 2 * m) ε) := by
  rw [show P C l = scaleInventory ((C.D : ℚ) ^ 2) (parentInventory d.input) by
    simp [P, hs]]
  simpa only [Nat.cast_pow] using
    scaledParentInventory_plain_transport C.q (C.D ^ 2) m ε d.input

private theorem floor_nat_mul_iterate (a m : ℕ) :
    (((a : ℚ) * (m : ℚ)).floor).toNat = a * m := by
  have hq : (a : ℚ) * (m : ℚ) = ((a * m : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hq]
  have hf : (((a * m : ℕ) : ℚ).floor) = (a * m : ℤ) := by
    simpa using Rat.floor_natCast_div_natCast (a * m) 1
  rw [hf]
  have hz : (a : ℤ) * (m : ℤ) = ((a * m : ℕ) : ℤ) := by
    norm_num
  rw [hz, Int.toNat_natCast]

set_option maxHeartbeats 1000000 in
-- The dependent constituent output carrier normalization needs a larger local allowance.
/-- The unscaled child inventory is the plain constituent output carrier. -/
theorem childInventory_output_transport (q m : ℕ) (ε : ℚ) {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) :
    OrdinaryTensorTransport (inventoryTensorZ q (childInventory d) m ε)
      (constituentOutputZ q d m ε) := by
  let e := (Fintype.equivFin (ConstituentTerm p)).symm
  simpa [childInventory, constituentOutputZ, constituentOutN, constituentIndex,
      constituentOutI, constituentOutJ, constituentOutK, constituentOutBeta,
      ConstituentSpec.toPaper, e, floor_nat_mul_iterate] using
    (finRange_inventory_plain_transport q m ε
      (fun i => (d.outBase (e i) : ℚ))
      (fun i => (e i).2.2.1)
      (fun W i => d.betaChild W (e i).1 (e i).2.1 (e i).2.2))

/-- `QAt` at a present stage is its plain constituent output carrier. -/
theorem stageOutput_plain_transport (C : Certificate) (l : Stage C.top)
    {d : Step (wid (l.val - 1))} (hs : C.stage l = some d) (m : ℕ) (ε : ℚ) :
    OrdinaryTensorTransport (inventoryTensorZ C.q (QAt C l) m ε)
      (constituentOutputZ C.q d.data m ε) := by
  rw [show QAt C l = childInventory d.data by simp [QAt, hs]]
  exact childInventory_output_transport C.q m ε d.data

end
end OmegaBound.ADVXXZGeneral
end

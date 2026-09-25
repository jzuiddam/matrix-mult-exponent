import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalTopAddresses

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

noncomputable def physicalTopLevel : Stage releasedOrdinaryCertificatePhysical.top :=
  ⟨3, by simp [releasedOrdinaryCertificatePhysical]⟩

theorem physical_G_entries :
    G releasedOrdinaryCertificatePhysical =
      (inventoryEnum (Fin 6 × Shape 4)).map physicalGlobalScaledEntry := by
  unfold G scaleInventory globalInventory inventoryEnum physicalGlobalScaledEntry
  simp only [List.map_map]
  rfl

theorem physical_P_top_entries :
    P releasedOrdinaryCertificatePhysical physicalTopLevel =
      (List.finRange 126).map physicalTopParentEntry := by
  have hs : releasedOrdinaryCertificatePhysical.stage physicalTopLevel =
      some releasedOrdinaryStep3 := by
    simp [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage, physicalTopLevel]
  rw [P, hs]
  unfold scaleInventory parentInventory physicalTopParentEntry
  simp only [List.map_map]
  rfl

theorem physical_top_parent_entry_ne_zero (p : Fin 126) :
    (physicalTopParentEntry p).1 ≠ 0 := by
  unfold physicalTopParentEntry
  apply mul_ne_zero
  · apply pow_ne_zero
    exact_mod_cast (ne_of_gt (show 0 < releasedOrdinaryCertificatePhysical.D by
      change 0 < ordinaryD ^ 2
      decide +kernel))
  · exact_mod_cast (ne_of_gt (releasedOrdinaryStep3.input.baseN_pos p))

theorem filter_nonzero_interior (I : Inventory) :
    (interior I).filter (fun a => decide (a.1 ≠ 0)) = interior I := by
  apply List.filter_eq_self.mpr
  intro a ha
  have hpos := (List.mem_filter.mp ha).2
  simp only [decide_eq_true_eq] at hpos ⊢
  exact ne_of_gt hpos.1

theorem physical_P_top_filter_nonzero :
    (P releasedOrdinaryCertificatePhysical physicalTopLevel).filter
        (fun a => decide (a.1 ≠ 0)) =
      P releasedOrdinaryCertificatePhysical physicalTopLevel := by
  rw [physical_P_top_entries]
  apply List.filter_eq_self.mpr
  intro a ha
  rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
  simpa using physical_top_parent_entry_ne_zero p

theorem physical_G_interior_entries :
    interior (G releasedOrdinaryCertificatePhysical) =
      ((inventoryEnum (Fin 6 × Shape 4)).filter
        (fun ru => decide (PhysicalTopActive ru))).map physicalGlobalScaledEntry := by
  rw [physical_G_entries]
  unfold interior
  apply filter_map_of_eq
  intro ru
  rfl

theorem physical_top_entries_perm :
    List.Perm (interior (G releasedOrdinaryCertificatePhysical))
      (P releasedOrdinaryCertificatePhysical physicalTopLevel) := by
  rw [physical_G_interior_entries, physical_P_top_entries]
  have hsub := (inventoryEnum_subtype_perm PhysicalTopActive).map
    physicalGlobalScaledEntry
  simp only [List.map_map, Function.comp_apply] at hsub
  have he := (inventoryEnum_equiv_perm physicalTopActiveEquiv).map
    (fun ru => physicalGlobalScaledEntry ru.1)
  have he0 : List.Perm
      ((inventoryEnum (Fin 126)).map
        (fun p => physicalGlobalScaledEntry (physicalTopActiveEquiv p).1))
      ((inventoryEnum {ru : Fin 6 × Shape 4 // PhysicalTopActive ru}).map
        (fun ru => physicalGlobalScaledEntry ru.1)) := by
    simpa only [List.map_map, Function.comp_apply] using he
  have hmap :
      (inventoryEnum (Fin 126)).map
          (fun p => physicalGlobalScaledEntry (physicalTopActiveEquiv p).1) =
        (inventoryEnum (Fin 126)).map physicalTopParentEntry := by
    apply List.map_congr_left
    intro p hp
    change physicalGlobalScaledEntry (physicalTopPair p) = physicalTopParentEntry p
    exact physical_top_entry_eq p
  have he' : List.Perm
      ((inventoryEnum (Fin 126)).map physicalTopParentEntry)
      ((inventoryEnum {ru : Fin 6 × Shape 4 // PhysicalTopActive ru}).map
        (fun ru => physicalGlobalScaledEntry ru.1)) := by
    rw [hmap] at he0
    exact he0
  have hfin := (inventoryEnum_fin_perm 126).map physicalTopParentEntry
  exact hsub.symm.trans (he'.symm.trans hfin)

theorem released_ordinary_physical_top_link :
    ∀ l : Stage releasedOrdinaryCertificatePhysical.top,
      l.val = releasedOrdinaryCertificatePhysical.top →
        InventoryEq (interior (G releasedOrdinaryCertificatePhysical))
          (P releasedOrdinaryCertificatePhysical l) := by
  intro l hl
  have hl3 : l = physicalTopLevel := by
    apply Subtype.ext
    simpa [releasedOrdinaryCertificatePhysical] using hl
  subst l
  unfold InventoryEq
  rw [filter_nonzero_interior, physical_P_top_filter_nonzero]
  exact physical_top_entries_perm

end OmegaBound.ADVXXZGeneral

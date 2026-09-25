import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalNextLinkBase

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 6000 in
-- Composing the two exhaustive-enumeration permutations unfolds a nested dependent subtype.
theorem physical_next_entries_perm :
    List.Perm (interior (QAt releasedOrdinaryCertificatePhysical physicalTopLevel))
      (P releasedOrdinaryCertificatePhysical physicalLevel2) := by
  rw [physical_Q_top_interior_entries, physical_P_level2_entries]
  have hsub := (inventoryEnum_subtype_perm OrdinaryStageActive).map
    physicalStage3ChildEntry
  simp only [List.map_map] at hsub
  have hleft :
      (inventoryEnum {x : ConstituentTerm releasedParent // OrdinaryStageActive x}).map
          (physicalStage3ChildEntry ∘ Subtype.val) =
        (inventoryEnum {x : ConstituentTerm releasedParent // OrdinaryStageActive x}).map
          (physicalStage2ParentEntry ∘ ordinaryStageActiveEquiv) := by
    apply List.map_congr_left
    intro x hx
    exact physical_stage2_entry_eq (ordinaryStageActiveEquiv x)
  rw [hleft] at hsub
  exact hsub.symm

theorem released_ordinary_physical_next_link :
    ∀ l h : Stage releasedOrdinaryCertificatePhysical.top, l.val + 1 = h.val →
      InventoryEq (interior (QAt releasedOrdinaryCertificatePhysical h))
        (P releasedOrdinaryCertificatePhysical l) := by
  intro l h hlh
  have hl : l = physicalLevel2 := by
    apply Subtype.ext
    change l.val = 2
    have hlo := l.property.1
    have hhi := h.property.2
    change h.val ≤ 3 at hhi
    omega
  have hh : h = physicalTopLevel := by
    apply Subtype.ext
    change h.val = 3
    have hlo := l.property.1
    have hhi := h.property.2
    change h.val ≤ 3 at hhi
    omega
  subst l
  subst h
  unfold InventoryEq
  rw [filter_nonzero_interior, physical_P_level2_filter_nonzero]
  exact physical_next_entries_perm

end OmegaBound.ADVXXZGeneral

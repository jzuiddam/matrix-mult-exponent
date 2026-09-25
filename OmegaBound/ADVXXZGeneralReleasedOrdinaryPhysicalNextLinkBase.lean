import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalTopLink

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

noncomputable def physicalLevel2 : Stage releasedOrdinaryCertificatePhysical.top :=
  ⟨2, by simp [releasedOrdinaryCertificatePhysical]⟩

abbrev OrdinaryStageActive (x : ConstituentTerm releasedParent) : Prop :=
  0 < releasedConstituentSpec.outBase x ∧
    0 < coord .X x.2.2.1 ∧ 0 < coord .Y x.2.2.1 ∧ 0 < coord .Z x.2.2.1

noncomputable instance instDecidableOrdinaryStageActive (x : ConstituentTerm releasedParent) :
    Decidable (OrdinaryStageActive x) := by
  unfold OrdinaryStageActive
  infer_instance

def ordinaryStageActiveEquiv :
    {x : ConstituentTerm releasedParent // OrdinaryStageActive x} ≃
      ReleasedOrdinaryOccurrence where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable def physicalStage3ChildEntry
    (x : ConstituentTerm releasedParent) : ℚ × AtomKey :=
  (((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℚ),
    ⟨2, x.2.2.1,
      fun W sigma => (releasedConstituentSpec.betaChild W x.1 x.2.1 x.2.2).prob sigma⟩)

noncomputable def physicalStage2ParentEntry
    (x : ReleasedOrdinaryOccurrence) : ℚ × AtomKey :=
  (((releasedOrdinaryCertificatePhysical.D : ℚ) ^ 2) *
      releasedConstituentSpec.outBase x.1,
    ⟨2, x.1.2.2.1,
      fun W sigma =>
        (releasedConstituentSpec.betaChild W x.1.1 x.1.2.1 x.1.2.2).prob sigma⟩)

theorem physical_stage2_entry_eq (x : ReleasedOrdinaryOccurrence) :
    physicalStage3ChildEntry x.1 = physicalStage2ParentEntry x := by
  apply Prod.ext
  · unfold physicalStage3ChildEntry physicalStage2ParentEntry
    change
      (((ordinaryD ^ 4 * releasedConstituentSpec.outBase x.1 : ℕ) : ℚ)) =
        (((ordinaryD ^ 2 : ℕ) : ℚ) ^ 2) *
          (releasedConstituentSpec.outBase x.1 : ℚ)
    push_cast
    ring
  · rfl

theorem physical_Q_top_entries :
    QAt releasedOrdinaryCertificatePhysical physicalTopLevel =
      (inventoryEnum (ConstituentTerm releasedParent)).map physicalStage3ChildEntry := by
  have hs : releasedOrdinaryCertificatePhysical.stage physicalTopLevel =
      some releasedOrdinaryStep3 := by
    simp [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage, physicalTopLevel]
  rw [QAt, hs]
  unfold childInventory inventoryEnum physicalStage3ChildEntry
  simp only [List.map_map]
  rfl

theorem physical_stage2_parent_entry_index
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :
    (((releasedOrdinaryCertificatePhysical.D : ℚ) ^ 2) *
        releasedOrdinaryStep2.input.baseN t,
      (⟨2, parentShape releasedOrdinaryStep2.input t,
        fun W sigma => (releasedOrdinaryStep2.input.beta W t).prob sigma⟩ : AtomKey)) =
      physicalStage2ParentEntry (ordinaryOccurrence t) := by
  apply Prod.ext
  · rfl
  · change
      (⟨2, parentShape releasedOrdinaryParent t,
        fun W sigma => (releasedOrdinaryParent.beta W t).prob sigma⟩ : AtomKey) =
      ⟨2, (ordinaryOccurrence t).1.2.2.1,
        fun W sigma =>
          (releasedConstituentSpec.betaChild W (ordinaryOccurrence t).1.1
            (ordinaryOccurrence t).1.2.1 (ordinaryOccurrence t).1.2.2).prob sigma⟩
    congr 1

theorem physical_P_level2_entries :
    P releasedOrdinaryCertificatePhysical physicalLevel2 =
      (inventoryEnum ReleasedOrdinaryOccurrence).map physicalStage2ParentEntry := by
  have hs : releasedOrdinaryCertificatePhysical.stage physicalLevel2 =
      some releasedOrdinaryStep2 := by
    simp [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage, physicalLevel2]
  rw [P, hs]
  unfold scaleInventory parentInventory inventoryEnum
  simp only [List.map_map]
  apply List.map_congr_left
  intro t ht
  exact physical_stage2_parent_entry_index t

theorem physical_stage3_active_iff (x : ConstituentTerm releasedParent) :
    (0 < (physicalStage3ChildEntry x).1 ∧
      0 < coord .X (physicalStage3ChildEntry x).2.2.1 ∧
      0 < coord .Y (physicalStage3ChildEntry x).2.2.1 ∧
      0 < coord .Z (physicalStage3ChildEntry x).2.2.1) ↔
      OrdinaryStageActive x := by
  have hD : 0 < ordinaryD ^ 4 := pow_pos (by decide +kernel) _
  have hmass :
      0 < (((ordinaryD ^ 4 * releasedConstituentSpec.outBase x : ℕ) : ℚ)) ↔
        0 < releasedConstituentSpec.outBase x := by
    constructor
    · intro h
      have hn : 0 < ordinaryD ^ 4 * releasedConstituentSpec.outBase x := by
        exact_mod_cast h
      exact Nat.pos_of_ne_zero fun hz => by simp [hz] at hn
    · intro h
      exact_mod_cast (Nat.mul_pos hD h)
  unfold physicalStage3ChildEntry OrdinaryStageActive
  exact and_congr hmass Iff.rfl

theorem physical_Q_top_interior_entries :
    interior (QAt releasedOrdinaryCertificatePhysical physicalTopLevel) =
      ((inventoryEnum (ConstituentTerm releasedParent)).filter
        (fun x => decide (OrdinaryStageActive x))).map physicalStage3ChildEntry := by
  rw [physical_Q_top_entries]
  unfold interior
  apply filter_map_of_eq
  intro x
  exact Bool.decide_congr (physical_stage3_active_iff x)

theorem physical_stage2_parent_entry_ne_zero (x : ReleasedOrdinaryOccurrence) :
    (physicalStage2ParentEntry x).1 ≠ 0 := by
  unfold physicalStage2ParentEntry
  apply mul_ne_zero
  · apply pow_ne_zero
    exact_mod_cast (ne_of_gt (show 0 < releasedOrdinaryCertificatePhysical.D by
      change 0 < ordinaryD ^ 2
      decide +kernel))
  · exact_mod_cast (ne_of_gt x.2.1)

theorem physical_P_level2_filter_nonzero :
    (P releasedOrdinaryCertificatePhysical physicalLevel2).filter
        (fun a => decide (a.1 ≠ 0)) =
      P releasedOrdinaryCertificatePhysical physicalLevel2 := by
  rw [physical_P_level2_entries]
  apply List.filter_eq_self.mpr
  intro a ha
  rcases List.mem_map.mp ha with ⟨x, hx, rfl⟩
  simpa using physical_stage2_parent_entry_ne_zero x

end OmegaBound.ADVXXZGeneral

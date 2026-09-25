import OmegaBound.ADVXXZGeneralReleasedOrdinaryPair

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

private def targetNodeShardRows32 (b : Fin 6) :
    List OmegaBound.ADVXXZT6SplitTargetData.TargetNode :=
  match b.val with
  | 0 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0
  | 1 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1
  | 2 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2
  | 3 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3
  | 4 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4
  | _ => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5

private theorem targetNodeShardRows_ok32 (b : Fin 6) :
    OmegaBound.ADVXXZT6SplitTargetData.NodeShardOK (918 * b.val)
      (targetNodeShardRows32 b) := by
  fin_cases b <;> first
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5_ok

private def targetNodeShardIndex32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) : Fin 6 :=
  ⟨i.val / 918, by omega⟩

private def targetNodeShardOffset32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) : Fin 918 :=
  ⟨i.val % 918, Nat.mod_lt _ (by omega)⟩

private def targetNodeByShard32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.TargetNode :=
  (targetNodeShardRows32 (targetNodeShardIndex32 i)).getD
    (targetNodeShardOffset32 i).val
    OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode

private theorem targetNodeByShard_spec32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    let d := targetNodeByShard32 i
    let released :=
      OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode
    d.kind = released.kind ∧ d.rot = released.rot ∧
      (if d.kind = .k112 ∨ d.kind = .k022 then
        released.mu = some ((d.muNum : ℚ) / ordinaryD)
       else released.mu = none) := by
  have h :=
    (targetNodeShardRows_ok32 (targetNodeShardIndex32 i)).2
      (targetNodeShardOffset32 i)
  have hi : 918 * (i.val / 918) + i.val % 918 = i.val := by
    rw [Nat.add_comm]
    exact Nat.mod_add_div i.val 918
  simpa [targetNodeByShard32, targetNodeShardIndex32,
    targetNodeShardOffset32, hi] using
      And.intro h.1 (And.intro h.2.1 h.2.2.1)

private theorem getD_six_blocks32 {alpha : Type} (d : alpha)
    (l0 l1 l2 l3 l4 l5 : List alpha)
    (h0 : l0.length = 918) (h1 : l1.length = 918)
    (h2 : l2.length = 918) (h3 : l3.length = 918)
    (h4 : l4.length = 918) (_h5 : l5.length = 918)
    (i : Nat) (hi : i < 5508) :
    (l0 ++ (l1 ++ (l2 ++ (l3 ++ (l4 ++ l5))))).getD i d =
      (match i / 918 with
       | 0 => l0 | 1 => l1 | 2 => l2 | 3 => l3 | 4 => l4 | _ => l5).getD
        (i % 918) d := by
  have hdiv : i / 918 < 6 := by omega
  have hd := Nat.mod_add_div i 918
  interval_cases hq : i / 918
  all_goals simp only [hq]
  · have h : i < l0.length := by omega
    rw [List.getD_append _ _ _ _ h]
    apply congrArg (fun n => l0.getD n d)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · have h0' : l0.length ≤ i := by omega
    have h1' : i - 918 < l1.length := by omega
    rw [List.getD_append_right _ _ _ _ h0', h0,
      List.getD_append _ _ _ _ h1']
    apply congrArg (fun n => l1.getD n d)
    have hr := Nat.sub_eq_of_eq_add hd.symm
    simpa only [hq, Nat.mul_one] using hr
  · have h0' : l0.length ≤ i := by omega
    have h1' : l1.length ≤ i - 918 := by omega
    have h2' : i - 918 - 918 < l2.length := by omega
    rw [List.getD_append_right _ _ _ _ h0', h0,
      List.getD_append_right _ _ _ _ h1', h1,
      List.getD_append _ _ _ _ h2']
    apply congrArg (fun n => l2.getD n d)
    have hr := Nat.sub_eq_of_eq_add hd.symm
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one,
      Nat.add_assoc] using hr
  · have h0' : l0.length ≤ i := by omega
    have h1' : l1.length ≤ i - 918 := by omega
    have h2' : l2.length ≤ i - 918 - 918 := by omega
    have h3' : i - 918 - 918 - 918 < l3.length := by omega
    rw [List.getD_append_right _ _ _ _ h0', h0,
      List.getD_append_right _ _ _ _ h1', h1,
      List.getD_append_right _ _ _ _ h2', h2,
      List.getD_append _ _ _ _ h3']
    apply congrArg (fun n => l3.getD n d)
    have hr := Nat.sub_eq_of_eq_add hd.symm
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one,
      Nat.add_assoc] using hr
  · have h0' : l0.length ≤ i := by omega
    have h1' : l1.length ≤ i - 918 := by omega
    have h2' : l2.length ≤ i - 918 - 918 := by omega
    have h3' : l3.length ≤ i - 918 - 918 - 918 := by omega
    have h4' : i - 918 - 918 - 918 - 918 < l4.length := by omega
    rw [List.getD_append_right _ _ _ _ h0', h0,
      List.getD_append_right _ _ _ _ h1', h1,
      List.getD_append_right _ _ _ _ h2', h2,
      List.getD_append_right _ _ _ _ h3', h3,
      List.getD_append _ _ _ _ h4']
    apply congrArg (fun n => l4.getD n d)
    have hr := Nat.sub_eq_of_eq_add hd.symm
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one,
      Nat.add_assoc] using hr
  · have h0' : l0.length ≤ i := by omega
    have h1' : l1.length ≤ i - 918 := by omega
    have h2' : l2.length ≤ i - 918 - 918 := by omega
    have h3' : l3.length ≤ i - 918 - 918 - 918 := by omega
    have h4' : l4.length ≤ i - 918 - 918 - 918 - 918 := by omega
    rw [List.getD_append_right _ _ _ _ h0', h0,
      List.getD_append_right _ _ _ _ h1', h1,
      List.getD_append_right _ _ _ _ h2', h2,
      List.getD_append_right _ _ _ _ h3', h3,
      List.getD_append_right _ _ _ _ h4', h4]
    apply congrArg (fun n => l5.getD n d)
    have hr := Nat.sub_eq_of_eq_add hd.symm
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one,
      Nat.add_assoc] using hr

private theorem targetNodeRows_getD_eq_byShard32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode =
      targetNodeByShard32 i := by
  have h := getD_six_blocks32
    OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0_ok).1
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1_ok).1
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2_ok).1
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3_ok).1
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4_ok).1
    (OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5_ok).1 i.val i.isLt
  simpa only [OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows,
    targetNodeByShard32, targetNodeShardRows32, targetNodeShardIndex32,
    targetNodeShardOffset32, List.append_assoc] using h

private theorem targetNode_eq_rowsGetD32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.targetNode i =
      OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode := by
  simp [OmegaBound.ADVXXZT6SplitTargetData.targetNode,
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray,
    Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The six checked target shards attach every symbolic target node to the
corresponding released term's kind, rotation, and exact rational mu. -/
theorem released_ordinary_target_metadata32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode i
    let released :=
      OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode
    d.kind = released.kind ∧ d.rot = released.rot ∧
      (if d.kind = .k112 ∨ d.kind = .k022 then
        released.mu = some ((d.muNum : ℚ) / ordinaryD)
       else released.mu = none) := by
  rw [targetNode_eq_rowsGetD32, targetNodeRows_getD_eq_byShard32]
  exact targetNodeByShard_spec32 i

theorem releasedTable_getD_eq_dataById32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode =
      OmegaBound.ADVXXZT7SpecialInventory.dataById i := by
  unfold OmegaBound.ADVXXZT7SpecialInventory.dataById
  rw [List.getD_eq_getElem _ _ (by
    rw [OmegaBound.ADVXXZT7SpecialInventory.natural_table_law.1]
    exact i.isLt)]
  rfl

/-- The same attachment stated through the typed lookup used by the released
level-two aggregate. -/
theorem released_ordinary_target_metadata_dataById32
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode i
    let released := OmegaBound.ADVXXZT7SpecialInventory.dataById i
    d.kind = released.kind ∧ d.rot = released.rot ∧
      (if d.kind = .k112 ∨ d.kind = .k022 then
        released.mu = some ((d.muNum : ℚ) / ordinaryD)
       else released.mu = none) := by
  rw [← releasedTable_getD_eq_dataById32]
  exact released_ordinary_target_metadata32 i

end OmegaBound.ADVXXZGeneral

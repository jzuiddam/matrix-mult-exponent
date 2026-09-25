import OmegaBound.ADVXXZGeneralReleasedOrdinaryAdmissible
import OmegaBound.ADVXXZT7EnrichedTable
import OmegaBound.ADVXXZT7Round20ExactSplit

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 100000
namespace OmegaBound.ADVXXZGeneral

private def ordinaryPairMatches (v : Shape 2) (W : Side) (sigma : Chunk 2)
    (u : OrdinaryChild v) : Prop :=
  (@leftHalf 1 sigma 0).val = coord W u.1 ∧
    (@rightHalf 1 sigma 0).val = coord W v - coord W u.1

private instance (v : Shape 2) (W : Side) (sigma : Chunk 2)
    (u : OrdinaryChild v) : Decidable (ordinaryPairMatches v W sigma u) := by
  unfold ordinaryPairMatches
  infer_instance

private def ordinaryPairLargeCount (v : Shape 2) (W : Side) (sigma : Chunk 2) : ℕ :=
  (Finset.univ.filter fun u : OrdinaryChild v =>
    decide (ordinaryPairMatches v W sigma u ∧ coord (ordinaryLargeSide v) u.1 = 1)).card

private def ordinaryPairOtherCount (v : Shape 2) (W : Side) (sigma : Chunk 2) : ℕ :=
  (Finset.univ.filter fun u : OrdinaryChild v =>
    decide (ordinaryPairMatches v W sigma u ∧ ¬ coord (ordinaryLargeSide v) u.1 = 1)).card

private def expectedLargeAt (side : Fin 3) (word : Fin 9) : ℕ :=
  match side.val, word.val with
  | 0, 1 | 0, 3 | 1, 1 | 1, 3 => 1
  | 2, 4 => 2
  | _, _ => 0

private def expectedOtherAt (side : Fin 3) (word : Fin 9) : ℕ :=
  match side.val, word.val with
  | 0, 1 | 0, 3 | 1, 1 | 1, 3 => 1
  | 2, 2 | 2, 6 => 1
  | _, _ => 0

private def expectedLargeCount (kind : OmegaBound.ADVXXZLevel2Closure.Kind)
    (rot : Fin 3) (W : Side) (sigma : Chunk 2) : ℕ :=
  if kind = .k112 then
    expectedLargeAt
      (OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseSide ⟨kind, rot, 0⟩
        (OmegaBound.ADVXXZT6Round82.sideIndex W))
      (OmegaBound.ADVXXZT6SplitTargetData.wordId sigma)
  else 0

private def expectedOtherCount (kind : OmegaBound.ADVXXZLevel2Closure.Kind)
    (rot : Fin 3) (W : Side) (sigma : Chunk 2) : ℕ :=
  if kind = .k112 then
    expectedOtherAt
      (OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseSide ⟨kind, rot, 0⟩
        (OmegaBound.ADVXXZT6Round82.sideIndex W))
      (OmegaBound.ADVXXZT6SplitTargetData.wordId sigma)
  else 0

private theorem ordinary_pair_child_count_table
    (v : Shape 2) (hx : 0 < coord .X v) (hy : 0 < coord .Y v)
    (hz : 0 < coord .Z v) (kind : OmegaBound.ADVXXZLevel2Closure.Kind)
    (rot : Fin 3)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt kind rot)
    (W : Side) (sigma : Chunk 2) :
    ordinaryPairLargeCount v W sigma = expectedLargeCount kind rot W sigma ∧
      ordinaryPairOtherCount v W sigma = expectedOtherCount kind rot W sigma := by
  cases kind <;> revert v rot W sigma <;> decide +kernel

private theorem interior_shape_kind
    (v : Shape 2) (hx : 0 < coord .X v) (hy : 0 < coord .Y v)
    (hz : 0 < coord .Z v) (kind : OmegaBound.ADVXXZLevel2Closure.Kind)
    (rot : Fin 3)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt kind rot) :
    kind = .k112 := by
  have hsX := congrArg Prod.fst hshape
  have hsY := congrArg (fun s => s.2.1) hshape
  have hsZ := congrArg (fun s => s.2.2) hshape
  cases kind <;> fin_cases rot
  all_goals
    simp only [OmegaBound.ADVXXZLevel2Closure.shapeAt,
      OmegaBound.ADVXXZLevel2Closure.standardShape,
      OmegaBound.ADVXXZLevel2Closure.rotateShape, Function.iterate_succ_apply,
      Function.iterate_zero_apply] at hsX hsY hsZ
  all_goals simp_all <;> omega

private def ordinaryK112BaseNum (D mu : ℕ) (side : Fin 3) (word : Fin 9) : ℕ :=
  match side.val, word.val with
  | 0, 1 | 0, 3 | 1, 1 | 1, 3 => D / 2
  | 2, 2 | 2, 6 => mu
  | 2, 4 => D - 2 * mu
  | _, _ => 0

private theorem target_base_num_k112 (rot : Fin 3) (mu : ℕ)
    (side : Fin 3) (word : Fin 9) :
    OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseNum ⟨.k112, rot, mu⟩ side word =
      ordinaryK112BaseNum OmegaBound.ADVXXZT6SplitTargetData.targetDen mu side word := by
  fin_cases side <;> fin_cases word <;> rfl

private theorem ordinary_k112_base_num (D mu : ℕ) (hmu : mu ≤ D / 2)
    (heven : 2 * (D / 2) = D) (side : Fin 3) (word : Fin 9) :
    ordinaryK112BaseNum D mu side word =
      expectedLargeAt side word * (D / 2 - mu) + expectedOtherAt side word * mu := by
  have hadd : D / 2 - mu + mu = D / 2 := Nat.sub_add_cancel hmu
  have hdouble : D - 2 * mu = 2 * (D / 2 - mu) := by
    calc
      D - 2 * mu = 2 * (D / 2) - 2 * mu :=
        congrArg (fun n : ℕ => n - 2 * mu) heven.symm
      _ = 2 * (D / 2 - mu) := (Nat.mul_sub_left_distrib 2 (D / 2) mu).symm
  fin_cases side <;> fin_cases word <;>
    simp [ordinaryK112BaseNum, expectedLargeAt, expectedOtherAt, hadd, hdouble]

set_option maxHeartbeats 1000000 in
-- Symbolic finite sums need extra reduction time; no released table is evaluated here.
private theorem ordinary_pair_numerator_symbolic
    (v : Shape 2) (hx : 0 < coord .X v) (hy : 0 < coord .Y v)
    (hz : 0 < coord .Z v)
    (d : OmegaBound.ADVXXZT6SplitTargetData.TargetNode)
    (hshape :
      (coord .X v, coord .Y v, coord .Z v) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt d.kind d.rot)
    (hmu : d.muNum <= ordinaryD / 2) (W : Side) (sigma : Chunk 2) :
    (d.raw (OmegaBound.ADVXXZT6Round82.sideIndex W)).nums
        (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv sigma) =
      ∑ u : OrdinaryChild v,
        (if coord (ordinaryLargeSide v) u.1 = 1
          then ordinaryD / 2 - d.muNum else d.muNum) *
        (if (@leftHalf 1 sigma 0).val = coord W u.1 then 1 else 0) *
        (if (@rightHalf 1 sigma 0).val = coord W v - coord W u.1 then 1 else 0) := by
  have hcounts := ordinary_pair_child_count_table v hx hy hz d.kind d.rot hshape W sigma
  have hsum :
      (∑ u : OrdinaryChild v,
        (if coord (ordinaryLargeSide v) u.1 = 1
          then ordinaryD / 2 - d.muNum else d.muNum) *
        (if (@leftHalf 1 sigma 0).val = coord W u.1 then 1 else 0) *
        (if (@rightHalf 1 sigma 0).val = coord W v - coord W u.1 then 1 else 0)) =
      ordinaryPairLargeCount v W sigma * (ordinaryD / 2 - d.muNum) +
        ordinaryPairOtherCount v W sigma * d.muNum := by
    simp only [ordinaryPairLargeCount, ordinaryPairOtherCount, ordinaryPairMatches]
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_mul,
      Finset.sum_mul]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hleft : (@leftHalf 1 sigma 0).val = coord W u.1 <;>
      by_cases hright :
        (@rightHalf 1 sigma 0).val = coord W v - coord W u.1 <;>
      by_cases hl : coord (ordinaryLargeSide v) u.1 = 1 <;>
      simp [hleft, hright, hl]
  change OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseNum d
      (OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseSide d
        (OmegaBound.ADVXXZT6Round82.sideIndex W))
      (OmegaBound.ADVXXZT6SplitTargetData.wordId sigma) = _
  rw [hsum, hcounts.1, hcounts.2]
  have hkind := interior_shape_kind v hx hy hz d.kind d.rot hshape
  rcases d with ⟨kind, rot, mu⟩
  change mu ≤ ordinaryD / 2 at hmu
  change kind = .k112 at hkind
  subst kind
  rw [target_base_num_k112]
  have htarget : OmegaBound.ADVXXZT6SplitTargetData.targetDen = ordinaryD := rfl
  rw [htarget]
  have heven : 2 * (ordinaryD / 2) = ordinaryD := by decide +kernel
  simpa [expectedLargeCount, expectedOtherCount] using
    ordinary_k112_base_num ordinaryD mu hmu heven
      (OmegaBound.ADVXXZT6SplitTargetData.TargetNode.baseSide ⟨.k112, rot, mu⟩
        (OmegaBound.ADVXXZT6Round82.sideIndex W))
      (OmegaBound.ADVXXZT6SplitTargetData.wordId sigma)

set_option maxRecDepth 2000

private def targetNodeShardRows (b : Fin 6) :
    List OmegaBound.ADVXXZT6SplitTargetData.TargetNode :=
  match b.val with
  | 0 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0
  | 1 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1
  | 2 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2
  | 3 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3
  | 4 => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4
  | _ => OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5

private theorem targetNodeShardRows_ok (b : Fin 6) :
    OmegaBound.ADVXXZT6SplitTargetData.NodeShardOK (918 * b.val)
      (targetNodeShardRows b) := by
  fin_cases b <;> first
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows0_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows1_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows2_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows3_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows4_ok
  | exact OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows5_ok

private def targetNodeShardIndex
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) : Fin 6 :=
  ⟨i.val / 918, by omega⟩

private def targetNodeShardOffset
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) : Fin 918 :=
  ⟨i.val % 918, Nat.mod_lt _ (by omega)⟩

private def targetNodeByShard
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.TargetNode :=
  (targetNodeShardRows (targetNodeShardIndex i)).getD
    (targetNodeShardOffset i).val OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode

private theorem targetNodeByShard_metadata
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    let d := targetNodeByShard i
    let released := OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD i.val
      OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode
    d.kind = released.kind ∧ d.rot = released.rot := by
  have h := (targetNodeShardRows_ok (targetNodeShardIndex i)).2 (targetNodeShardOffset i)
  have hi : 918 * (i.val / 918) + i.val % 918 = i.val := by
    rw [Nat.add_comm]
    exact Nat.mod_add_div i.val 918
  simpa [targetNodeByShard, targetNodeShardIndex, targetNodeShardOffset, hi] using
    And.intro h.1 h.2.1

private theorem getD_six_blocks {α : Type} (d : α) (l0 l1 l2 l3 l4 l5 : List α)
    (h0 : l0.length = 918) (h1 : l1.length = 918) (h2 : l2.length = 918)
    (h3 : l3.length = 918) (h4 : l4.length = 918) (_h5 : l5.length = 918)
    (i : ℕ) (hi : i < 5508) :
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
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one, Nat.add_assoc] using hr
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
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one, Nat.add_assoc] using hr
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
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one, Nat.add_assoc] using hr
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
    simpa only [Nat.sub_sub, hq, Nat.mul_succ, Nat.mul_one, Nat.add_assoc] using hr

private theorem targetNodeRows_getD_eq_byShard
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode =
      targetNodeByShard i := by
  have h := getD_six_blocks OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode
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
    targetNodeByShard, targetNodeShardRows, targetNodeShardIndex,
    targetNodeShardOffset, List.append_assoc] using h

private theorem targetNode_eq_rowsGetD
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT6SplitTargetData.targetNode i =
      OmegaBound.ADVXXZT6SplitTargetData.targetNodeRows.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyTargetNode := by
  simp [OmegaBound.ADVXXZT6SplitTargetData.targetNode,
    OmegaBound.ADVXXZT6SplitTargetData.targetNodeArray,
    Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem releasedTable_getD_eq_releasedAt
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZReleasedTree.releasedLevel2TermDataTable.getD i.val
        OmegaBound.ADVXXZT6SplitTargetData.dummyReleasedNode =
      OmegaBound.ADVXXZT7Enriched.releasedAt i.val := by
  rw [OmegaBound.ADVXXZT7SpecialReconstruction.releasedAt_eq_dataById]
  unfold OmegaBound.ADVXXZT7SpecialInventory.dataById
  rw [List.getD_eq_getElem _ _ (by
    rw [OmegaBound.ADVXXZT7SpecialInventory.natural_table_law.1]
    exact i.isLt)]
  rfl

private theorem targetNode_metadata
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    let d := OmegaBound.ADVXXZT6SplitTargetData.targetNode i
    let released := OmegaBound.ADVXXZT7Enriched.releasedAt i.val
    d.kind = released.kind ∧ d.rot = released.rot := by
  rw [targetNode_eq_rowsGetD, targetNodeRows_getD_eq_byShard]
  have h := targetNodeByShard_metadata i
  rw [releasedTable_getD_eq_releasedAt] at h
  exact h

private theorem enriched_parentShape_eq_shapeAt
    (d : OmegaBound.ADVXXZReleasedTree.ReleasedLevel2TermData) :
    OmegaBound.ADVXXZT7Enriched.parentShape d =
      OmegaBound.ADVXXZLevel2Closure.shapeAt d.kind d.rot := by
  rcases d with ⟨node, kind, rot, frac, mu⟩
  cases kind <;> fin_cases rot <;> rfl

private theorem targetNode_shapeAt
    (i : OmegaBound.ADVXXZCertSemantic.Level2TermId) :
    OmegaBound.ADVXXZT2.l2sh i.val =
      OmegaBound.ADVXXZLevel2Closure.shapeAt
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).kind
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).rot := by
  have hr := (OmegaBound.ADVXXZT7Enriched.enrichedRow_ok i).2.1
  have hn : (OmegaBound.ADVXXZT7Enriched.enrichedRow i).node = i := by
    simpa [OmegaBound.ADVXXZT7Round5JointHash.childRow] using
      OmegaBound.ADVXXZT7Round20ExactSplit.childRow_node i
  rw [hn, enriched_parentShape_eq_shapeAt] at hr
  have hm := targetNode_metadata i
  rw [hm.1, hm.2]
  exact hr

private theorem nodeForPattern_childIndex
    (t : Fin 126) (r : Fin 6) (u : ChildShape releasedParent t) :
    OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1 =
      OmegaBound.ADVXXZT2.leftOcc
        (OmegaBound.ADVXXZT6SplitTargetData.occurrence t r
          (OmegaBound.ADVXXZT6Round78.childIndex t u)) := by
  have hk := OmegaBound.ADVXXZT6Round82.kidPat_childIndex t u
  have hpat : OmegaBound.ADVXXZT6SplitTargetData.patShape
      (OmegaBound.ADVXXZT6Selection.kidPat t
        (OmegaBound.ADVXXZT6Round78.childIndex t u)) =
      OmegaBound.ADVXXZT6Round78.childTriple t u := by
    rw [hk]
    rfl
  rw [← hk]
  unfold OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
  rw [if_pos]
  · apply congrArg OmegaBound.ADVXXZT2.leftOcc
    apply Fin.ext
    rw [hpat]
    simp [OmegaBound.ADVXXZT6SplitTargetData.occurrence,
      OmegaBound.ADVXXZT6Round78.childIndex,
      OmegaBound.ADVXXZT6Round78.childIndexNat]
  · have hb := OmegaBound.ADVXXZT6Round78.releasedChildIndexBounds t u
    have hfound := @List.findIdx_getElem _
      (fun v => v == OmegaBound.ADVXXZT6Round78.childTriple t u)
      (OmegaBound.ADVXXZT2.parKids t.1) hb
    have heq :
        (OmegaBound.ADVXXZT2.parKids t.1)[
          OmegaBound.ADVXXZT6Round78.childIndexNat t u]'hb =
            OmegaBound.ADVXXZT6Round78.childTriple t u := by
      simpa [OmegaBound.ADVXXZT6Round78.childIndexNat] using hfound
    rw [hpat, ← heq]
    exact List.getElem_mem hb

private theorem nodeForPattern_shape
    (t : Fin 126) (r : Fin 6) (u : ChildShape releasedParent t) :
    OmegaBound.ADVXXZT2.l2sh
        (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1).val =
      (coord .X u.1, coord .Y u.1, coord .Z u.1) := by
  rw [nodeForPattern_childIndex]
  have hf := OmegaBound.ADVXXZT6SplitTargetData.fine_index_ok t r
    (OmegaBound.ADVXXZT6Round78.childIndex t u)
  unfold OmegaBound.ADVXXZT2.leftOcc
  rw [hf.2.2.2.1]
  have hk := OmegaBound.ADVXXZT6Round82.kidPat_childIndex t u
  have hc := congrArg
    (fun z : Shape 2 => (coord .X z, coord .Y z, coord .Z z)) hk
  simpa [OmegaBound.ADVXXZT6Selection.kidPat, coord] using hc

theorem released_child_target_shape (t : Fin 126) (r : Fin 6)
    (u : ChildShape releasedParent t) :
    (coord .X u.1, coord .Y u.1, coord .Z u.1) =
      OmegaBound.ADVXXZLevel2Closure.shapeAt
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode
          (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1)).kind
        (OmegaBound.ADVXXZT6SplitTargetData.targetNode
          (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1)).rot :=
  (nodeForPattern_shape t r u).symm.trans
    (targetNode_shapeAt
      (OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern r t u.1))

/-- The released width-two pair table follows from one symbolic identity in its `muNum`.
The only finite computation above is over the fifteen shapes and nine width-two words. -/
theorem ordinary_pair_numerator_ok : OrdinaryPairNumeratorOK := by
  intro x hx hy hz W sigma
  let i := OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern
    x.2.1 x.1 x.2.2.1
  have hshape :
      (coord .X x.2.2.1, coord .Y x.2.2.1, coord .Z x.2.2.1) =
        OmegaBound.ADVXXZLevel2Closure.shapeAt
          (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).kind
          (OmegaBound.ADVXXZT6SplitTargetData.targetNode i).rot :=
    (nodeForPattern_shape x.1 x.2.1 x.2.2).symm.trans (targetNode_shapeAt i)
  have h := ordinary_pair_numerator_symbolic x.2.2.1 hx hy hz
    (OmegaBound.ADVXXZT6SplitTargetData.targetNode i) hshape
    (ordinary_mu_bound i) W sigma
  simpa only [releasedConstituentSpec,
    OmegaBound.ADVXXZT6Round82.certificateBetaChild,
    OmegaBound.ADVXXZT6Round82.certificateBetaChildAt,
    OmegaBound.ADVXXZT6Round82.releasedChildRawAt,
    OmegaBound.ADVXXZT6SplitTargetData.fineRaw,
    OmegaBound.ADVXXZT6Round82.kidPat_childIndex,
    OmegaBound.ADVXXZT6SplitTargetData.RawTarget.toDist] using h

/-- Stage two's pair-mixture law, obtained by dividing the symbolic numerator identity by
the common released denominator. -/
theorem ordinary_pair_mixture (W : Side)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (sigma : Chunk 2) :
    (releasedOrdinaryData2.betaRegion W t r).prob sigma =
      ∑ u, (releasedOrdinaryData2.alpha t r).prob u *
        (releasedOrdinaryData2.betaChild W t r u).prob (leftHalf sigma) *
        (releasedOrdinaryData2.betaChild W t r
          (complement releasedOrdinaryParent t u)).prob (rightHalf sigma) := by
  have hn := ordinary_pair_numerator_ok (ordinaryOccurrence t).1
    (ordinaryOccurrence t).2.2.1 (ordinaryOccurrence t).2.2.2.1
    (ordinaryOccurrence t).2.2.2.2 W sigma
  have hDnat : ordinaryD ≠ 0 := Nat.ne_of_gt (by decide +kernel)
  have hD : (ordinaryD : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDnat
  change (releasedOrdinaryParent.beta W t).prob sigma =
    ∑ u, (ordinaryAlphaDist (ordinaryOccurrence t).1.2.2.1
          (ordinaryOccurrence t).2.2.1 (ordinaryOccurrence t).2.2.2.1
          (ordinaryOccurrence t).2.2.2.2 (ordinaryTarget t).muNum
          (ordinaryTarget_mu_bound t)).prob u *
      (ordinaryChildBeta W u.1).prob (leftHalf sigma) *
      (ordinaryChildBeta W (complement releasedOrdinaryParent t u).1).prob
        (rightHalf sigma)
  simp only [RatDist.prob, ordinaryAlphaDist, ordinaryChildBeta, Nat.cast_one, div_one]
  simp_rw [ordinary_complement_coord]
  rw [show (releasedOrdinaryParent.beta W t).den = ordinaryD by rfl]
  push_cast
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hD]
  have hnQ := congrArg (fun n : ℕ => (n : ℚ)) hn
  push_cast at hnQ
  simpa only [releasedOrdinaryParent, ordinaryTarget] using hnQ

theorem released_ordinary_stage2_roles :
    EnumeratesPermutations releasedOrdinaryData2.perm :=
  releasedPerm_enumerates

theorem released_ordinary_stage2_admissible :
    ConstituentAdmissibleAt releasedOrdinaryData2 (ordinaryD ^ 4) where
  roles := released_ordinary_stage2_roles
  mixture := by
    intro W t sigma
    exact ordinary_mixture W t sigma
  pair_mixture := ordinary_pair_mixture
  regional_support := ordinary_regional_support
  child_support := ordinary_child_support
  child_boundary := by
    intro t r u
    exact ordinary_child_boundary u.1
  out_eq := ordinary_out_eq

end OmegaBound.ADVXXZGeneral

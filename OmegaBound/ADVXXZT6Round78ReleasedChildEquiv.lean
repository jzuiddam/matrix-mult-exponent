import OmegaBound.ADVXXZT6Round78ReleasedIndexBase

/-! # Released child-row equivalences -/

set_option maxRecDepth 1000000

namespace OmegaBound.ADVXXZT6Round78

open ADVXXZPaper
open ADVXXZT9R16PositiveParents (releasedPositiveInput)

noncomputable def childIndex (t : Fin 126) (u : ChildShape releasedPositiveInput t) :
    Fin (ADVXXZT2.parKids t.1).length :=
  ⟨childIndexNat t u, releasedChildIndexBounds t u⟩

theorem childIndex_injective (t : Fin 126) : Function.Injective (childIndex t) := by
  intro a b h
  have hn : childIndexNat t a = childIndexNat t b := congrArg Fin.val h
  have ha0 := @List.findIdx_getElem _
    (fun v => v == childTriple t a) (ADVXXZT2.parKids t.1)
    (releasedChildIndexBounds t a)
  have hb0 := @List.findIdx_getElem _
    (fun v => v == childTriple t b) (ADVXXZT2.parKids t.1)
    (releasedChildIndexBounds t b)
  have ha :
      (ADVXXZT2.parKids t.1)[childIndexNat t a]'(releasedChildIndexBounds t a) =
        childTriple t a := by
    simpa [childIndexNat] using ha0
  have hb :
      (ADVXXZT2.parKids t.1)[childIndexNat t b]'(releasedChildIndexBounds t b) =
        childTriple t b := by
    simpa [childIndexNat] using hb0
  have hab : childTriple t a = childTriple t b := by
    calc
      childTriple t a =
          (ADVXXZT2.parKids t.1)[childIndexNat t a]'(releasedChildIndexBounds t a) :=
        ha.symm
      _ = (ADVXXZT2.parKids t.1)[childIndexNat t b]'(releasedChildIndexBounds t b) := by
        simpa only [hn]
      _ = childTriple t b := hb
  have hx : coord .X a.1 = coord .X b.1 := congrArg Prod.fst hab
  have hy : coord .Y a.1 = coord .Y b.1 := congrArg (fun q => q.2.1) hab
  have hz : coord .Z a.1 = coord .Z b.1 := congrArg (fun q => q.2.2) hab
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hx
  · apply Prod.ext
    · apply Fin.ext
      exact hy
    · apply Fin.ext
      exact hz

noncomputable def ReleasedChildCardinality : Prop :=
  ∀ t : Fin 126,
    Fintype.card (ChildShape releasedPositiveInput t) = (ADVXXZT2.parKids t.1).length

noncomputable instance : Decidable ReleasedChildCardinality := by
  unfold ReleasedChildCardinality
  infer_instance

/-- One bounded kernel census: the paper subtype and released row have equal cardinality. -/
theorem releasedChildCardinality : ReleasedChildCardinality := by
  decide +kernel

theorem releasedChildIndexBijective (t : Fin 126) : Function.Bijective (childIndex t) :=
  (Fintype.bijective_iff_injective_and_card (childIndex t)).2
    ⟨childIndex_injective t, by simpa using releasedChildCardinality t⟩

noncomputable def childRowEquiv (t : Fin 126) :
    ChildShape releasedPositiveInput t ≃ Fin (ADVXXZT2.parKids t.1).length :=
  Equiv.ofBijective (childIndex t) (releasedChildIndexBijective t)

end OmegaBound.ADVXXZT6Round78

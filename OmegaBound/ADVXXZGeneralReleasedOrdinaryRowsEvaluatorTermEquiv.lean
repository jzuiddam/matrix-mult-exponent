import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorTargetBridge
import OmegaBound.ADVXXZGeneralReleasedOrdinaryOccurrenceCensus

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 3000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

/-- The explicit released parent/region/child address in the 5,508-row
incidence census. -/
noncomputable def releasedTermOccurrence32
    (x : ConstituentTerm releasedParent) : OmegaBound.ADVXXZT2.Occ :=
  OmegaBound.ADVXXZT6SplitTargetData.occurrence x.1 x.2.1
    (OmegaBound.ADVXXZT6Round78.childIndex x.1 x.2.2)

/-- Send a constituent address to its left released level-two node. -/
noncomputable def releasedTermNode32
    (x : ConstituentTerm releasedParent) :
    OmegaBound.ADVXXZCertSemantic.Level2TermId :=
  OmegaBound.ADVXXZT2.leftOcc (releasedTermOccurrence32 x)

theorem releasedTermNode_eq_nodeForPattern32
    (x : ConstituentTerm releasedParent) :
    releasedTermNode32 x =
      OmegaBound.ADVXXZT6SplitTargetData.nodeForPattern x.2.1 x.1 x.2.2.1 := by
  unfold releasedTermNode32 releasedTermOccurrence32
  exact (released_nodeForPattern_childIndex x.1 x.2.1 x.2.2).symm

theorem releasedTermNode_injective32 : Function.Injective releasedTermNode32 := by
  rintro ⟨p, r, u⟩ ⟨q, s, v⟩ hnode
  have hocc :
      releasedTermOccurrence32 ⟨p, r, u⟩ =
        releasedTermOccurrence32 ⟨q, s, v⟩ :=
    OmegaBound.ADVXXZT2.leftOcc_bijective.1 (by
      simpa only [releasedTermNode32] using hnode)
  have hp := OmegaBound.ADVXXZT6SplitTargetData.fine_index_ok p r
    (OmegaBound.ADVXXZT6Round78.childIndex p u)
  have hq := OmegaBound.ADVXXZT6SplitTargetData.fine_index_ok q s
    (OmegaBound.ADVXXZT6Round78.childIndex q v)
  change
    let row := OmegaBound.ADVXXZT2.rowOf
      (releasedTermOccurrence32 ⟨p, r, u⟩)
    row.parent = p ∧ row.region = r ∧
      row.coordinate.val =
        (OmegaBound.ADVXXZT6Round78.childIndex p u).val ∧
      _ at hp
  change
    let row := OmegaBound.ADVXXZT2.rowOf
      (releasedTermOccurrence32 ⟨q, s, v⟩)
    row.parent = q ∧ row.region = s ∧
      row.coordinate.val =
        (OmegaBound.ADVXXZT6Round78.childIndex q v).val ∧
      _ at hq
  rw [hocc] at hp
  have hpq : p = q := hp.1.symm.trans hq.1
  subst q
  have hrs : r = s := hp.2.1.symm.trans hq.2.1
  subst s
  have hindex :
      OmegaBound.ADVXXZT6Round78.childIndex p u =
        OmegaBound.ADVXXZT6Round78.childIndex p v :=
    Fin.ext (hp.2.2.1.symm.trans hq.2.2.1)
  have huv := OmegaBound.ADVXXZT6Round78.childIndex_injective p hindex
  subst v
  rfl

theorem releasedTermNode_bijective32 : Function.Bijective releasedTermNode32 := by
  apply (Fintype.bijective_iff_injective_and_card releasedTermNode32).2
  refine ⟨releasedTermNode_injective32, ?_⟩
  change Fintype.card (ConstituentTerm releasedParent) = Fintype.card (Fin 5508)
  rw [releasedConstituentTerm_card, Fintype.card_fin]

/-- The released incidence inventory gives a concrete bijection from every
constituent address to exactly one released level-two table row. -/
noncomputable def releasedTermEquiv32 :
    ConstituentTerm releasedParent ≃
      OmegaBound.ADVXXZCertSemantic.Level2TermId :=
  Equiv.ofBijective releasedTermNode32 releasedTermNode_bijective32

@[simp] theorem releasedTermEquiv32_apply
    (x : ConstituentTerm releasedParent) :
    releasedTermEquiv32 x = releasedTermNode32 x := rfl

end OmegaBound.ADVXXZGeneral

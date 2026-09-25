import OmegaBound.ADVXXZGeneralCertScaleV22
import Mathlib.Data.Bool.Basic

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The same `Fintype.equivFin` occurrence enumeration used by the inventory definitions. -/
noncomputable def inventoryEnum (alpha : Type*) [Fintype alpha] : List alpha :=
  (List.finRange (Fintype.card alpha)).map (Fintype.equivFin alpha).symm

@[simp] theorem mem_inventoryEnum {alpha : Type*} [Fintype alpha] (x : alpha) :
    x ∈ inventoryEnum alpha := by
  apply List.mem_map.mpr
  refine ⟨Fintype.equivFin alpha x, List.mem_finRange _, ?_⟩
  exact (Fintype.equivFin alpha).symm_apply_apply x

theorem nodup_inventoryEnum {alpha : Type*} [Fintype alpha] :
    (inventoryEnum alpha).Nodup := by
  unfold inventoryEnum
  exact (List.nodup_finRange _).map (Fintype.equivFin alpha).symm.injective

/-- Canonical finite enumerations are permutation-invariant under an equivalence. -/
theorem inventoryEnum_equiv_perm {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] (e : alpha ≃ beta) :
    List.Perm ((inventoryEnum alpha).map e) (inventoryEnum beta) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup_inventoryEnum.map e.injective
  · exact nodup_inventoryEnum
  · ext x
    simp only [List.mem_toFinset, List.mem_map, mem_inventoryEnum, true_and]
    simpa using e.surjective x

/-- Filtering an exhaustive enumeration is the same occurrence list as enumerating its subtype. -/
theorem inventoryEnum_subtype_perm {alpha : Type*} [Fintype alpha]
    (P : alpha → Prop) [DecidablePred P] :
    List.Perm ((inventoryEnum {x : alpha // P x}).map Subtype.val)
      ((inventoryEnum alpha).filter (fun x => decide (P x))) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup_inventoryEnum.map Subtype.val_injective
  · exact nodup_inventoryEnum.filter _
  · ext x
    simp

theorem inventoryEnum_fin_perm (n : ℕ) :
    List.Perm (inventoryEnum (Fin n)) (List.finRange n) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact nodup_inventoryEnum
  · exact List.nodup_finRange _
  · ext x
    simp

/-- A pointwise predicate pullback commutes with filtering a mapped occurrence list. -/
theorem filter_map_of_eq {alpha beta : Type*} (f : alpha → beta)
    (p : alpha → Bool) (q : beta → Bool) (h : ∀ x, q (f x) = p x)
    (xs : List alpha) :
    (xs.map f).filter q = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      rw [h x]
      cases hp : p x <;> simp [hp, ih]

end OmegaBound.ADVXXZGeneral

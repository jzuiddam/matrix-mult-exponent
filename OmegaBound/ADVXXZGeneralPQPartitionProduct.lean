import OmegaBound.ADVXXZGeneralAmend25Parent

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem partition_reindex_count
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (x : ι → α)
    (c : κ) (a : α) :
    OmegaBound.ADVXXZ.typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a =
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card := by
  classical
  unfold OmegaBound.ADVXXZ.typeCnt
  let e := Finite.equivFin {i : ι // g i = c}
  refine Finset.card_bij (fun q _ => (e.symm q).1) ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (e.symm q).2, (Finset.mem_filter.mp hq).2⟩
  · intro q₁ hq₁ q₂ hq₂ h
    apply e.symm.injective
    exact Subtype.ext h
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    let q := e ⟨i, hi'.1⟩
    refine ⟨q, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change x (e.symm q).1 = a
      rw [show (e.symm q).1 = i by simp only [q, e.symm_apply_apply]]
      exact hi'.2
    · simp only [q, e.symm_apply_apply]

private noncomputable def partitionWordEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) :
    (ι → α) ≃ ((c : κ) → Fin (Nat.card {i : ι // g i = c}) → α) :=
  Equiv.piCongrFiberwise (f := g) fun c =>
    Equiv.piCongrLeft' (fun _ : {i : ι // g i = c} => α)
      (Finite.equivFin {i : ι // g i = c})

@[simp] private theorem partitionWordEquiv_apply
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (x : ι → α)
    (c : κ) (q : Fin (Nat.card {i : ι // g i = c})) :
    partitionWordEquiv g x c q =
      x ((Finite.equivFin {i : ι // g i = c}).symm q).1 := rfl

private def piTypeClassEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {X : (c : κ) → Fin (Nat.card {i : ι // g i = c}) → α //
      ∀ c a, OmegaBound.ADVXXZ.typeCnt (X c) a = k c a} ≃
      ((c : κ) → {x : Fin (Nat.card {i : ι // g i = c}) → α //
        ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k c a}) where
  toFun X c := ⟨X.1 c, X.2 c⟩
  invFun X := ⟨fun c => (X c).1, fun c => (X c).2⟩
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    funext c
    apply Subtype.ext
    rfl

private noncomputable def partitionProductEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {x : ι → α // ∀ c a,
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card = k c a} ≃
      ((c : κ) → {x : Fin (Nat.card {i : ι // g i = c}) → α //
        ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k c a}) :=
  ((partitionWordEquiv g).subtypeEquiv fun x => by
    constructor
    · intro hx c a
      change OmegaBound.ADVXXZ.typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a = k c a
      exact (partition_reindex_count g x c a).trans (hx c a)
    · intro hx c a
      have hxc := hx c a
      change OmegaBound.ADVXXZ.typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a = k c a at hxc
      exact (partition_reindex_count g x c a).symm.trans hxc).trans
        (piTypeClassEquiv g k)

/-- Restricting a word to every fibre of a finite partition gives the product of the
corresponding exact type classes. -/
theorem partitionProductCardinality_parent25 : Parent25.PartitionProductCardinality := by
  intro ι κ α _ _ _ _ _ g k
  exact (Nat.card_congr (partitionProductEquiv g k)).trans Nat.card_pi

end OmegaBound.ADVXXZGeneral
end

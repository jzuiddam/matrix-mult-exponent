import OmegaBound.ADVXXZGeneralPQParent25
import OmegaBound.ADVXXZGeneralPQPartitionProduct
import OmegaBound.ADVXXZConstituentPairing
import OmegaBound.ADVXXZGeneralCExact36Defs

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

namespace Parent25

/-- The Parent25 partition contract at one empirical-grid scale. -/
def PartitionBridge40 : Prop :=
  ∀ {w s b m : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
    ∀ r W (j : AlphaLabel p d b m r)
      (a : (Pop p d b m r).Part (side d r W)),
      compatible p d b m r W j.val a ↔
        ∀ t c σ,
          (Finset.univ.filter fun ih : Fin (parentCount p d b m r t) × Fin 2 =>
            key d r W (j.val.val ⟨t,ih⟩) = c ∧ a ⟨t,ih⟩ = σ).card =
              cellHistogram p d m r W t c σ

/-- The unrestricted Parent25 Q fibre as exact type classes at one grid scale. -/
def QTypeClassBridge40 : Prop :=
  ∀ {w s b m : ℕ} (p : ConstituentInput w s) (d : ConstituentSpec p),
    ConstituentAdmissibleAt d b → ConstituentIntegral36 d b m →
    ∀ r W (j : AlphaLabel p d b m r),
      Nonempty (QFiber p d b m r W j.val ≃
        ((t : Fin s) → (c : Cell p t) →
          {x : Fin (Nat.card (CellPos p d b m r W j.val t c)) → Chunk w //
            ∀ σ, OmegaBound.ADVXXZ.typeCnt x σ = cellHistogram p d m r W t c σ})) ∧
      ∀ t c, (∑ σ, cellHistogram p d m r W t c σ) =
        Nat.card (CellPos p d b m r W j.val t c)

end Parent25

private noncomputable def parent25IfSum {alpha : Type*} [Fintype alpha]
    (pred : alpha → Prop) (f : alpha → ℕ) : ℕ := by
  classical
  exact ∑ x, if pred x then f x else 0

private theorem parent25_ifSum_eq {alpha : Type*} [Fintype alpha]
    (pred : alpha → Prop) [DecidablePred pred] (f : alpha → ℕ) :
    parent25IfSum pred f = ∑ x, if pred x then f x else 0 := by
  classical
  unfold parent25IfSum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : pred x <;> simp [hx]

private noncomputable def parent25FixedCell {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : Shape w → Prop) (sigma : Chunk w) := by
  classical
  exact Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
    cell (j.val ⟨t, ih⟩).val ∧ a ⟨t, ih⟩ = sigma

private noncomputable def parent25FixedChildCell {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : ChildShape p t → Prop) (sigma : Chunk w) := by
  classical
  exact Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
    cell (j.val ⟨t, ih⟩) ∧ a ⟨t, ih⟩ = sigma

private noncomputable def parent25ExactShapeCell {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (v : ChildShape p t) (sigma : Chunk w) := by
  classical
  exact Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
    j.val ⟨t, ih⟩ = v ∧ a ⟨t, ih⟩ = sigma

private theorem parent25_cellCount_eq_fixed {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : Shape w → Prop) (sigma : Chunk w) :
    Parent25.cellCount p d b m r W j a t cell sigma =
      (parent25FixedCell p d r W j a t cell sigma).card := by
  classical
  unfold Parent25.cellCount parent25FixedCell
  symm
  refine Finset.card_bij
    (fun ih _ => (⟨t, ih⟩ : Parent25.Pos p d b m r)) ?_ ?_ ?_
  · intro ih hih
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, rfl, (Finset.mem_filter.mp hih).2⟩
  · intro ih₁ _ ih₂ _ h
    cases h
    rfl
  · rintro ⟨t', ih⟩ hz
    have hz' := (Finset.mem_filter.mp hz).2
    have ht : t' = t := hz'.1
    subst t'
    exact ⟨ih, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'.2⟩, rfl⟩

set_option maxHeartbeats 1000000 in
-- The dependent population carrier requires extra elaboration budget in the fibrewise rewrite.
private theorem parent25_fixed_count_eq_sum_shapes {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : ChildShape p t → Prop) (sigma : Chunk w) :
    (parent25FixedChildCell p d r W j a t cell sigma).card =
      parent25IfSum cell fun v =>
        (parent25ExactShapeCell p d r W j a t v sigma).card := by
  classical
  unfold parent25FixedChildCell parent25ExactShapeCell parent25IfSum
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 => j.val ⟨t, ih⟩)
    (s := (Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
      cell (j.val ⟨t, ih⟩) ∧ a ⟨t, ih⟩ = sigma))
    (t := (Finset.univ.filter cell : Finset (ChildShape p t)))]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : cell v
    · simp only [hv, if_true]
      apply congrArg Finset.card
      ext ih
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => ⟨h.2, h.1.2⟩
      · intro h
        refine ⟨⟨?_, h.2⟩, h.1⟩
        simpa only [h.1] using hv
    · simp only [hv, if_false]
  · intro ih hih
    have hiS := (Finset.mem_filter.mp (Finset.mem_coe.mp hih)).2.1
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩)

set_option maxHeartbeats 1000000 in
-- The same dependent carrier appears in both count presentations during elaboration.
private theorem parent25_cellCount_eq_sum_shapes {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (cell : Shape w → Prop) (sigma : Chunk w) :
    Parent25.cellCount p d b m r W j a t cell sigma =
      parent25IfSum (fun v : ChildShape p t => cell v.val) fun v =>
        (parent25ExactShapeCell p d r W j a t v sigma).card := by
  rw [parent25_cellCount_eq_fixed]
  change (parent25FixedChildCell p d r W j a t (fun v => cell v.val) sigma).card = _
  exact parent25_fixed_count_eq_sum_shapes p d r W j a t (fun v => cell v.val) sigma

private theorem parent25_coordFin_val {w : ℕ} (W : Side) (u : Shape w) :
    (Parent25.coordFin W u).val = coord W u := by
  cases W <;> rfl

private theorem parent25_key_eq_inl_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) {t : Fin s}
    (u v : ChildShape p t) :
    Parent25.key d r W u = Sum.inl v ↔ Parent25.boundary d r W u.val ∧ u = v := by
  classical
  by_cases hu : Parent25.boundary d r W u.val
  · simp [Parent25.key, hu]
  · simp [Parent25.key, hu]

private theorem parent25_key_eq_inr_iff {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) {t : Fin s}
    (u : ChildShape p t) (k : Fin (2 * w + 1)) :
    Parent25.key d r W u = Sum.inr k ↔
      ¬ Parent25.boundary d r W u.val ∧
        coord (Parent25.side d r W) u.val = k.val := by
  classical
  by_cases hu : Parent25.boundary d r W u.val
  · simp [Parent25.key, hu]
  · simp only [Parent25.key, hu, ↓reduceIte, not_false_eq_true, true_and,
      Sum.inr.injEq]
    constructor
    · intro h
      simpa only [parent25_coordFin_val] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [parent25_coordFin_val] using h

private theorem parent25_singleton_cellCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (v : ChildShape p t) (sigma : Chunk w) :
    Parent25.cellCount p d b m r W j a t (fun u => u = v.val) sigma =
      (parent25ExactShapeCell p d r W j a t v sigma).card := by
  classical
  rw [parent25_cellCount_eq_fixed]
  unfold parent25FixedCell parent25ExactShapeCell
  apply congrArg Finset.card
  ext ih
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨Subtype.ext h.1, h.2⟩
  · intro h
    exact ⟨congrArg Subtype.val h.1, h.2⟩

set_option maxHeartbeats 1000000 in
-- Unifying the reducible stage population with the fixed-parent carrier is elaboration-heavy.
private theorem parent25_key_count_eq_ifSum {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : (Parent25.Pop p d b m r).Label)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (t : Fin s) (c : Parent25.Cell p t) (sigma : Chunk w) :
    (Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
      Parent25.key d r W (j.val ⟨t, ih⟩) = c ∧ a ⟨t, ih⟩ = sigma).card =
      parent25IfSum (fun v : ChildShape p t => Parent25.key d r W v = c)
        fun v => (parent25ExactShapeCell p d r W j a t v sigma).card := by
  calc
    _ = (parent25FixedChildCell p d r W j a t
        (fun v => Parent25.key d r W v = c) sigma).card := by
      classical
      unfold parent25FixedChildCell
      apply congrArg Finset.card
      ext ih
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = _ := parent25_fixed_count_eq_sum_shapes p d r W j a t
      (fun v => Parent25.key d r W v = c) sigma

private theorem parent25_histogram_eq_ifSum {w s : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (m : ℕ)
    (r : Fin 6) (W : Fin 2) (t : Fin s) (c : Parent25.Cell p t)
    (sigma : Chunk w) :
    Parent25.cellHistogram p d m r W t c sigma =
      parent25IfSum (fun v : ChildShape p t => Parent25.key d r W v = c)
        fun v => Parent25.childCount p d m r W t v sigma := by
  classical
  unfold Parent25.cellHistogram
  exact (parent25_ifSum_eq
    (fun v : ChildShape p t => Parent25.key d r W v = c)
    (fun v => Parent25.childCount p d m r W t v sigma)).symm

private theorem parent25_ifSum_congr {alpha : Type*} [Fintype alpha]
    (P Q : alpha → Prop) (f g : alpha → ℕ)
    (hPQ : ∀ x, P x ↔ Q x) (hfg : ∀ x, P x → f x = g x) :
    parent25IfSum P f = parent25IfSum Q g := by
  classical
  unfold parent25IfSum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x
  · rw [if_pos hx, if_pos ((hPQ x).mp hx), hfg x hx]
  · rw [if_neg hx, if_neg (mt (hPQ x).mpr hx)]

private theorem parent25_ifSum_single {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (f : alpha → ℕ) (x : alpha) :
    parent25IfSum (fun y => y = x) f = f x := by
  classical
  rw [parent25_ifSum_eq, Finset.sum_ite_eq' Finset.univ x f,
    if_pos (Finset.mem_univ x)]

private theorem parent25_coord_sum_split {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2) {t : Fin s}
    (k : Fin (2 * w + 1)) (f : ChildShape p t → ℕ) :
    parent25IfSum
        (fun v => coord (Parent25.side d r W) v.val = k.val) f =
      parent25IfSum
          (fun v => Parent25.boundary d r W v.val ∧
            coord (Parent25.side d r W) v.val = k.val) f +
        parent25IfSum
          (fun v => ¬ Parent25.boundary d r W v.val ∧
            coord (Parent25.side d r W) v.val = k.val) f := by
  classical
  unfold parent25IfSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hb : Parent25.boundary d r W v.val <;>
    by_cases hk : coord (Parent25.side d r W) v.val = k.val <;>
      simp [hb, hk]

set_option maxHeartbeats 1000000 in
/-- The ordered compatibility event is exactly the partition into singleton boundary cells and
residual side-coordinate cells, with the parent index retained. -/
theorem parent25_partition_bridge40 : Parent25.PartitionBridge40 := by
  intro w s b m p d _hd _hb r W j a
  constructor
  · rintro ⟨hboundary, hcoord⟩ t c sigma
    rw [parent25_key_count_eq_ifSum, parent25_histogram_eq_ifSum]
    cases c with
    | inl v =>
        apply parent25_ifSum_congr
        · exact fun x => Iff.rfl
        · intro x hx
          have hx' := (parent25_key_eq_inl_iff d r W x v).mp hx
          rw [← parent25_singleton_cellCount p d r W j.val a t x sigma]
          exact hboundary t x hx'.1 sigma
    | inr k =>
        let actual := fun v : ChildShape p t =>
          (parent25ExactShapeCell p d r W j.val a t v sigma).card
        let target := fun v : ChildShape p t => Parent25.childCount p d m r W t v sigma
        let onCoord := fun v : ChildShape p t =>
          coord (Parent25.side d r W) v.val = k.val
        let onBoundary := fun v : ChildShape p t =>
          Parent25.boundary d r W v.val ∧ onCoord v
        let onResidual := fun v : ChildShape p t =>
          ¬ Parent25.boundary d r W v.val ∧ onCoord v
        have htotal : parent25IfSum onCoord actual = parent25IfSum onCoord target := by
          calc
            _ = Parent25.cellCount p d b m r W j.val a t
                (fun u => coord (Parent25.side d r W) u = k.val) sigma :=
              (parent25_cellCount_eq_sum_shapes p d r W j.val a t
                (fun u => coord (Parent25.side d r W) u = k.val) sigma).symm
            _ = ∑ u, if coord (Parent25.side d r W) u.val = k.val then
                Parent25.childCount p d m r W t u sigma else 0 := hcoord t k sigma
            _ = parent25IfSum onCoord target := by
              symm
              exact parent25_ifSum_eq onCoord target
        have hboundarySum :
            parent25IfSum onBoundary actual = parent25IfSum onBoundary target := by
          apply parent25_ifSum_congr
          · exact fun x => Iff.rfl
          · intro x hx
            change (parent25ExactShapeCell p d r W j.val a t x sigma).card =
              Parent25.childCount p d m r W t x sigma
            rw [← parent25_singleton_cellCount p d r W j.val a t x sigma]
            exact hboundary t x hx.1 sigma
        have hsplitActual := parent25_coord_sum_split d r W k actual
        have hsplitTarget := parent25_coord_sum_split d r W k target
        change parent25IfSum onCoord actual =
          parent25IfSum onBoundary actual + parent25IfSum onResidual actual at hsplitActual
        change parent25IfSum onCoord target =
          parent25IfSum onBoundary target + parent25IfSum onResidual target at hsplitTarget
        have hresidual :
            parent25IfSum onResidual actual = parent25IfSum onResidual target := by omega
        calc
          parent25IfSum (fun v => Parent25.key d r W v = Sum.inr k) actual =
              parent25IfSum onResidual actual :=
            parent25_ifSum_congr _ _ _ _
              (fun x => parent25_key_eq_inr_iff d r W x k) (fun _ _ => rfl)
          _ = parent25IfSum onResidual target := hresidual
          _ = parent25IfSum (fun v => Parent25.key d r W v = Sum.inr k) target :=
            (parent25_ifSum_congr _ _ _ _
              (fun x => parent25_key_eq_inr_iff d r W x k) (fun _ _ => rfl)).symm
  · intro hcells
    have hboundaryAll : ∀ t (v : ChildShape p t),
        Parent25.boundary d r W v.val → ∀ sigma,
          Parent25.cellCount p d b m r W j.val a t (fun u => u = v.val) sigma =
            Parent25.childCount p d m r W t v sigma := by
      intro t v hv sigma
      have hcell := hcells t (Sum.inl v) sigma
      rw [parent25_key_count_eq_ifSum, parent25_histogram_eq_ifSum] at hcell
      have hkeySingle :
          parent25IfSum (fun x : ChildShape p t =>
              Parent25.key d r W x = Sum.inl v)
              (fun x => (parent25ExactShapeCell p d r W j.val a t x sigma).card) =
            (parent25ExactShapeCell p d r W j.val a t v sigma).card := by
        calc
          _ = parent25IfSum (fun x : ChildShape p t => x = v)
              (fun x => (parent25ExactShapeCell p d r W j.val a t x sigma).card) :=
            parent25_ifSum_congr _ _ _ _
              (fun x => by
                rw [parent25_key_eq_inl_iff]
                constructor
                · exact fun hx => hx.2
                · intro hx
                  subst x
                  exact ⟨hv, rfl⟩)
              (fun _ _ => rfl)
          _ = _ := parent25_ifSum_single _ v
      have htargetSingle :
          parent25IfSum (fun x : ChildShape p t =>
              Parent25.key d r W x = Sum.inl v)
              (fun x => Parent25.childCount p d m r W t x sigma) =
            Parent25.childCount p d m r W t v sigma := by
        calc
          _ = parent25IfSum (fun x : ChildShape p t => x = v)
              (fun x => Parent25.childCount p d m r W t x sigma) :=
            parent25_ifSum_congr _ _ _ _
              (fun x => by
                rw [parent25_key_eq_inl_iff]
                constructor
                · exact fun hx => hx.2
                · intro hx
                  subst x
                  exact ⟨hv, rfl⟩)
              (fun _ _ => rfl)
          _ = _ := parent25_ifSum_single _ v
      rw [hkeySingle, htargetSingle] at hcell
      rw [parent25_singleton_cellCount]
      exact hcell
    refine ⟨hboundaryAll, ?_⟩
    intro t k sigma
    let actual := fun v : ChildShape p t =>
      (parent25ExactShapeCell p d r W j.val a t v sigma).card
    let target := fun v : ChildShape p t => Parent25.childCount p d m r W t v sigma
    let onCoord := fun v : ChildShape p t =>
      coord (Parent25.side d r W) v.val = k.val
    let onBoundary := fun v : ChildShape p t =>
      Parent25.boundary d r W v.val ∧ onCoord v
    let onResidual := fun v : ChildShape p t =>
      ¬ Parent25.boundary d r W v.val ∧ onCoord v
    have hboundarySum :
        parent25IfSum onBoundary actual = parent25IfSum onBoundary target := by
      apply parent25_ifSum_congr
      · exact fun x => Iff.rfl
      · intro x hx
        change (parent25ExactShapeCell p d r W j.val a t x sigma).card =
          Parent25.childCount p d m r W t x sigma
        rw [← parent25_singleton_cellCount p d r W j.val a t x sigma]
        exact hboundaryAll t x hx.1 sigma
    have hresCell := hcells t (Sum.inr k) sigma
    rw [parent25_key_count_eq_ifSum, parent25_histogram_eq_ifSum] at hresCell
    have hresidual : parent25IfSum onResidual actual = parent25IfSum onResidual target := by
      calc
        _ = parent25IfSum
            (fun x : ChildShape p t => Parent25.key d r W x = Sum.inr k) actual :=
          parent25_ifSum_congr _ _ _ _
            (fun x => (parent25_key_eq_inr_iff d r W x k).symm)
            (fun _ _ => rfl)
        _ = parent25IfSum
            (fun x : ChildShape p t => Parent25.key d r W x = Sum.inr k) target :=
          hresCell
        _ = _ := parent25_ifSum_congr _ _ _ _
          (fun x => parent25_key_eq_inr_iff d r W x k) (fun _ _ => rfl)
    have hsplitActual := parent25_coord_sum_split d r W k actual
    have hsplitTarget := parent25_coord_sum_split d r W k target
    change parent25IfSum onCoord actual =
      parent25IfSum onBoundary actual + parent25IfSum onResidual actual at hsplitActual
    change parent25IfSum onCoord target =
      parent25IfSum onBoundary target + parent25IfSum onResidual target at hsplitTarget
    rw [parent25_cellCount_eq_sum_shapes]
    calc
      parent25IfSum onCoord actual = parent25IfSum onCoord target := by omega
      _ = ∑ u, if coord (Parent25.side d r W) u.val = k.val then
          Parent25.childCount p d m r W t u sigma else 0 :=
        parent25_ifSum_eq onCoord target

private theorem parent25_floor_nat (n : ℕ) : ((n : ℚ).floor).toNat = n := by
  change ((((n : ℤ) : ℚ).floor).toNat) = n
  rw [Rat.floor_intCast]
  simp

private theorem parent25_alphaCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6)
    (t : Fin s) (v : ChildShape p t) :
    (Parent25.alphaCount p d b m r t v : ℚ) =
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob v := by
  rcases hb.alphaIntegral t r v with ⟨n, hn⟩
  have hscaled :
      ((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r * (d.alpha t r).prob v =
        ((m * n : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) *
          ((b : ℚ) * p.baseN t * (d.A t).prob r * (d.alpha t r).prob v) := by
        push_cast
        ring
      _ = (m : ℚ) * n := by rw [hn]
      _ = ((m * n : ℕ) : ℚ) := by norm_cast
  unfold Parent25.alphaCount
  rw [hscaled, parent25_floor_nat]

private theorem parent25_childCount_cast {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (W : Fin 2)
    (t : Fin s) (v : ChildShape p t) (sigma : Chunk w) :
    (Parent25.childCount p d m r W t v sigma : ℚ) =
      (m : ℚ) * d.outBase ⟨t, r, v⟩ *
        (d.betaChild (Parent25.side d r W) t r v).prob sigma := by
  simpa [Parent25.childCount, stageCounts27] using
    hb.countsExact r (Parent25.side d r W) t v sigma

private theorem parent25_sum_childCount {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (m : ℕ) (hb : ConstituentIntegral36 d b m) (r : Fin 6) (W : Fin 2)
    (t : Fin s) (v : ChildShape p t) :
    ∑ sigma : Chunk w, Parent25.childCount p d m r W t v sigma =
      m * d.outBase ⟨t, r, v⟩ := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_sum]
  simp_rw [parent25_childCount_cast p d m hb r W t v]
  rw [← Finset.mul_sum, RatDist.sum_prob]
  push_cast
  ring

private theorem parent25_childTotal_eq_alphaPair {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (t : Fin s) (v : ChildShape p t) :
    m * d.outBase ⟨t, r, v⟩ =
      Parent25.alphaCount p d b m r t v +
        Parent25.alphaCount p d b m r t (complement p t v) := by
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [parent25_alphaCount_cast p d m hb r t v,
    parent25_alphaCount_cast p d m hb r t (complement p t v), hd.out_eq t r v]
  push_cast
  ring

private noncomputable def parent25LabelShapeCell {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : AlphaLabel p d b m r) (t : Fin s) (v : ChildShape p t) := by
  classical
  exact Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
    j.val.val ⟨t, ih⟩ = v

private noncomputable def parent25LabelShapeHalf {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : AlphaLabel p d b m r) (t : Fin s) (h : Fin 2) (v : ChildShape p t) := by
  classical
  exact Finset.univ.filter fun i : Fin (Parent25.parentCount p d b m r t) =>
    j.val.val ⟨t, i, h⟩ = v

private theorem parent25_prod_fin2_filter_card {I : Type*} [Fintype I]
    (P : I × Fin 2 → Prop) :
    (by classical exact (Finset.univ.filter P).card) =
      (by classical exact (Finset.univ.filter fun i : I => P (i, 0)).card) +
        (by classical exact (Finset.univ.filter fun i : I => P (i, 1)).card) := by
  classical
  have hfiber : ∀ h : Fin 2,
      ((Finset.univ.filter P).filter fun ih => ih.2 = h).card =
        (Finset.univ.filter fun i : I => P (i, h)).card := by
    intro h
    refine Finset.card_bij (fun ih _ => ih.1) ?_ ?_ ?_
    · intro ih hih
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hih).1).2
          have hh := (Finset.mem_filter.mp hih).2
          have hi : (ih.1, h) = ih := Prod.ext rfl hh.symm
          exact hi.symm ▸ hp⟩
    · intro ih₁ hi₁ ih₂ hi₂ heq
      apply Prod.ext heq
      exact ((Finset.mem_filter.mp hi₁).2).trans ((Finset.mem_filter.mp hi₂).2).symm
    · intro i hi
      refine ⟨(i, h), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ih : I × Fin 2 => ih.2)
    (s := (Finset.univ.filter P)) (t := (Finset.univ : Finset (Fin 2)))]
  · rw [Fin.sum_univ_two]
    rw [hfiber 0, hfiber 1]
  · intro ih _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)

set_option maxHeartbeats 1000000 in
-- The label subtype is reducible to a dependent stage-population carrier at this split.
private theorem parent25_labelShape_split {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : AlphaLabel p d b m r) (t : Fin s) (v : ChildShape p t) :
    (parent25LabelShapeCell p d r j t v).card =
      (parent25LabelShapeHalf p d r j t 0 v).card +
        (parent25LabelShapeHalf p d r j t 1 v).card := by
  classical
  unfold parent25LabelShapeCell parent25LabelShapeHalf
  have hfiber : ∀ h : Fin 2,
      (((Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
          j.val.val ⟨t, ih⟩ = v).filter fun ih => ih.2 = h).card) =
        (Finset.univ.filter fun i : Fin (Parent25.parentCount p d b m r t) =>
          j.val.val ⟨t, i, h⟩ = v).card := by
    intro h
    refine Finset.card_bij (fun ih _ => ih.1) ?_ ?_ ?_
    · intro ih hih
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hih).1).2
          have hh := (Finset.mem_filter.mp hih).2
          have hi : (ih.1, h) = ih := Prod.ext rfl hh.symm
          exact hi.symm ▸ hp⟩
    · intro ih₁ hi₁ ih₂ hi₂ heq
      apply Prod.ext heq
      exact ((Finset.mem_filter.mp hi₁).2).trans ((Finset.mem_filter.mp hi₂).2).symm
    · intro i hi
      refine ⟨(i, h), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 => ih.2)
    (s := (Finset.univ.filter fun ih => j.val.val ⟨t, ih⟩ = v))
    (t := (Finset.univ : Finset (Fin 2)))]
  · rw [Fin.sum_univ_two]
    rw [hfiber 0, hfiber 1]
  · intro ih _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)

set_option maxHeartbeats 1000000 in
-- Expanding the target subtype and its dependent paired carrier needs extra elaboration budget.
private theorem parent25_labelShape_count {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : AlphaLabel p d b m r) (t : Fin s) (v : ChildShape p t) :
    (parent25LabelShapeCell p d r j t v).card =
      Parent25.alphaCount p d b m r t v +
        Parent25.alphaCount p d b m r t (complement p t v) := by
  classical
  have hsplit := parent25_labelShape_split p d r j t v
  have hzero :
      (parent25LabelShapeHalf p d r j t 0 v).card =
        Parent25.alphaCount p d b m r t v := by
    have ht := parent25_alphaLabel_target_count p d r j t v
    unfold OmegaBound.ADVXXZ.typeCnt at ht
    calc
      _ = (Finset.univ.filter fun i : Fin (Parent25.parentCount p d b m r t) =>
          j.val.val ⟨t, i, 0⟩ = v).card := by
        unfold parent25LabelShapeHalf
        apply congrArg Finset.card
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = _ := ht
  have hcomp :
      parent25LabelShapeHalf p d r j t 1 v =
        parent25LabelShapeHalf p d r j t 0 (complement p t v) := by
    unfold parent25LabelShapeHalf
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parent25_alphaLabel_complementary p d r j t i]
    constructor
    · intro h
      rw [← h, OmegaBound.ADVXXZPaper.complement_complement]
    · intro h
      rw [h, OmegaBound.ADVXXZPaper.complement_complement]
  have hone :
      (parent25LabelShapeHalf p d r j t 1 v).card =
        Parent25.alphaCount p d b m r t (complement p t v) := by
    rw [hcomp]
    have ht := parent25_alphaLabel_target_count p d r j t (complement p t v)
    unfold OmegaBound.ADVXXZ.typeCnt at ht
    calc
      _ = (Finset.univ.filter fun i : Fin (Parent25.parentCount p d b m r t) =>
          j.val.val ⟨t, i, 0⟩ = complement p t v).card := by
        unfold parent25LabelShapeHalf
        apply congrArg Finset.card
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = _ := ht
  exact hsplit.trans (congrArg₂ Nat.add hzero hone)

private theorem parent25_cellPos_card {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    (j : AlphaLabel p d b m r) (t : Fin s) (c : Parent25.Cell p t) :
    Nat.card (Parent25.CellPos p d b m r W j.val t c) =
      parent25IfSum (fun v : ChildShape p t => Parent25.key d r W v = c)
        fun v => Parent25.alphaCount p d b m r t v +
          Parent25.alphaCount p d b m r t (complement p t v) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let dummy : Parent25.Pos p d b m r → Chunk w := fun _ _ => 0
  have hshape :
      (Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
        Parent25.key d r W (j.val.val ⟨t, ih⟩) = c).card =
        parent25IfSum (fun v : ChildShape p t => Parent25.key d r W v = c)
          fun v => (parent25LabelShapeCell p d r j t v).card := by
    let pred := fun v : ChildShape p t => Parent25.key d r W v = c
    letI : Fintype (Chunk w) := inferInstance
    have h := parent25_fixed_count_eq_sum_shapes p d r W j.val dummy t pred (fun _ => 0)
    change (parent25FixedChildCell p d r W j.val dummy t pred (fun _ => 0)).card = _ at h
    have hall : parent25FixedChildCell p d r W j.val dummy t pred (fun _ => 0) =
        Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
          pred (j.val.val ⟨t, ih⟩) := by
      unfold parent25FixedChildCell dummy
      ext ih
      simp
    rw [hall] at h
    calc
      _ = parent25IfSum pred fun v =>
          (parent25ExactShapeCell p d r W j.val dummy t v (fun _ => 0)).card := h
      _ = parent25IfSum pred fun v => (parent25LabelShapeCell p d r j t v).card := by
        apply parent25_ifSum_congr
        · exact fun _ => Iff.rfl
        · intro v _
          apply congrArg Finset.card
          unfold parent25ExactShapeCell parent25LabelShapeCell dummy
          ext ih
          simp
  rw [hshape]
  apply parent25_ifSum_congr
  · exact fun _ => Iff.rfl
  · intro v _
    exact parent25_labelShape_count p d r j t v

private theorem parent25_sum_cellHistogram {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Fin 2) (j : AlphaLabel p d b m r)
    (t : Fin s) (c : Parent25.Cell p t) :
    (∑ sigma, Parent25.cellHistogram p d m r W t c sigma) =
      Nat.card (Parent25.CellPos p d b m r W j.val t c) := by
  classical
  rw [parent25_cellPos_card p d r W j t c]
  unfold Parent25.cellHistogram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : Parent25.key d r W v = c
  · simp only [hv, if_true]
    rw [parent25_sum_childCount p d m hb r W t v,
      parent25_childTotal_eq_alphaPair p d hd m hb r t v]
  · simp [hv]

private theorem parent25_coordFin_eq_of_key_eq {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p) (r : Fin 6) (W : Fin 2)
    {t : Fin s} {u v : ChildShape p t}
    (h : Parent25.key d r W v = Parent25.key d r W u) :
    Parent25.coordFin (Parent25.side d r W) v.val =
      Parent25.coordFin (Parent25.side d r W) u.val := by
  classical
  unfold Parent25.key at h
  split_ifs at h <;> simp_all

private theorem parent25_histograms_contains {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (r : Fin 6) (W : Fin 2)
    (j : AlphaLabel p d b m r)
    (a : (Parent25.Pop p d b m r).Part (Parent25.side d r W))
    (h : ∀ t c sigma,
      (Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
        Parent25.key d r W (j.val.val ⟨t, ih⟩) = c ∧ a ⟨t, ih⟩ = sigma).card =
          Parent25.cellHistogram p d m r W t c sigma) :
    Parent25.contains p d b m r W j.val a := by
  classical
  intro z
  rcases z with ⟨t, ih⟩
  let u : ChildShape p t := j.val.val ⟨t, ih⟩
  let c : Parent25.Cell p t := Parent25.key d r W u
  let sigma : Chunk w := a ⟨t, ih⟩
  have hmem : ih ∈ (Finset.univ.filter fun q :
      Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
      Parent25.key d r W (j.val.val ⟨t, q⟩) = c ∧ a ⟨t, q⟩ = sigma) := by
    simp [u, c, sigma]
  have hcard : 0 < (Finset.univ.filter fun q :
      Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
      Parent25.key d r W (j.val.val ⟨t, q⟩) = c ∧ a ⟨t, q⟩ = sigma).card :=
    Finset.card_pos.mpr ⟨ih, hmem⟩
  have hhist : 0 < Parent25.cellHistogram p d m r W t c sigma := by
    rw [← h t c sigma]
    exact hcard
  unfold Parent25.cellHistogram at hhist
  rcases (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hhist with
    ⟨v, _, hv⟩
  by_cases hkey : Parent25.key d r W v = c
  · simp only [hkey, if_true] at hv
    have hprob : (d.betaChild (Parent25.side d r W) t r v).prob sigma ≠ 0 := by
      intro hzero
      have hchild : Parent25.childCount p d m r W t v sigma = 0 := by
        unfold Parent25.childCount
        rw [hzero, mul_zero]
        exact parent25_floor_nat 0
      omega
    have hnum : (d.betaChild (Parent25.side d r W) t r v).num sigma ≠ 0 := by
      intro hzero
      apply hprob
      simp [RatDist.prob, hzero]
    have hsupp := hd.child_support (Parent25.side d r W) t r v sigma hnum
    rw [hsupp]
    rw [← parent25_coordFin_val, ← parent25_coordFin_val]
    exact congrArg Fin.val
      (parent25_coordFin_eq_of_key_eq d r W (hkey.trans (by rfl)))
  · simp [hkey] at hv

private theorem parent25_q_reindex_count
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

private noncomputable def parent25_q_partitionWordEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) :
    (ι → α) ≃ ((c : κ) → Fin (Nat.card {i : ι // g i = c}) → α) :=
  Equiv.piCongrFiberwise (f := g) fun c =>
    Equiv.piCongrLeft' (fun _ : {i : ι // g i = c} => α)
      (Finite.equivFin {i : ι // g i = c})

private def parent25_q_piTypeClassEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {X : (c : κ) → Fin (Nat.card {i : ι // g i = c}) → α //
      ∀ c a, OmegaBound.ADVXXZ.typeCnt (X c) a = k c a} ≃
      ((c : κ) → {x : Fin (Nat.card {i : ι // g i = c}) → α //
        ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k c a}) where
  toFun X c := ⟨X.1 c, X.2 c⟩
  invFun X := ⟨fun c => (X c).1, fun c => (X c).2⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by
    funext c
    apply Subtype.ext
    rfl

private noncomputable def parent25_q_partitionProductEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {x : ι → α // ∀ c a,
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card = k c a} ≃
      ((c : κ) → {x : Fin (Nat.card {i : ι // g i = c}) → α //
        ∀ a, OmegaBound.ADVXXZ.typeCnt x a = k c a}) :=
  ((parent25_q_partitionWordEquiv g).subtypeEquiv fun x => by
    constructor
    · intro hx c a
      change OmegaBound.ADVXXZ.typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a = k c a
      exact (parent25_q_reindex_count g x c a).trans (hx c a)
    · intro hx c a
      have hxc := hx c a
      change OmegaBound.ADVXXZ.typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a = k c a at hxc
      exact (parent25_q_reindex_count g x c a).symm.trans hxc).trans
        (parent25_q_piTypeClassEquiv g k)

set_option maxHeartbeats 1000000 in
private noncomputable def parent25_qFiberEquiv {w s b : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (m : ℕ) (hb : ConstituentIntegral36 d b m)
    (r : Fin 6) (W : Fin 2) (j : AlphaLabel p d b m r) :
    Parent25.QFiber p d b m r W j.val ≃
      ((t : Fin s) → (c : Parent25.Cell p t) →
        {x : Fin (Nat.card (Parent25.CellPos p d b m r W j.val t c)) → Chunk w //
          ∀ sigma, OmegaBound.ADVXXZ.typeCnt x sigma =
            Parent25.cellHistogram p d m r W t c sigma}) := by
  classical
  let E := fun t : Fin s => parent25_q_partitionProductEquiv
    (fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
      Parent25.key d r W (j.val.val ⟨t, ih⟩))
    (fun c sigma => Parent25.cellHistogram p d m r W t c sigma)
  let F : Parent25.QFiber p d b m r W j.val →
      ((t : Fin s) → (c : Parent25.Cell p t) →
        {x : Fin (Nat.card (Parent25.CellPos p d b m r W j.val t c)) → Chunk w //
          ∀ sigma, OmegaBound.ADVXXZ.typeCnt x sigma =
            Parent25.cellHistogram p d m r W t c sigma}) := fun x t =>
    E t ⟨(fun ih => x.val ⟨t, ih⟩),
      (parent25_partition_bridge40 p d hd hb r W j x.val).mp x.property.2 t⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    funext z
    rcases z with ⟨t, ih⟩
    have ht := congrFun hxy t
    have hsource := (E t).injective ht
    exact congrFun (congrArg Subtype.val hsource) ih
  · intro X
    let raw := fun t : Fin s => (E t).symm (X t)
    let a : (Parent25.Pop p d b m r).Part (Parent25.side d r W) :=
      fun z => (raw z.1).val z.2
    have hhist : ∀ t c sigma,
        (Finset.univ.filter fun ih : Fin (Parent25.parentCount p d b m r t) × Fin 2 =>
          Parent25.key d r W (j.val.val ⟨t, ih⟩) = c ∧ a ⟨t, ih⟩ = sigma).card =
            Parent25.cellHistogram p d m r W t c sigma := by
      intro t c sigma
      exact (raw t).property c sigma
    let q : Parent25.QFiber p d b m r W j.val :=
      ⟨a, parent25_histograms_contains p d hd m r W j a hhist,
        (parent25_partition_bridge40 p d hd hb r W j a).mpr hhist⟩
    refine ⟨q, ?_⟩
    funext t
    change E t ⟨(fun ih => q.val ⟨t, ih⟩), _⟩ = X t
    simpa only [q, a, raw] using (E t).apply_symm_apply (X t)

/-- The parentwise compatible Q fibre is the product of its exact boundary/residual
cell type classes, including the empty-cell normalization identity. -/
theorem constituent_Q_type_classes40 : Parent25.QTypeClassBridge40 := by
  intro w s b m p d hd hb r W j
  constructor
  · exact ⟨parent25_qFiberEquiv p d hd m hb r W j⟩
  · intro t c
    exact parent25_sum_cellHistogram p d hd m hb r W j t c


end OmegaBound.ADVXXZGeneral
end

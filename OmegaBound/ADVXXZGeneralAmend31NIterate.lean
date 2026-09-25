import OmegaBound.ADVXXZGeneralAmend31DTensor
import OmegaBound.ADVXXZGeneralAmend27N
import OmegaBound.ADVXXZGeneralCertScaleV22

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Paper clause: `P/prelim.tex:161`. -/
theorem boundary_symbol_involutive31 {q : ℕ} (x : CW90.Idx7 q) :
  boundarySymbol31 (boundarySymbol31 x) = x := by
  rcases x with (_ | i) | ⟨⟩ <;> rfl

/-- Paper clause: `P/prelim.tex:161`. -/
theorem boundary_symbol_coefficient31 {q : ℕ} (x y : CW90.Idx7 q) :
  cwZ q x y (.inl none) = (if y = boundarySymbol31 x then 1 else 0) ∧
  cwZ q x (.inl none) y = (if y = boundarySymbol31 x then 1 else 0) ∧
  cwZ q (.inl none) x y = (if y = boundarySymbol31 x then 1 else 0) := by
  rcases x with (_ | i) | ⟨⟩ <;> rcases y with (_ | j) | ⟨⟩ <;>
    simp [cwZ, boundarySymbol31, eq_comm]

/-- Paper clause: `P/constituent.tex:17–21`. -/
theorem boundary_partner_chunks31 {q w k : ℕ}
    (x : Fin k → Fin w → CW90.Idx7 q) (t : Fin k) :
  chunkSeq (boundaryWordPartner31 x) t = reflect (chunkSeq x t) := by
  funext j
  apply Fin.ext
  change (lvl7 (boundarySymbol31 (x t j))).val = 2 - (lvl7 (x t j)).val
  rcases (x t j) with (_ | i) | ⟨⟩ <;> rfl

/-- Paper clause: `P/constituent.tex:39`. -/
theorem boundary_dimension_append31 (q : ℕ) (I J : Inventory) (n : ℕ) (W : Side) :
  boundaryDimension31 q (I ++ J) n W =
    boundaryDimension31 q I n W * boundaryDimension31 q J n W := by
  simp [boundaryDimension31]

/-- Paper clause: `P/constituent.tex:39`. -/
theorem boundary_dimension_nil31 (q n : ℕ) (W : Side) :
  boundaryDimension31 q [] n W = 1 := by
  rfl

/-- Paper clause: `P/constituent.tex:33,39`. -/
theorem boundary_dimension_zero31 (q : ℕ) (I : Inventory) (W : Side) :
  boundaryDimension31 q I 0 W = 1 := by
  induction I with
  | nil => rfl
  | cons a I ih =>
    simp only [boundaryDimension31, List.map_cons, List.prod_cons] at *
    rw [ih, mul_one]
    split_ifs
    · have hk : (a.1 * (0 : ℚ)).floor.toNat = 0 := by rw [mul_zero]; rfl
      letI : IsEmpty (Fin (a.1 * (0 : ℚ)).floor.toNat) := by rw [hk]; infer_instance
      have hw : boundaryWords31 q a 0 (boundaryReadingSide31 W) = Finset.univ := by
        ext x
        have hz : Rat.floor 0 = 0 := rfl
        simp [boundaryWords31, hk, hz]
      rw [hw]
      simp [Fintype.card_fun, hk]
    · rfl

/-- Paper clauses:
`P/prelim.tex:181–185` and `P/constituent.tex:36`. -/
theorem boundary_dimension_inactive31 (q : ℕ) (a : ℚ × AtomKey) (n : ℕ)
    (W : Side) (h : ¬ boundaryActive31 a W) :
  boundaryDimension31 q [a] n W = 1 := by
  simp [boundaryDimension31, h]

/-- Proof support for `accumulated_boundary_admissible31`; paper clauses: `P/constituent.tex:17–22,120,145`. -/
private theorem boundary_global_admissible31 (C : Certificate) (hC : AdmissibleAt C) :
    BoundaryInventoryAdmissible (boundaryOccurrences27 (G C)) 1 := by
  classical
  intro a ha
  simp only [boundaryOccurrences27, List.mem_filter, decide_eq_true_eq] at ha
  rcases ha with ⟨ha, hzero⟩
  simp only [G, scaleInventory, globalInventory, List.mem_map] at ha
  rcases ha with ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  let ru := (Fintype.equivFin (Fin 6 × Shape C.width)).symm i
  change
    0 ≤ (C.D : ℚ)^4 * C.global.joint.prob ru ∧
    (∀ W σ, 0 ≤ (C.global.beta W ru.1 ru.2).prob σ) ∧
    (∀ W, (∑ σ, (C.global.beta W ru.1 ru.2).prob σ) = 1) ∧
    (∀ W σ, (C.global.beta W ru.1 ru.2).prob σ ≠ 0 →
      chunkLvl σ = coord W ru.2) ∧
    (∃ W, coord W ru.2 = 0) ∧
    (∀ Z X Y : Side, X ≠ Y → X ≠ Z → Y ≠ Z → coord Z ru.2 = 0 →
      ∀ σ, (C.global.beta X ru.1 ru.2).prob σ =
        (C.global.beta Y ru.1 ru.2).prob (reflect σ)) ∧
    (∃ k : ℕ, (1 : ℚ) * ((C.D : ℚ)^4 * C.global.joint.prob ru) = k) ∧
    ∀ W σ, ∃ k : ℕ,
      (1 : ℚ) * ((C.D : ℚ)^4 * C.global.joint.prob ru) *
        (C.global.beta W ru.1 ru.2).prob σ = k
  refine ⟨mul_nonneg (by positivity) (C.global.joint.prob_nonneg ru),
    fun W σ => (C.global.beta W ru.1 ru.2).prob_nonneg σ,
    fun W => (C.global.beta W ru.1 ru.2).sum_prob,
    (fun W σ hprob => hC.global_ok.support W ru.1 ru.2 σ (by
      intro hnum
      apply hprob
      simp [RatDist.prob, hnum])), ?_,
    hC.global_ok.boundary ru.1 ru.2, ?_, ?_⟩
  · simp only [ru] at hzero ⊢
    rcases hzero with hx | hy | hz
    · exact ⟨.X, hx⟩
    · exact ⟨.Y, hy⟩
    · exact ⟨.Z, hz⟩
  · simpa only [one_mul] using ((hC.lattice.1.2 ru.1).2 ru.2).1
  · intro W σ
    simpa only [one_mul] using ((hC.lattice.1.2 ru.1).2 ru.2).2 W σ

/-- Proof support for `accumulated_boundary_admissible31`; paper clauses: `P/constituent.tex:17–22,120,145`. -/
private theorem boundary_child_admissible31 (C : Certificate) (hC : AdmissibleAt C)
    (l : Stage C.top) :
    BoundaryInventoryAdmissible (boundaryOccurrences27 (QAt C l)) 1 := by
  classical
  unfold QAt
  cases hs : C.stage l with
  | none => simp [boundaryOccurrences27, BoundaryInventoryAdmissible]
  | some d =>
    have hd := hC.stage_ok l d hs
    have hlat := hC.lattice.2 l d hs
    intro a ha
    simp only [boundaryOccurrences27, List.mem_filter, decide_eq_true_eq] at ha
    rcases ha with ⟨ha, hzero⟩
    simp only [childInventory, List.mem_map] at ha
    rcases ha with ⟨i, hi, rfl⟩
    let x := (Fintype.equivFin (ConstituentTerm d.input)).symm i
    change
      0 ≤ (d.data.outBase x : ℚ) ∧
      (∀ W σ, 0 ≤ (d.data.betaChild W x.1 x.2.1 x.2.2).prob σ) ∧
      (∀ W, (∑ σ, (d.data.betaChild W x.1 x.2.1 x.2.2).prob σ) = 1) ∧
      (∀ W σ, (d.data.betaChild W x.1 x.2.1 x.2.2).prob σ ≠ 0 →
        chunkLvl σ = coord W x.2.2.1) ∧
      (∃ W, coord W x.2.2.1 = 0) ∧
      (∀ Z X Y : Side, X ≠ Y → X ≠ Z → Y ≠ Z → coord Z x.2.2.1 = 0 →
        ∀ σ, (d.data.betaChild X x.1 x.2.1 x.2.2).prob σ =
          (d.data.betaChild Y x.1 x.2.1 x.2.2).prob (reflect σ)) ∧
      (∃ k : ℕ, (1 : ℚ) * (d.data.outBase x : ℚ) = k) ∧
      ∀ W σ, ∃ k : ℕ, (1 : ℚ) * (d.data.outBase x : ℚ) *
        (d.data.betaChild W x.1 x.2.1 x.2.2).prob σ = k
    refine ⟨by positivity,
      fun W σ => (d.data.betaChild W x.1 x.2.1 x.2.2).prob_nonneg σ,
      fun W => (d.data.betaChild W x.1 x.2.1 x.2.2).sum_prob,
      (fun W σ hprob => hd.child_support W x.1 x.2.1 x.2.2 σ (by
        intro hnum
        apply hprob
        simp [RatDist.prob, hnum])), ?_, hd.child_boundary x.1 x.2.1 x.2.2, ?_, ?_⟩
    · simp only [x] at hzero ⊢
      rcases hzero with hx | hy | hz
      · exact ⟨.X, hx⟩
      · exact ⟨.Y, hy⟩
      · exact ⟨.Z, hz⟩
    · exact ⟨d.data.outBase x, by simp⟩
    · intro W σ
      simpa only [one_mul] using ((hlat.2 x.1 x.2.1).2 x.2.2).2.2 W σ

/-- Proof support for `accumulated_boundary_admissible31`; paper clause: `P/constituent.tex:39`. -/
private theorem boundary_admissible_append31 (I J : Inventory) (b : ℕ)
    (hI : BoundaryInventoryAdmissible I b)
    (hJ : BoundaryInventoryAdmissible J b) :
    BoundaryInventoryAdmissible (I ++ J) b := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hI a ha
  · exact hJ a ha

/-- Proof support for `accumulated_boundary_admissible31`; paper clause: `P/constituent.tex:39`. -/
private theorem boundary_admissible_flatMap31 {α : Type*} (L : List α)
    (f : α → Inventory) (b : ℕ)
    (hf : ∀ x ∈ L, BoundaryInventoryAdmissible (f x) b) :
    BoundaryInventoryAdmissible (L.flatMap f) b := by
  intro a ha
  simp only [List.mem_flatMap] at ha
  rcases ha with ⟨x, hx, ha⟩
  exact hf x hx a ha

/-- Paper clauses:
`P/constituent.tex:17–22,120,145` and `P/numerical.tex:17–22`. -/
theorem accumulated_boundary_admissible31 (C : Certificate) (hC : AdmissibleAt C) :
  BoundaryInventoryAdmissible (accumulatedBoundary27 C) 1 := by
  rw [accumulatedBoundary27]
  apply boundary_admissible_append31
  · exact boundary_global_admissible31 C hC
  · apply boundary_admissible_flatMap31
    intro l hl
    split_ifs with h
    · exact boundary_child_admissible31 C hC ⟨l.val, h⟩
    · simp [BoundaryInventoryAdmissible]

/-- Proof support for `accumulated_boundary_rate31`; paper clause: `P/numerical.tex:17–22,27`. -/
private theorem boundaryRate_boundaryOccurrences31
    (q : ℕ) (I : Inventory) (W : Side) :
    boundaryRate q (boundaryOccurrences27 I) W = boundaryRate q I W := by
  induction I with
  | nil => rfl
  | cons a I ih =>
      simp only [boundaryRate, boundaryOccurrences27] at ih
      simp only [boundaryOccurrences27, List.filter_cons]
      split_ifs with ha
      · simp only [boundaryRate, List.map_cons, List.sum_cons]
        exact congrArg _ ih
      · simp only [boundaryRate, List.map_cons, List.sum_cons]
        rcases W with _ | _ | _ <;>
          simp only [boundaryActive31] at ha ⊢ <;>
          split_ifs with hactive
        all_goals simp_all [decide_eq_true_eq]

/-- Proof support for `accumulated_boundary_rate31`; paper clause: `P/constituent.tex:39`. -/
private theorem boundaryRate_append31
    (q : ℕ) (I J : Inventory) (W : Side) :
    boundaryRate q (I ++ J) W = boundaryRate q I W + boundaryRate q J W := by
  simp [boundaryRate]

/-- Proof support for `accumulated_boundary_rate31`; paper clause: `P/constituent.tex:39`. -/
private theorem boundaryRate_flatMap31 {α : Type*}
    (q : ℕ) (L : List α) (f : α → Inventory) (W : Side) :
    boundaryRate q (L.flatMap f) W = (L.map fun x => boundaryRate q (f x) W).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [boundaryRate_append31, ih]

/-- Proof support for the stage order in `accumulated_boundary_rate31`; paper clause: `P/numerical.tex:17–22`. -/
private def stageFinEquiv31 (top : ℕ) :
    {i : Fin (top + 1) // 2 ≤ i.val} ≃ Stage top where
  toFun i := ⟨i.1.val, i.2, Nat.le_of_lt_succ i.1.isLt⟩
  invFun l := ⟨⟨l.val, Nat.lt_succ_of_le l.2.2⟩, l.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Proof support for the stage order in `accumulated_boundary_rate31`; paper clause: `P/numerical.tex:17–22`. -/
private theorem stage_sum_finRange31 {M : Type*} [AddCommMonoid M]
    (top : ℕ) (f : Stage top → M) :
    ((List.finRange (top + 1)).map fun i =>
      if h : 2 ≤ i.val ∧ i.val ≤ top then f ⟨i.val, h⟩ else 0).sum =
      ∑ l : Stage top, f l := by
  classical
  let e := stageFinEquiv31 top
  calc
    ((List.finRange (top + 1)).map fun i =>
        if h : 2 ≤ i.val ∧ i.val ≤ top then f ⟨i.val, h⟩ else 0).sum =
        ((List.finRange (top + 1)).map fun i =>
          if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro i _hi
            have hi : i.val ≤ top := Nat.le_of_lt_succ i.isLt
            split_ifs <;> simp_all [e, stageFinEquiv31]
    _ = ∑ i : Fin (top + 1), if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0 := by
      rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    _ = ∑ i : {i : Fin (top + 1) // 2 ≤ i.val}, f (e i) := by
      let p := fun i : Fin (top + 1) => 2 ≤ i.val
      let g := fun i : Fin (top + 1) => if h : p i then f (e ⟨i, h⟩) else 0
      letI : Fintype {i : Fin (top + 1) // p i} := Fintype.ofFinite _
      have hfilter : (∑ i : Fin (top + 1), g i) =
          (∑ i ∈ Finset.univ.filter p, g i) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hnot
        have hn : ¬ p i := by
          intro hp
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩)
        simp [g, hn]
      rw [show (∑ i : Fin (top + 1),
          if h : 2 ≤ i.val then f (e ⟨i, h⟩) else 0) =
          ∑ i : Fin (top + 1), g i by rfl, hfilter]
      rw [Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp [p]) g]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [g]
      rw [dif_pos i.property]
    _ = ∑ l : Stage top, f l := Equiv.sum_comp e f

/-- Paper clause:
`P/numerical.tex:17–22,27`. -/
theorem accumulated_boundary_rate31 (C : Certificate) (W : Side) :
  boundaryRate C.q (accumulatedBoundary27 C) W / (C.D : ℝ)^4 =
    derivedMatrixRateAt C W := by
  classical
  rw [show boundaryRate C.q (accumulatedBoundary27 C) W =
      boundaryRate C.q (boundaryOccurrences27 (G C)) W +
        boundaryRate C.q
          (((List.finRange (C.top + 1)).reverse).flatMap fun l =>
            if h : 2 ≤ l.val ∧ l.val ≤ C.top then
              boundaryOccurrences27 (QAt C ⟨l.val, h⟩) else []) W by
    simp only [accumulatedBoundary27, boundaryRate_append31]]
  rw [boundaryRate_boundaryOccurrences31, boundaryRate_flatMap31,
    List.map_reverse, List.sum_reverse]
  have hbranch : ∀ l : Fin (C.top + 1),
      boundaryRate C.q
          (if h : 2 ≤ l.val ∧ l.val ≤ C.top then
            boundaryOccurrences27 (QAt C ⟨l.val, h⟩) else []) W =
        if h : 2 ≤ l.val ∧ l.val ≤ C.top then
          boundaryRate C.q (boundaryOccurrences27 (QAt C ⟨l.val, h⟩)) W else 0 := by
    intro l
    split_ifs <;> rfl
  simp_rw [hbranch, boundaryRate_boundaryOccurrences31]
  have hs :
      ((List.finRange (C.top + 1)).map fun l =>
        if h : 2 ≤ l.val ∧ l.val ≤ C.top then
          boundaryRate C.q (QAt C ⟨l.val, h⟩) W else 0).sum =
        ∑ l : Stage C.top, boundaryRate C.q (QAt C l) W :=
    stage_sum_finRange31 C.top (fun l => boundaryRate C.q (QAt C l) W)
  rw [hs]
  rfl

/-- Paper clauses:
`P/prelim.tex:185` and `P/numerical.tex:21`. -/
theorem level_one_boundary31 (u : Shape 1) :
  coord .X u = 0 ∨ coord .Y u = 0 ∨ coord .Z u = 0 := by
  rcases u with ⟨⟨i,j,k⟩, hs⟩
  change (i : ℕ) = 0 ∨ (j : ℕ) = 0 ∨ (k : ℕ) = 0
  dsimp at hs
  omega
end
end OmegaBound.ADVXXZGeneral
end

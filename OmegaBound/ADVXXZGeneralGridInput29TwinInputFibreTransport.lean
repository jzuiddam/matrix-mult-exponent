import OmegaBound.ADVXXZGeneralInputSelfBound
import OmegaBound.ADVXXZGeneralGridInput29TwinRepairFibresCardinality
import OmegaBound.ADVXXZGeneralGridInput29TwinRepairFibresApplication

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral.Grid29
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem inputFibre_reindex_count
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (x : ι → α)
    (c : κ) (a : α) :
    typeCnt
        (fun q : Fin (Nat.card {i : ι // g i = c}) =>
          x ((Finite.equivFin {i : ι // g i = c}).symm q).1) a =
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card := by
  classical
  unfold typeCnt
  let e := Finite.equivFin {i : ι // g i = c}
  refine Finset.card_bij (fun q _ => (e.symm q).1) ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (e.symm q).2, (Finset.mem_filter.mp hq).2⟩
  · intro q₁ _ q₂ _ h
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

private noncomputable def inputFibre_wordEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) :
    (ι → α) ≃ ((c : κ) → Fin (Nat.card {i : ι // g i = c}) → α) :=
  Equiv.piCongrFiberwise (f := g) fun c =>
    Equiv.piCongrLeft' (fun _ : {i : ι // g i = c} => α)
      (Finite.equivFin {i : ι // g i = c})

private def inputFibre_piTypeClassEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {X : (c : κ) → Fin (Nat.card {i : ι // g i = c}) → α //
      ∀ c a, typeCnt (X c) a = k c a} ≃
      ((c : κ) → Words (Nat.card {i : ι // g i = c}) (k c)) where
  toFun X c := ⟨X.1 c, X.2 c⟩
  invFun X := ⟨fun c => (X c).1, fun c => (X c).2⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by
    funext c
    apply Subtype.ext
    rfl

/-- Restricting a word to the color fibres is an event-preserving equivalence, not
merely a cardinality identity.  The value at a fibre coordinate is definitionally the
value at the corresponding original position. -/
noncomputable def inputFibreProductEquiv
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ) :
    {x : ι → α // ∀ c a,
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card = k c a} ≃
      ((c : κ) → Words (Nat.card {i : ι // g i = c}) (k c)) :=
  ((inputFibre_wordEquiv g).subtypeEquiv fun x => by
    constructor
    · intro hx c a
      exact (inputFibre_reindex_count g x c a).trans (hx c a)
    · intro hx c a
      exact (inputFibre_reindex_count g x c a).symm.trans (hx c a)).trans
        (inputFibre_piTypeClassEquiv g k)

@[simp] theorem inputFibreProductEquiv_apply
    {ι κ α : Type} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq κ] [DecidableEq α] (g : ι → κ) (k : κ → α → ℕ)
    (x : {x : ι → α // ∀ c a,
      (Finset.univ.filter fun i => g i = c ∧ x i = a).card = k c a})
    (c : κ) (q : Fin (Nat.card {i : ι // g i = c})) :
    (inputFibreProductEquiv g k x c).val q =
      x.val ((Finite.equivFin {i : ι // g i = c}).symm q).1 := rfl

private abbrev InputStageCell {w s : ℕ} (p : ConstituentInput w s) :=
  (t : Fin s) × ChildShape p t

abbrev InputStageCellPos {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :=
  {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
    stageColour27 0 b m p d r j t i = u}

private def InputStageHistogramPart {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side) : Type :=
  {a : (stagePopulationAt 0 p d b m r).Part W //
    ∀ t u sigma,
      histogram27
        (fun i => (stageColour27 0 b m p d r j t i, a ⟨t,i⟩))
        (u, sigma) = stageCounts27 m p d r W t u sigma}

private def InputStageParentHistogram {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (t : Fin s) : Type :=
  {x : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 → Chunk w //
    ∀ u sigma,
      (Finset.univ.filter fun i =>
        stageColour27 0 b m p d r j t i = u ∧ x i = sigma).card =
          stageCounts27 m p d r W t u sigma}

private theorem inputStageExact_iff_histogram {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : (stagePopulationAt 0 p d b m r).Part W) :
    a ∈ exactPartsAt 0 b m p d r j W ↔
      ∀ t u sigma,
        histogram27
          (fun i => (stageColour27 0 b m p d r j t i, a ⟨t,i⟩))
          (u, sigma) = stageCounts27 m p d r W t u sigma := by
  rw [stageExact_iff_partition27 0 b m p d r j W]
  constructor
  · exact fun h => h.2
  · intro hcount
    refine ⟨?_, hcount⟩
    intro t i
    let u := stageColour27 0 b m p d r j t i
    let sigma := a ⟨t,i⟩
    have hhist : 0 < histogram27
        (fun z => (stageColour27 0 b m p d r j t z, a ⟨t,z⟩))
        (u, sigma) := by
      unfold histogram27
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hpositive : 0 < stageCounts27 m p d r W t u sigma := by
      rw [← hcount]
      exact hhist
    apply hd.child_support W t r u sigma
    intro hzero
    have hcountZero : stageCounts27 m p d r W t u sigma = 0 := by
      unfold stageCounts27
      rw [show (d.betaChild W t r u).prob sigma = 0 by
        simp [RatDist.prob, hzero]]
      simp only [mul_zero]
      change ((((0 : ℤ) : ℚ).floor).toNat) = 0
      rw [Rat.floor_intCast]
      exact Int.toNat_zero
    omega

private noncomputable def inputStageExactHistogramEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side) :
    StageExactPart27 0 b m p d r j W ≃
      InputStageHistogramPart p d r j W :=
  Equiv.subtypeEquiv (Equiv.refl _)
    (inputStageExact_iff_histogram p d hd r j W)

set_option maxHeartbeats 2000000 in
-- The dependent subtype splitting requires additional reduction.
private noncomputable def inputStageSplitEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side) :
    InputStageHistogramPart p d r j W ≃
      ((t : Fin s) → InputStageParentHistogram p d r j W t) where
  toFun a t := ⟨fun i => a.val ⟨t,i⟩, fun u sigma => by
    simpa only [histogram27, Prod.mk.injEq] using a.property t u sigma⟩
  invFun a := ⟨fun z => (a z.1).val z.2, fun t u sigma => by
    simpa only [histogram27, Prod.mk.injEq] using (a t).property u sigma⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by funext t; apply Subtype.ext; rfl

set_option maxHeartbeats 1000000 in
-- The iterated parent product requires additional reduction.
private noncomputable def inputStageParentsProductEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side) :
    ((t : Fin s) → InputStageParentHistogram p d r j W t) ≃
      ((t : Fin s) → (u : ChildShape p t) →
        Words (Nat.card (InputStageCellPos p d r j t u))
          (stageCounts27 m p d r W t u)) :=
  Equiv.piCongrRight fun t => by
    change
      {x : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 → Chunk w //
        ∀ u sigma,
          (Finset.univ.filter fun i =>
            stageColour27 0 b m p d r j t i = u ∧ x i = sigma).card =
              stageCounts27 m p d r W t u sigma} ≃ _
    exact inputFibreProductEquiv
      (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
        stageColour27 0 b m p d r j t i)
      (stageCounts27 m p d r W t)

set_option maxHeartbeats 1000000 in
-- The composed stage equivalence requires additional reduction.
/-- An exact physical part is uniformly the finite product of the actual child-cell
type-class words.  The equivalence uses the choice-generated `Finite.equivFin` only to
number positions inside a fixed physical cell; it does not replace the physical pairing. -/
noncomputable def inputExactPartFibreEquiv {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side) :
    StageExactPart27 0 b m p d r j W ≃
      ((t : Fin s) → (u : ChildShape p t) →
        Words (Nat.card (InputStageCellPos p d r j t u))
          (stageCounts27 m p d r W t u)) :=
  (inputStageExactHistogramEquiv p d hd r j W).trans
    ((inputStageSplitEquiv p d r j W).trans
      (inputStageParentsProductEquiv p d r j W))

@[simp] theorem inputExactPartFibreEquiv_apply {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t)
    (q : Fin (Nat.card (InputStageCellPos p d r j t u))) :
    (inputExactPartFibreEquiv p d hd r j W a t u).val q =
      a.val ⟨t, ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q).val⟩ := by
  unfold inputExactPartFibreEquiv inputStageParentsProductEquiv
    inputStageSplitEquiv inputStageExactHistogramEquiv inputFibreProductEquiv
    inputFibre_piTypeClassEquiv inputFibre_wordEquiv
  rfl

end
end OmegaBound.ADVXXZGeneral.Grid29
end

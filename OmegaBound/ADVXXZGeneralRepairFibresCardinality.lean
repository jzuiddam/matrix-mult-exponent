import OmegaBound.ADVXXZGeneralRepairFibresApplication
import OmegaBound.ADVXXZConstituentPairing

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Split a predicate fibre on `I × Fin 2` into its two literal half fibres. -/
def twoHalfFibreEquiv27 {I : Type} (P : I × Fin 2 → Prop) :
    {x : I × Fin 2 // P x} ≃
      {i : I // P (i, 0)} ⊕ {i : I // P (i, 1)} where
  toFun x := if h : x.val.2 = 0 then
    Sum.inl ⟨x.val.1, by
      have hx : x.val = (x.val.1, 0) := Prod.ext rfl h
      exact hx ▸ x.property⟩
  else
    Sum.inr ⟨x.val.1, by
      have h1 : x.val.2 = 1 := Fin.eq_one_of_ne_zero x.val.2 h
      have hx : x.val = (x.val.1, 1) := Prod.ext rfl h1
      exact hx ▸ x.property⟩
  invFun x := x.elim
    (fun i => ⟨(i.val, 0), i.property⟩)
    (fun i => ⟨(i.val, 1), i.property⟩)
  left_inv x := by
    rcases x with ⟨⟨i, h⟩, hx⟩
    apply Subtype.ext
    fin_cases h <;> rfl
  right_inv x := by
    rcases x with x | x <;> rfl

private noncomputable def stageWholeFibreFintype27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    Fintype {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} :=
  Fintype.ofFinite _

private noncomputable def stageWholeFibreDecidableEq27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    DecidableEq {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
      stageColour27 q b m p d r j t i = u} :=
  Classical.decEq _

private noncomputable def stageHalfFibreFintype27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (h : Fin 2) :
    Fintype {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, h) = u} :=
  Fintype.ofFinite _

private noncomputable def stageHalfFibreDecidableEq27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (h : Fin 2) :
    DecidableEq {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, h) = u} :=
  Classical.decEq _

set_option maxHeartbeats 1000000 in
-- Target membership unfolds the dependent raw-population label only at this boundary.
private theorem stageTargetHalfZeroCard27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 0) = u}
      (stageHalfFibreFintype27 q m p d r j t u 0) =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r * (d.alpha t r).prob u).floor.toNat := by
  letI := stageHalfFibreFintype27 q m p d r j t u 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 0
  rw [Fintype.card_subtype]
  have h := (Finset.mem_filter.mp hj).2 t u
  simpa only [stageColour27] using h

set_option maxHeartbeats 1000000 in
-- The label complementarity projection has the same dependent stage-label envelope.
private def stageHalfOneComplementEquiv27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 1) = u} ≃
    {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
      stageColour27 q b m p d r j t (i, 0) = complement p t u} where
  toFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 0)⟩ = complement p t u
    calc
      j.val ⟨t, (i.val, 0)⟩ =
          complement p t (complement p t (j.val ⟨t, (i.val, 0)⟩)) :=
        (OmegaBound.ADVXXZPaper.complement_complement t _).symm
      _ = complement p t (j.val ⟨t, (i.val, 1)⟩) :=
        (congrArg (complement p t) hc).symm
      _ = complement p t u := congrArg (complement p t) i.property⟩
  invFun i := ⟨i.val, by
    have hc := j.property.2 t i.val
    change j.val ⟨t, (i.val, 1)⟩ = u
    calc
      j.val ⟨t, (i.val, 1)⟩ = complement p t (j.val ⟨t, (i.val, 0)⟩) := hc
      _ = complement p t (complement p t u) :=
        congrArg (complement p t) i.property
      _ = u := OmegaBound.ADVXXZPaper.complement_complement t u⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

set_option maxHeartbeats 1000000 in
-- Applying the half-zero result at the complementary child retains that envelope.
private theorem stageTargetHalfOneCard27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 1) = u}
      (stageHalfFibreFintype27 q m p d r j t u 1) =
      (((b * m * p.baseN t : ℕ) : ℚ) *
        (d.A t).prob r *
          (d.alpha t r).prob (complement p t u)).floor.toNat := by
  letI := stageHalfFibreFintype27 q m p d r j t u 1
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 1
  letI := stageHalfFibreFintype27 q m p d r j t (complement p t u) 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t (complement p t u) 0
  calc
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
        stageColour27 q b m p d r j t (i, 1) = u} =
        Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
          stageColour27 q b m p d r j t (i, 0) = complement p t u} :=
      Fintype.card_congr (stageHalfOneComplementEquiv27 q m p d r j t u)
    _ = _ := stageTargetHalfZeroCard27 q m p d r j hj t (complement p t u)

set_option maxHeartbeats 1000000 in
-- The result type contains the target label and its explicitly fixed fibre instances.
/-- A target label uses exactly `m * outBase` positions of each child colour across both halves. -/
theorem stageTargetFibre_card27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target)
    (t : Fin s) (u : ChildShape p t) :
    @Fintype.card
      {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
        stageColour27 q b m p d r j t i = u}
      (stageWholeFibreFintype27 q m p d r j t u) =
      m * d.outBase ⟨t, r, u⟩ := by
  letI := stageWholeFibreFintype27 q m p d r j t u
  letI := stageWholeFibreDecidableEq27 q m p d r j t u
  letI := stageHalfFibreFintype27 q m p d r j t u 0
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 0
  letI := stageHalfFibreFintype27 q m p d r j t u 1
  letI := stageHalfFibreDecidableEq27 q m p d r j t u 1
  calc
    Fintype.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
        stageColour27 q b m p d r j t i = u} =
        Fintype.card
          ({i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 0) = u} ⊕
            {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
              stageColour27 q b m p d r j t (i, 1) = u}) :=
      Fintype.card_congr (twoHalfFibreEquiv27
        (fun i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 =>
          stageColour27 q b m p d r j t i = u))
    _ = Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 0) = u} +
        Fintype.card
          {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) //
            stageColour27 q b m p d r j t (i, 1) = u} := Fintype.card_sum
    _ = (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob u).floor.toNat +
        (((b * m * p.baseN t : ℕ) : ℚ) * (d.A t).prob r *
          (d.alpha t r).prob (complement p t u)).floor.toNat :=
      congrArg₂ (fun x y : ℕ => x + y)
        (stageTargetHalfZeroCard27 q m p d r j hj t u)
        (stageTargetHalfOneCard27 q m p d r j hj t u)
    _ = m * d.outBase ⟨t, r, u⟩ := stageAlphaPair27 p d hd hb m r t u

set_option maxHeartbeats 1000000 in
-- The exact-part equivalence repeats the dependent stage label in every partition parameter.
/-- Every target label has a realized exact part alphabet on each physical side. -/
theorem stageExactPart_nonempty27 {w s b : ℕ} (q m : ℕ)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b)
    (r : Fin 6) (j : (stagePopulationAt q p d b m r).Label)
    (hj : j ∈ (stagePopulationAt q p d b m r).target) (W : Side) :
    Nonempty (StageExactPart27 q b m p d r j W) := by
  letI stagePositionFintype27 :
      ∀ t : Fin s,
        Fintype (Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :=
    fun _ => inferInstance
  letI stagePositionDecidableEq27 :
      ∀ t : Fin s,
        DecidableEq (Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2) :=
    fun _ => inferInstance
  letI childShapeFintype27 : ∀ t : Fin s, Fintype (ChildShape p t) :=
    fun _ => inferInstance
  letI childShapeDecidableEq27 : ∀ t : Fin s, DecidableEq (ChildShape p t) :=
    fun _ => inferInstance
  have hsum : ∀ t u,
      ∑ σ, stageCounts27 m p d r W t u σ =
        Nat.card {i : Fin (StageCandidateRaw.stageParentCount b m p d r t) × Fin 2 //
          stageColour27 q b m p d r j t i = u} := by
    intro t u
    rw [stageCounts27_sum p d hb m r W t u]
    letI := stageWholeFibreFintype27 q m p d r j t u
    letI := stageWholeFibreDecidableEq27 q m p d r j t u
    rw [Nat.card_eq_fintype_card]
    exact (stageTargetFibre_card27 q m p d hd hb r j hj t u).symm
  have hlevel : ∀ t u σ, 0 < stageCounts27 m p d r W t u σ →
      chunkLvl σ = coord W u.val := by
    intro t u σ hpos
    apply hd.child_support W t r u σ
    intro hzero
    have hcount : stageCounts27 m p d r W t u σ = 0 := by
      unfold stageCounts27
      rw [show (d.betaChild W t r u).prob σ = 0 by
        simp [RatDist.prob, hzero]]
      simp only [mul_zero]
      change ((((0 : ℤ) : ℚ).floor).toNat) = 0
      rw [Rat.floor_intCast]
      exact Int.toNat_zero
    omega
  obtain ⟨a⟩ := partitionExact_nonempty27
    (stageColour27 q b m p d r j) (fun _ u => u.val)
    (stageCounts27 m p d r) W hsum hlevel
  exact ⟨(stagePartEquiv27 q b m p d r j W).symm a⟩

end
end OmegaBound.ADVXXZGeneral
end

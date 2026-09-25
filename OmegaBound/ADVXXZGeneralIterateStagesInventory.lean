import OmegaBound.ADVXXZGeneralIterateStagesRates
import OmegaBound.ADVXXZGeneralIterateInfraTerminal

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- All masses in the global inventory are nonnegative. -/
theorem globalInventory_nonnegative_for_iterate (C : Certificate) :
    ∀ a ∈ G C, 0 ≤ a.1 := by
  classical
  intro a ha
  simp only [G, scaleInventory, globalInventory, List.mem_map] at ha
  rcases ha with ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  exact mul_nonneg (by positivity) (C.global.joint.prob_nonneg _)

/-- All masses in a child inventory are nonnegative. -/
theorem childInventory_nonnegative_for_iterate (C : Certificate) (l : Stage C.top) :
    ∀ a ∈ QAt C l, 0 ≤ a.1 := by
  classical
  intro a ha
  cases hs : C.stage l with
  | none => simp [QAt, hs] at ha
  | some d =>
    rw [QAt, hs] at ha
    simp only [childInventory, List.mem_map] at ha
    rcases ha with ⟨i, hi, rfl⟩
    change 0 ≤ (d.data.outBase ((Fintype.equivFin (ConstituentTerm d.input)).symm i) : ℚ)
    positivity

/-- Parent masses, after the certificate's `D²` scaling, are integral at every outer multiplier. -/
theorem parentInventory_integral_for_iterate (C : Certificate) (l : Stage C.top) (m : ℕ) :
    ∀ a ∈ P C l, ∃ k : ℕ, a.1 * (m : ℚ) = k := by
  classical
  intro a ha
  cases hs : C.stage l with
  | none => simp [P, hs] at ha
  | some d =>
    rw [P, hs] at ha
    simp only [scaleInventory, parentInventory, List.mem_map] at ha
    rcases ha with ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨C.D ^ 2 * d.input.baseN i * m, ?_⟩
    norm_num

/-- Child masses are natural numbers and hence integral at every outer multiplier. -/
theorem childInventory_integral_for_iterate (C : Certificate) (l : Stage C.top) (m : ℕ) :
    ∀ a ∈ QAt C l, ∃ k : ℕ, a.1 * (m : ℚ) = k := by
  classical
  intro a ha
  cases hs : C.stage l with
  | none => simp [QAt, hs] at ha
  | some d =>
    rw [QAt, hs] at ha
    simp only [childInventory, List.mem_map] at ha
    rcases ha with ⟨i, hi, rfl⟩
    refine ⟨d.data.outBase
      ((Fintype.equivFin (ConstituentTerm d.input)).symm i) * m, ?_⟩
    norm_num

/-- The global lattice hypothesis remains integral after multiplying by an arbitrary stage size. -/
theorem globalInventory_integral_for_iterate (C : Certificate) (hC : AdmissibleAt C)
    (m : ℕ) : ∀ a ∈ G C, ∃ k : ℕ, a.1 * (m : ℚ) = k := by
  classical
  intro a ha
  simp only [G, scaleInventory, globalInventory, List.mem_map] at ha
  rcases ha with ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  let ru := (Fintype.equivFin (Fin 6 × Shape C.width)).symm i
  obtain ⟨k, hk⟩ := ((hC.lattice.1.2 ru.1).2 ru.2).1
  have hk' : (C.D : ℚ) ^ 4 * C.global.joint.prob ru = k := by
    simpa only [Nat.cast_pow] using hk
  refine ⟨k * m, ?_⟩
  change ((C.D : ℚ) ^ 4 * C.global.joint.prob ru) * (m : ℚ) = _
  rw [hk']
  norm_num

/-- Filtering to the interior preserves the global mass-integrality fact. -/
theorem globalInterior_integral_for_iterate (C : Certificate) (hC : AdmissibleAt C)
    (m : ℕ) : ∀ a ∈ interior (G C), ∃ k : ℕ, a.1 * (m : ℚ) = k := by
  intro a ha
  exact globalInventory_integral_for_iterate C hC m a (List.mem_filter.mp ha).1

/-- Filtering to the interior preserves the child mass-integrality fact. -/
theorem childInterior_integral_for_iterate (C : Certificate) (l : Stage C.top) (m : ℕ) :
    ∀ a ∈ interior (QAt C l), ∃ k : ℕ, a.1 * (m : ℚ) = k := by
  intro a ha
  exact childInventory_integral_for_iterate C l m a (List.mem_filter.mp ha).1

/-- The global boundary occurrences satisfy the public boundary-matrix hypotheses at scale one. -/
theorem globalBoundary_admissible_for_iterate (C : Certificate) (hC : AdmissibleAt C) :
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

/-- Every stage-child boundary occurrence satisfies the public boundary-matrix hypotheses. -/
theorem childBoundary_admissible_for_iterate (C : Certificate) (hC : AdmissibleAt C)
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

/-- Child atoms have exactly the stage width. -/
theorem childInventory_width_for_iterate (C : Certificate) (l : Stage C.top) :
    ∀ a ∈ QAt C l, a.2.1 = wid (l.val - 1) := by
  classical
  intro a ha
  cases hs : C.stage l with
  | none => simp [QAt, hs] at ha
  | some d =>
    rw [QAt, hs] at ha
    simp only [childInventory, List.mem_map] at ha
    rcases ha with ⟨i, hi, rfl⟩
    rfl

/-- Global atoms have the certificate width. -/
theorem globalInventory_width_for_iterate (C : Certificate) :
    ∀ a ∈ G C, a.2.1 = C.width := by
  classical
  intro a ha
  simp only [G, scaleInventory, globalInventory, List.mem_map] at ha
  rcases ha with ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  rfl

end
end OmegaBound.ADVXXZGeneral
end

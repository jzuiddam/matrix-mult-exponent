import OmegaBound.ADVXXZT6Round130fSemantic

/-! # Symbolic soundness of the exact evaluator -/

set_option maxRecDepth 1000000
set_library_suggestions Lean.LibrarySuggestions.empty

open Finset

namespace OmegaBound.ADVXXZT6Round130f

open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT9R16PositiveParents (releasedPositiveInput)

private noncomputable abbrev releasedData130f :=
  OmegaBound.ADVXXZT6Round82.releasedCorrectedData

def dualMarginReal130f (dual : DualQ130f) (W : Side) (a : Fin 5) : ℝ :=
  match W with
  | .X => dual.lambdaMargin 0 a
  | .Y => dual.lambdaMargin 1 a
  | .Z => dual.lambdaMargin 2 a

theorem sumQFin130f_cast {n : Nat} (f : Fin n → ℚ) :
    (sumQFin130f f : ℝ) = ∑ i, (f i : ℝ) := by
  unfold sumQFin130f
  rw [List.sum_ofFn]
  push_cast
  rfl

/-- Generic coefficient soundness against `ADVXXZT6Round61.releasedParentCoefficient`. -/
theorem coefficientQ130f_cast (r : Fin 6) (p : Fin 126) :
    (coefficientQ130f r p : ℝ) =
      OmegaBound.ADVXXZT6Round61.releasedParentCoefficient r p := by
  unfold coefficientQ130f OmegaBound.ADVXXZT6Round61.releasedParentCoefficient
  push_cast
  rfl

@[simp] theorem childQ130f_cast (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    (childQ130f p r d : ℝ) =
      releasedData130f.alpha p r
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) := by
  rw [childQ130f, probQ130f_cast]
  exact OmegaBound.ADVXXZT6Round130.releasedCorrectedData_alpha_childRowEquiv_symm130
    p r d |>.symm

theorem childRowEquiv_symm_rev130f (p : Fin 126)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm (Fin.rev d) =
      complement releasedPositiveInput p
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) := by
  apply (OmegaBound.ADVXXZT6Round78.childRowEquiv p).injective
  rw [(OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply]
  change Fin.rev d = OmegaBound.ADVXXZT6Round78.childIndex p
    (complement releasedPositiveInput p
      ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d))
  rw [OmegaBound.ADVXXZT6Round78.releasedComplementLayout]
  exact congrArg Fin.rev
    ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply d) |>.symm

@[simp] theorem symQ130f_cast (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    (symQ130f p r d : ℝ) =
      symWeight releasedData130f p r
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) := by
  rw [symQ130f, Rat.cast_add, childQ130f_cast, childQ130f_cast,
    OmegaBound.ADVXXZPaper.symWeight_eq_add_complement,
    childRowEquiv_symm_rev130f]

@[simp] theorem betaChildQ130f_cast (W : Side) (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) (i : Fin 9) :
    (betaChildQ130f W p r d i : ℝ) =
      (releasedData130f.betaChild W p r
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d)).probR
          (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm i) := by
  rw [betaChildQ130f, probQ130f_cast]
  unfold releasedData130f OmegaBound.ADVXXZT6Round82.releasedCorrectedData
    OmegaBound.ADVXXZT6Round82.certificateBetaChild
  congr 2
  exact (OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply d |>.symm

@[simp] theorem betaRegionQ130f_cast (W : Side) (p : Fin 126) (r : Fin 6)
    (i : Fin 81) :
    (betaRegionQ130f W p r i : ℝ) =
      (releasedData130f.betaRegion W p r).probR
        (OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm i) := by
  rw [betaRegionQ130f, probQ130f_cast]
  rfl

theorem marginalQ130f_cast (W : Side) (p : Fin 126) (r : Fin 6) (a : Fin 5) :
    (marginalQ130f W p r a : ℝ) =
      constituentMarginal releasedData130f p r W a := by
  rw [marginalQ130f, sumQFin130f_cast]
  unfold constituentMarginal
  rw [show (∑ d, ((if OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d W = a
      then childQ130f p r d else 0 : ℚ) : ℝ)) =
      ∑ d, if OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d W = a
        then (childQ130f p r d : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp]
  rw [show (∑ d, if OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d W = a
      then (childQ130f p r d : ℝ) else 0) =
      ∑ u : ChildShape releasedPositiveInput p,
        if OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W = a
        then (childQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ)
        else 0 by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [childQ130f_cast]
  rw [(OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
  have hl := OmegaBound.ADVXXZT6Round130.childLevel_childRowEquiv_symm130 p
    ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W
  rw [(OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply] at hl
  rw [← hl]
  change (if OmegaBound.ADVXXZT6Round130.childLevel130 p W u = a then _ else _) =
    if coord W u.1 = (a : Nat) then _ else _
  by_cases h : OmegaBound.ADVXXZT6Round130.childLevel130 p W u = a
  · rw [if_pos h, if_pos]
    simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using congrArg Fin.val h
  · rw [if_neg h, if_neg]
    intro hc
    apply h
    apply Fin.ext
    simpa [OmegaBound.ADVXXZT6Round130.childLevel130_val] using hc

theorem entropy_childQ130f_value (p : Fin 126) (r : Fin 6) :
    (entropyFin130f (childQ130f p r)).value =
      Entropy.H Finset.univ (releasedData130f.alpha p r) := by
  rw [value_entropyFin130f]
  unfold Entropy.H
  rw [show (∑ d, Real.negMulLog (childQ130f p r d : ℝ)) =
      ∑ u : ChildShape releasedPositiveInput p,
        Real.negMulLog (childQ130f p r
          ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ) by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [childQ130f_cast, (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]

theorem entropy_marginalQ130f_value (W : Side) (p : Fin 126) (r : Fin 6) :
    (entropyFin130f (marginalQ130f W p r)).value =
      Entropy.H Finset.univ (constituentMarginal releasedData130f p r W) := by
  rw [value_entropyFin130f]
  unfold Entropy.H
  apply Finset.sum_congr rfl
  intro a _
  rw [marginalQ130f_cast]

theorem dualLinearQ130f_cast (dual : DualQ130f) (p : Fin 126)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    (dualLinearQ130f dual p d : ℝ) =
      (dual.lambdaSum : ℝ) + ∑ W : Side,
        dualMarginReal130f dual W
          (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d W) := by
  unfold dualLinearQ130f dualMarginReal130f
  push_cast
  rw [show (Finset.univ : Finset Side) = {.X, .Y, .Z} by decide +kernel]
  simp
  ring

theorem fenchelQ130f_value (dual : DualQ130f) (p : Fin 126) (r : Fin 6) :
    (fenchelQ130f dual p r).value =
      OmegaBound.ADVXXZT6Round130.constituentFenchelUpper130 p
        (releasedData130f.alpha p r) (dual.lambdaSum : ℝ)
        (dualMarginReal130f dual) := by
  rw [OmegaBound.ADVXXZT6Round130.constituentFenchelUpper_reindex130]
  simp only [fenchelQ130f, value_sub130f, value_expSumFin130f,
    value_pure130f, value_sumFin130f]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    push_cast
    rw [dualLinearQ130f_cast]
  · rw [sumQFin130f_cast]
    apply Finset.sum_congr rfl
    intro d _
    rw [← dualLinearQ130f_cast, ← childQ130f_cast]
    push_cast
    rfl

/-- One symbolic proof interprets every X evaluator instance; no parent case split occurs. -/
theorem xQ130f_value (dual : DualQ130f) (p : Fin 126) (r : Fin 6) (W : Side) :
    (xQ130f dual p r W).value =
      (dual.coefficient : ℝ) *
        (Entropy.H Finset.univ (constituentMarginal releasedData130f p r W) +
          Entropy.H Finset.univ (releasedData130f.alpha p r) -
          OmegaBound.ADVXXZT6Round130.constituentFenchelUpper130 p
            (releasedData130f.alpha p r) (dual.lambdaSum : ℝ)
            (dualMarginReal130f dual)) := by
  rw [xQ130f, value_scale130f, value_sub130f, value_add130f,
    entropy_marginalQ130f_value, entropy_childQ130f_value, fenchelQ130f_value]

theorem releasedKidLevel_equiv130f (p : Fin 126)
    (u : ChildShape releasedPositiveInput p) (W : Side) :
    OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W =
      OmegaBound.ADVXXZT6Round130.childLevel130 p W u := by
  simpa using (OmegaBound.ADVXXZT6Round130.childLevel_childRowEquiv_symm130 p
    ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W).symm

theorem etaSelected_equiv130f (p : Fin 126) (ySide zSide : Side) (a : Fin 5)
    (u : ChildShape releasedPositiveInput p) :
    etaSelected130f p ySide zSide a
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) = true ↔
      coord ySide u.1 = (a : Nat) ∧ 0 < coord zSide u.1 := by
  unfold etaSelected130f
  rw [releasedKidLevel_equiv130f, releasedKidLevel_equiv130f]
  constructor
  · intro h
    have h' := of_decide_eq_true h
    exact ⟨by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using
      congrArg Fin.val h'.1, by simpa only
        [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h'.2⟩
  · intro h
    apply decide_eq_true
    exact ⟨Fin.ext (by simpa only
      [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h.1), by simpa only
        [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h.2⟩

theorem entropy_betaChildQ130f_value (W : Side) (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    (entropyFin130f (betaChildQ130f W p r d)).value =
      OmegaBound.ADVXXZT6Round130.splitEntropyNats130
        (releasedData130f.betaChild W p r
          ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d)) := by
  rw [value_entropyFin130f]
  unfold OmegaBound.ADVXXZT6Round130.splitEntropyNats130 Entropy.H
  rw [show (∑ i : Fin 9, Real.negMulLog (betaChildQ130f W p r d i : ℝ)) =
      ∑ σ : OmegaBound.ADVXXZ.Chunk 2,
        Real.negMulLog (betaChildQ130f W p r d
          (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv σ) : ℝ) by
    exact (Equiv.sum_comp OmegaBound.ADVXXZT6SplitTargetData.wordEquiv _).symm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [betaChildQ130f_cast,
    OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm_apply_apply]

theorem entropy_betaRegionQ130f_value (W : Side) (p : Fin 126) (r : Fin 6) :
    (entropyFin130f (betaRegionQ130f W p r)).value =
      OmegaBound.ADVXXZT6Round130.splitEntropyNats130
        (releasedData130f.betaRegion W p r) := by
  rw [value_entropyFin130f]
  unfold OmegaBound.ADVXXZT6Round130.splitEntropyNats130 Entropy.H
  rw [show (∑ i : Fin 81, Real.negMulLog (betaRegionQ130f W p r i : ℝ)) =
      ∑ σ : OmegaBound.ADVXXZ.Chunk 4,
        Real.negMulLog (betaRegionQ130f W p r
          (OmegaBound.ADVXXZT6DenominatorData.wordEquiv4 σ) : ℝ) by
    exact (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4 _).symm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [betaRegionQ130f_cast,
    OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm_apply_apply]

theorem selectedMass_eta130f_cast (p : Fin 126) (r : Fin 6)
    (ySide zSide : Side) (a : Fin 5) :
    (selectedMassQ130f p r (etaSelected130f p ySide zSide a) : ℝ) =
      ∑ u : ChildShape releasedPositiveInput p,
        if coord ySide u.1 = (a : Nat) ∧ 0 < coord zSide u.1
        then symWeight releasedData130f p r u else 0 := by
  rw [selectedMassQ130f, sumQFin130f_cast]
  rw [show (∑ d, ((if etaSelected130f p ySide zSide a d
      then symQ130f p r d else 0 : ℚ) : ℝ)) =
      ∑ d, if etaSelected130f p ySide zSide a d
        then (symQ130f p r d : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp]
  rw [show (∑ d, if etaSelected130f p ySide zSide a d
      then (symQ130f p r d : ℝ) else 0) =
      ∑ u : ChildShape releasedPositiveInput p,
        if etaSelected130f p ySide zSide a
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u)
        then (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ)
        else 0 by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [symQ130f_cast, (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
  by_cases h : coord ySide u.1 = (a : Nat) ∧ 0 < coord zSide u.1
  · rw [if_pos h, if_pos ((etaSelected_equiv130f p ySide zSide a u).mpr h)]
  · rw [if_neg h, if_neg]
    exact fun hs => h ((etaSelected_equiv130f p ySide zSide a u).mp hs)

theorem selectedBeta_eta130f_cast (p : Fin 126) (r : Fin 6)
    (ySide zSide : Side) (a : Fin 5) (i : Fin 9) :
    (selectedBetaQ130f ySide p r (etaSelected130f p ySide zSide a) i : ℝ) =
      constituentAverage releasedData130f p r ySide ySide zSide a
        (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm i) := by
  unfold selectedBetaQ130f constituentAverage weightedSplit
  push_cast
  rw [sumQFin130f_cast, selectedMass_eta130f_cast]
  congr 1
  rw [show (∑ d, ((if etaSelected130f p ySide zSide a d then
      symQ130f p r d * betaChildQ130f ySide p r d i else 0 : ℚ) : ℝ)) =
      ∑ d, if etaSelected130f p ySide zSide a d then
        (symQ130f p r d : ℝ) * (betaChildQ130f ySide p r d i : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp]
  rw [show (∑ d, if etaSelected130f p ySide zSide a d then
      (symQ130f p r d : ℝ) * (betaChildQ130f ySide p r d i : ℝ) else 0) =
      ∑ u : ChildShape releasedPositiveInput p,
        if etaSelected130f p ySide zSide a
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) then
          (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ) *
          (betaChildQ130f ySide p r
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) i : ℝ) else 0 by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [symQ130f_cast, betaChildQ130f_cast,
    (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
  by_cases h : coord ySide u.1 = (a : Nat) ∧ 0 < coord zSide u.1
  · rw [if_pos h, if_pos ((etaSelected_equiv130f p ySide zSide a u).mpr h)]
  · rw [if_neg h, if_neg]
    exact fun hs => h ((etaSelected_equiv130f p ySide zSide a u).mp hs)

theorem entropy_selectedBeta_eta130f_value (p : Fin 126) (r : Fin 6)
    (ySide zSide : Side) (a : Fin 5) :
    (entropyFin130f
      (selectedBetaQ130f ySide p r (etaSelected130f p ySide zSide a))).value =
      Entropy.H Finset.univ
        (constituentAverage releasedData130f p r ySide ySide zSide a) := by
  rw [value_entropyFin130f]
  unfold Entropy.H
  rw [show (∑ i : Fin 9, Real.negMulLog
      (selectedBetaQ130f ySide p r (etaSelected130f p ySide zSide a) i : ℝ)) =
      ∑ σ : OmegaBound.ADVXXZ.Chunk 2, Real.negMulLog
        (selectedBetaQ130f ySide p r (etaSelected130f p ySide zSide a)
          (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv σ) : ℝ) by
    exact (Equiv.sum_comp OmegaBound.ADVXXZT6SplitTargetData.wordEquiv _).symm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [selectedBeta_eta130f_cast,
    OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm_apply_apply]

/-- One symbolic proof interprets every eta evaluator instance; no parent case split occurs. -/
theorem etaQ130f_value (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    (etaQ130f p r xSide ySide zSide).value =
      OmegaBound.ADVXXZT6Round130.constituentEtaNats130
        releasedData130f p r xSide ySide zSide := by
  unfold etaQ130f OmegaBound.ADVXXZT6Round130.constituentEtaNats130
  rw [value_add130f, value_sumFin130f, value_sumFin130f]
  congr 1
  · rw [show (∑ d, (if
        (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d zSide).val = 0 then
          scale130f (symQ130f p r d) (entropyFin130f (betaChildQ130f ySide p r d))
        else zero130f).value) =
      ∑ u : ChildShape releasedPositiveInput p,
        (if (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) zSide).val = 0 then
          scale130f (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u))
            (entropyFin130f (betaChildQ130f ySide p r
              ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u)))
        else zero130f).value by
      exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
    apply Finset.sum_congr rfl
    intro u _
    rw [releasedKidLevel_equiv130f]
    rw [OmegaBound.ADVXXZT6Round130.childLevel130_val]
    by_cases h : coord zSide u.1 = 0
    · rw [if_pos h, if_pos h, value_scale130f, symQ130f_cast,
        entropy_betaChildQ130f_value,
        (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
    · rw [if_neg h, if_neg h, value_zero130f]
  · apply Finset.sum_congr rfl
    intro a _
    rw [value_scale130f, selectedMass_eta130f_cast,
      entropy_selectedBeta_eta130f_value]

theorem yQ130f_value (coefficient : ℚ) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    (yQ130f coefficient p r xSide ySide zSide).value =
      (coefficient : ℝ) *
        (OmegaBound.ADVXXZT6Round130.splitEntropyNats130
            (releasedData130f.betaRegion ySide p r) -
          OmegaBound.ADVXXZT6Round130.constituentEtaNats130
            releasedData130f p r xSide ySide zSide) := by
  rw [yQ130f, value_scale130f, value_sub130f,
    entropy_betaRegionQ130f_value, etaQ130f_value]

theorem lambdaSelected_equiv130f (p : Fin 126) (xSide ySide zSide : Side)
    (a : Fin 5) (u : ChildShape releasedPositiveInput p) :
    lambdaSelected130f p xSide ySide zSide a
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) = true ↔
      0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧ coord zSide u.1 = (a : Nat) := by
  unfold lambdaSelected130f
  rw [releasedKidLevel_equiv130f, releasedKidLevel_equiv130f,
    releasedKidLevel_equiv130f]
  constructor
  · intro h
    have h' := of_decide_eq_true h
    exact ⟨by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h'.1,
      by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h'.2.1,
      by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using
        congrArg Fin.val h'.2.2⟩
  · intro h
    apply decide_eq_true
    exact ⟨by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h.1,
      by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h.2.1,
      Fin.ext (by simpa only [OmegaBound.ADVXXZT6Round130.childLevel130_val] using h.2.2)⟩

theorem selectedMass_lambda130f_cast (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) (a : Fin 5) :
    (selectedMassQ130f p r (lambdaSelected130f p xSide ySide zSide a) : ℝ) =
      ∑ u : ChildShape releasedPositiveInput p,
        if 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧ coord zSide u.1 = (a : Nat)
        then symWeight releasedData130f p r u else 0 := by
  rw [selectedMassQ130f, sumQFin130f_cast]
  rw [show (∑ d, ((if lambdaSelected130f p xSide ySide zSide a d
      then symQ130f p r d else 0 : ℚ) : ℝ)) =
      ∑ d, if lambdaSelected130f p xSide ySide zSide a d
        then (symQ130f p r d : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp]
  rw [show (∑ d, if lambdaSelected130f p xSide ySide zSide a d
      then (symQ130f p r d : ℝ) else 0) =
      ∑ u : ChildShape releasedPositiveInput p,
        if lambdaSelected130f p xSide ySide zSide a
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u)
        then (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ)
        else 0 by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [symQ130f_cast, (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
  let P := 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧ coord zSide u.1 = (a : Nat)
  by_cases h : P
  · rw [if_pos h, if_pos ((lambdaSelected_equiv130f p xSide ySide zSide a u).mpr h)]
  · rw [if_neg h, if_neg]
    exact fun hs => h ((lambdaSelected_equiv130f p xSide ySide zSide a u).mp hs)

theorem selectedBeta_lambda130f_cast (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) (a : Fin 5) (i : Fin 9) :
    (selectedBetaQ130f zSide p r
        (lambdaSelected130f p xSide ySide zSide a) i : ℝ) =
      weightedSplit (symWeight releasedData130f p r)
        (releasedData130f.betaChild zSide p r)
        (fun u => 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
          coord zSide u.1 = (a : Nat))
        (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm i) := by
  unfold selectedBetaQ130f weightedSplit
  push_cast
  rw [sumQFin130f_cast, selectedMass_lambda130f_cast]
  congr 1
  rw [show (∑ d, ((if lambdaSelected130f p xSide ySide zSide a d then
      symQ130f p r d * betaChildQ130f zSide p r d i else 0 : ℚ) : ℝ)) =
      ∑ d, if lambdaSelected130f p xSide ySide zSide a d then
        (symQ130f p r d : ℝ) * (betaChildQ130f zSide p r d i : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp]
  rw [show (∑ d, if lambdaSelected130f p xSide ySide zSide a d then
      (symQ130f p r d : ℝ) * (betaChildQ130f zSide p r d i : ℝ) else 0) =
      ∑ u : ChildShape releasedPositiveInput p,
        if lambdaSelected130f p xSide ySide zSide a
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) then
          (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) : ℝ) *
          (betaChildQ130f zSide p r
            ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) i : ℝ) else 0 by
    exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
  apply Finset.sum_congr rfl
  intro u _
  rw [symQ130f_cast, betaChildQ130f_cast,
    (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
  let P := 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧ coord zSide u.1 = (a : Nat)
  by_cases h : P
  · rw [if_pos h, if_pos ((lambdaSelected_equiv130f p xSide ySide zSide a u).mpr h)]
  · rw [if_neg h, if_neg]
    exact fun hs => h ((lambdaSelected_equiv130f p xSide ySide zSide a u).mp hs)

theorem entropy_selectedBeta_lambda130f_value (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) (a : Fin 5) :
    (entropyFin130f (selectedBetaQ130f zSide p r
      (lambdaSelected130f p xSide ySide zSide a))).value =
      Entropy.H Finset.univ
        (weightedSplit (symWeight releasedData130f p r)
          (releasedData130f.betaChild zSide p r)
          (fun u => 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
            coord zSide u.1 = (a : Nat))) := by
  rw [value_entropyFin130f]
  unfold Entropy.H
  rw [show (∑ i : Fin 9, Real.negMulLog
      (selectedBetaQ130f zSide p r
        (lambdaSelected130f p xSide ySide zSide a) i : ℝ)) =
      ∑ σ : OmegaBound.ADVXXZ.Chunk 2, Real.negMulLog
        (selectedBetaQ130f zSide p r
          (lambdaSelected130f p xSide ySide zSide a)
          (OmegaBound.ADVXXZT6SplitTargetData.wordEquiv σ) : ℝ) by
    exact (Equiv.sum_comp OmegaBound.ADVXXZT6SplitTargetData.wordEquiv _).symm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [selectedBeta_lambda130f_cast,
    OmegaBound.ADVXXZT6SplitTargetData.wordEquiv.symm_apply_apply]

/-- One symbolic proof interprets every lambda evaluator instance; no parent case split occurs. -/
theorem lambdaQ130f_value (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    (lambdaQ130f p r xSide ySide zSide).value =
      OmegaBound.ADVXXZT6Round130.constituentLambdaNats130
        releasedData130f p r xSide ySide zSide := by
  unfold lambdaQ130f OmegaBound.ADVXXZT6Round130.constituentLambdaNats130
  rw [value_add130f, value_sumFin130f, value_sumFin130f]
  congr 1
  · rw [show (∑ d, (if
        (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d xSide).val = 0 ∨
          (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p d ySide).val = 0 then
          scale130f (symQ130f p r d) (entropyFin130f (betaChildQ130f zSide p r d))
        else zero130f).value) =
      ∑ u : ChildShape releasedPositiveInput p,
        (if (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p
              ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) xSide).val = 0 ∨
            (OmegaBound.ADVXXZT6Round130.releasedKidLevel130 p
              ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) ySide).val = 0 then
          scale130f (symQ130f p r ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u))
            (entropyFin130f (betaChildQ130f zSide p r
              ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u)))
        else zero130f).value by
      exact (Equiv.sum_comp (OmegaBound.ADVXXZT6Round78.childRowEquiv p) _).symm]
    apply Finset.sum_congr rfl
    intro u _
    rw [releasedKidLevel_equiv130f, releasedKidLevel_equiv130f,
      OmegaBound.ADVXXZT6Round130.childLevel130_val,
      OmegaBound.ADVXXZT6Round130.childLevel130_val]
    by_cases h : coord xSide u.1 = 0 ∨ coord ySide u.1 = 0
    · rw [if_pos h, if_pos h, value_scale130f, symQ130f_cast,
        entropy_betaChildQ130f_value,
        (OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm_apply_apply]
    · rw [if_neg h, if_neg h, value_zero130f]
  · apply Finset.sum_congr rfl
    intro a _
    rw [value_scale130f, selectedMass_lambda130f_cast,
      entropy_selectedBeta_lambda130f_value]

theorem zQ130f_value (coefficient : ℚ) (p : Fin 126) (r : Fin 6)
    (xSide ySide zSide : Side) :
    (zQ130f coefficient p r xSide ySide zSide).value =
      (coefficient : ℝ) *
        (OmegaBound.ADVXXZT6Round130.splitEntropyNats130
            (releasedData130f.betaRegion zSide p r) -
          OmegaBound.ADVXXZT6Round130.constituentLambdaNats130
            releasedData130f p r xSide ySide zSide) := by
  rw [zQ130f, value_scale130f, value_sub130f,
    entropy_betaRegionQ130f_value, lambdaQ130f_value]

/-- The released Lean-side quantity represented by a row, in logical role order.
The coefficient is deliberately recomputed from `coefficientQ130f` rather than trusted from
the generated dual table. -/
noncomputable def semanticQuantity130f (dual : DualQ130f) (p : Fin 126)
    (r : Fin 6) (role : Fin 3) : ℝ :=
  let xSide := physicalRole130f r .X
  let ySide := physicalRole130f r .Y
  let zSide := physicalRole130f r .Z
  let coefficient := (coefficientQ130f r p : ℝ)
  match role.val with
  | 0 => coefficient *
      (Entropy.H Finset.univ
          (constituentMarginal releasedData130f p r xSide) +
        Entropy.H Finset.univ (releasedData130f.alpha p r) -
        OmegaBound.ADVXXZT6Round130.constituentFenchelUpper130 p
          (releasedData130f.alpha p r) (dual.lambdaSum : ℝ)
          (dualMarginReal130f dual))
  | 1 => coefficient *
      (OmegaBound.ADVXXZT6Round130.splitEntropyNats130
          (releasedData130f.betaRegion ySide p r) -
        OmegaBound.ADVXXZT6Round130.constituentEtaNats130
          releasedData130f p r xSide ySide zSide)
  | _ => coefficient *
      (OmegaBound.ADVXXZT6Round130.splitEntropyNats130
          (releasedData130f.betaRegion zSide p r) -
        OmegaBound.ADVXXZT6Round130.constituentLambdaNats130
          releasedData130f p r xSide ySide zSide)

/-- Generic semantic soundness for all three quantity kinds.  Its only finite premise is the
exact rational coefficient check; the proof has no parent or region case split. -/
theorem semanticRowQ130f_value (dual : DualQ130f) (p : Fin 126) (r : Fin 6)
    (role : Fin 3)
    (hcoefficient : (dual.coefficient : ℝ) = (coefficientQ130f r p : ℝ)) :
    (semanticRowQ130f dual p r role).value = semanticQuantity130f dual p r role := by
  fin_cases role <;>
    simp only [semanticRowQ130f, semanticQuantity130f]
  · rw [xQ130f_value, hcoefficient]
  · rw [yQ130f_value, hcoefficient]
  · rw [zQ130f_value, hcoefficient]

end OmegaBound.ADVXXZT6Round130f

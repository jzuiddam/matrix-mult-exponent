import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorSplit

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_library_suggestions Lean.LibrarySuggestions.empty

private theorem evaluator_child_prob_zero_or_one (W : Side) (v : Shape 1)
    (sigma : Chunk 1) :
    (ordinaryChildBeta W v).probR sigma = 0 ∨
      (ordinaryChildBeta W v).probR sigma = 1 := by
  by_cases h : (sigma 0).val = coord W v
  · right
    simp [ordinaryChildBeta, RatDist.probR, h]
  · left
    simp [ordinaryChildBeta, RatDist.probR, h]

private theorem evaluator_child_split_zero (W : Side) (v : Shape 1) :
    splitEntropy (ordinaryChildBeta W v) = 0 := by
  unfold splitEntropy entropy Entropy.H₂ Entropy.H
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro sigma _
  rcases evaluator_child_prob_zero_or_one W v sigma with hp | hp
  · rw [hp, Real.negMulLog_zero]
  · rw [hp, Real.negMulLog_one]

private theorem evaluator_weighted_delta_value {iota : Type*} [Fintype iota]
    (mass : iota → ℝ) (shape : iota → Shape 1) (selected : iota → Prop)
    [DecidablePred selected] (W : Side) (a : ℕ)
    (hselected : ∀ x, selected x → coord W (shape x) = a) (sigma : Chunk 1) :
    weightedSplit mass (fun x => ordinaryChildBeta W (shape x)) selected sigma = 0 ∨
      weightedSplit mass (fun x => ordinaryChildBeta W (shape x)) selected sigma = 1 := by
  classical
  let total := ∑ x, if selected x then mass x else 0
  by_cases hsigma : (sigma 0).val = a
  · have hnum :
        (∑ x, if selected x then
          mass x * (ordinaryChildBeta W (shape x)).probR sigma else 0) = total := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : selected x
        · have hcoord := hselected x hx
          simp [hx, ordinaryChildBeta, RatDist.probR, hsigma, hcoord, total]
        · simp [hx]
    unfold weightedSplit
    rw [hnum]
    by_cases htotal : total = 0
    · left
      simp [htotal]
    · right
      exact div_self htotal
  · left
    unfold weightedSplit
    have hnum :
        (∑ x, if selected x then
          mass x * (ordinaryChildBeta W (shape x)).probR sigma else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : selected x
      · have hcoord := hselected x hx
        simp [hx, ordinaryChildBeta, RatDist.probR, hsigma, hcoord]
      · simp [hx]
    rw [hnum]
    simp

private theorem evaluator_weighted_delta_entropy {iota : Type*} [Fintype iota]
    (mass : iota → ℝ) (shape : iota → Shape 1) (selected : iota → Prop)
    [DecidablePred selected] (W : Side) (a : ℕ)
    (hselected : ∀ x, selected x → coord W (shape x) = a) :
    entropy (weightedSplit mass (fun x => ordinaryChildBeta W (shape x)) selected) = 0 := by
  unfold entropy Entropy.H₂ Entropy.H
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro sigma _
  rcases evaluator_weighted_delta_value mass shape selected W a hselected sigma with hp | hp
  · rw [hp, Real.negMulLog_zero]
  · rw [hp, Real.negMulLog_one]

private theorem evaluator_eta_first_zero
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (Y Z : Side) :
    (∑ u, if coord Z u.1 = 0 then
      symWeight d t r u * splitEntropy (d.betaChild Y t r u) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : coord Z u.1 = 0
  · rw [if_pos hu, hbeta, evaluator_child_split_zero, mul_zero]
  · rw [if_neg hu]

set_option maxHeartbeats 1000000 in
private theorem evaluator_constituentAverage_zero
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (Y Z : Side) (a : Fin 3) :
    entropy (constituentAverage d t r Y Y Z a) = 0 := by
  unfold constituentAverage
  rw [show d.betaChild Y t r = (fun u => ordinaryChildBeta Y u.1) by
    funext u
    exact hbeta Y t r u]
  exact evaluator_weighted_delta_entropy
    (iota := ChildShape releasedOrdinaryParent t)
    (mass := symWeight d t r) (shape := fun u => u.1)
    (selected := fun u => coord Y u.1 = (a : ℕ) ∧ 0 < coord Z u.1)
    (W := Y) (a := a) (fun _ h => h.1)

private theorem evaluator_eta_zero_of_child_delta
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) :
    constituentEta d t r X Y Z = 0 := by
  unfold constituentEta
  rw [evaluator_eta_first_zero d hbeta t r Y Z, zero_add]
  apply Finset.sum_eq_zero
  intro a _
  apply mul_eq_zero_of_right
  exact evaluator_constituentAverage_zero d hbeta t r Y Z a

private theorem evaluator_lambda_first_zero
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) :
    (∑ u, if coord X u.1 = 0 ∨ coord Y u.1 = 0 then
      symWeight d t r u * splitEntropy (d.betaChild Z t r u) else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : coord X u.1 = 0 ∨ coord Y u.1 = 0
  · rw [if_pos hu, hbeta, evaluator_child_split_zero, mul_zero]
  · rw [if_neg hu]

set_option maxHeartbeats 1000000 in
private theorem evaluator_lambda_average_zero
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) (a : Fin 3) :
    entropy (weightedSplit (symWeight d t r) (d.betaChild Z t r)
      (fun u => 0 < coord X u.1 ∧ 0 < coord Y u.1 ∧ coord Z u.1 = (a : ℕ))) = 0 := by
  rw [show d.betaChild Z t r = (fun u => ordinaryChildBeta Z u.1) by
    funext u
    exact hbeta Z t r u]
  exact evaluator_weighted_delta_entropy
    (iota := ChildShape releasedOrdinaryParent t)
    (mass := symWeight d t r) (shape := fun u => u.1)
    (selected := fun u => 0 < coord X u.1 ∧ 0 < coord Y u.1 ∧
      coord Z u.1 = (a : ℕ)) (W := Z) (a := a) (fun _ h => h.2.2)

private theorem evaluator_lambda_zero_of_child_delta
    (d : ConstituentData releasedOrdinaryParent)
    (hbeta : ∀ W t r u, d.betaChild W t r u = ordinaryChildBeta W u.1)
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) :
    constituentLambda d t r X Y Z = 0 := by
  unfold constituentLambda
  rw [evaluator_lambda_first_zero d hbeta t r X Y Z, zero_add]
  apply Finset.sum_eq_zero
  intro a _
  apply mul_eq_zero_of_right
  exact evaluator_lambda_average_zero d hbeta t r X Y Z a

theorem released_ordinary_eta_zero
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) :
    constituentEta releasedOrdinaryData2.toPaper t r X Y Z = 0 := by
  apply evaluator_eta_zero_of_child_delta releasedOrdinaryData2.toPaper
  intro W t r u
  rfl

theorem released_ordinary_lambda_zero
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6)
    (X Y Z : Side) :
    constituentLambda releasedOrdinaryData2.toPaper t r X Y Z = 0 := by
  apply evaluator_lambda_zero_of_child_delta releasedOrdinaryData2.toPaper
  intro W t r u
  rfl

end OmegaBound.ADVXXZGeneral
end

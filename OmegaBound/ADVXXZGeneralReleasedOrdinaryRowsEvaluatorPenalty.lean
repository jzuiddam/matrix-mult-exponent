import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorZero

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_library_suggestions Lean.LibrarySuggestions.empty

private def evaluatorShape211 : Shape 2 := ⟨(2, 1, 1), by decide +kernel⟩
private def evaluatorShape121 : Shape 2 := ⟨(1, 2, 1), by decide +kernel⟩
private def evaluatorShape112 : Shape 2 := ⟨(1, 1, 2), by decide +kernel⟩

private def evaluator211_011 : OrdinaryChild evaluatorShape211 :=
  ⟨⟨(0, 1, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator211_101 : OrdinaryChild evaluatorShape211 :=
  ⟨⟨(1, 0, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator211_110 : OrdinaryChild evaluatorShape211 :=
  ⟨⟨(1, 1, 0), by decide +kernel⟩, by decide +kernel⟩
private def evaluator211_200 : OrdinaryChild evaluatorShape211 :=
  ⟨⟨(2, 0, 0), by decide +kernel⟩, by decide +kernel⟩

private def evaluator121_011 : OrdinaryChild evaluatorShape121 :=
  ⟨⟨(0, 1, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator121_101 : OrdinaryChild evaluatorShape121 :=
  ⟨⟨(1, 0, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator121_110 : OrdinaryChild evaluatorShape121 :=
  ⟨⟨(1, 1, 0), by decide +kernel⟩, by decide +kernel⟩
private def evaluator121_020 : OrdinaryChild evaluatorShape121 :=
  ⟨⟨(0, 2, 0), by decide +kernel⟩, by decide +kernel⟩

private def evaluator112_011 : OrdinaryChild evaluatorShape112 :=
  ⟨⟨(0, 1, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator112_101 : OrdinaryChild evaluatorShape112 :=
  ⟨⟨(1, 0, 1), by decide +kernel⟩, by decide +kernel⟩
private def evaluator112_110 : OrdinaryChild evaluatorShape112 :=
  ⟨⟨(1, 1, 0), by decide +kernel⟩, by decide +kernel⟩
private def evaluator112_002 : OrdinaryChild evaluatorShape112 :=
  ⟨⟨(0, 0, 2), by decide +kernel⟩, by decide +kernel⟩

private def evaluatorSameMarginals (v : Shape 2)
    (a a' : OrdinaryChild v → ℝ) : Prop :=
  ∀ W x, (∑ u, if coord W u.1 = (x : ℕ) then a u else 0) =
    ∑ u, if coord W u.1 = (x : ℕ) then a' u else 0

private theorem evaluator_univ_211 :
    (Finset.univ : Finset (OrdinaryChild evaluatorShape211)) =
      {evaluator211_011, evaluator211_101, evaluator211_110, evaluator211_200} := by
  decide +kernel

private theorem evaluator_univ_121 :
    (Finset.univ : Finset (OrdinaryChild evaluatorShape121)) =
      {evaluator121_011, evaluator121_101, evaluator121_110, evaluator121_020} := by
  decide +kernel

private theorem evaluator_univ_112 :
    (Finset.univ : Finset (OrdinaryChild evaluatorShape112)) =
      {evaluator112_011, evaluator112_101, evaluator112_110, evaluator112_002} := by
  decide +kernel

private theorem evaluator_unique_211 (a a' : OrdinaryChild evaluatorShape211 → ℝ)
    (h : evaluatorSameMarginals evaluatorShape211 a a') : a = a' := by
  have hx0 := h .X (0 : Fin 3)
  have hx2 := h .X (2 : Fin 3)
  have hy0 := h .Y (0 : Fin 3)
  have hz0 := h .Z (0 : Fin 3)
  rw [evaluator_univ_211] at hx0 hx2 hy0 hz0
  simp [evaluator211_011, evaluator211_101, evaluator211_110, evaluator211_200,
    evaluatorShape211, coord] at hx0 hx2 hy0 hz0
  change a evaluator211_200 = a' evaluator211_200 at hx2
  change a evaluator211_101 + a evaluator211_200 =
    a' evaluator211_101 + a' evaluator211_200 at hy0
  change a evaluator211_110 + a evaluator211_200 =
    a' evaluator211_110 + a' evaluator211_200 at hz0
  funext u
  have hu : u = evaluator211_011 ∨ u = evaluator211_101 ∨
      u = evaluator211_110 ∨ u = evaluator211_200 := by
    have hm : u ∈ (Finset.univ : Finset (OrdinaryChild evaluatorShape211)) :=
      Finset.mem_univ u
    rw [evaluator_univ_211] at hm
    simpa using hm
  rcases hu with rfl | rfl | rfl | rfl
  · exact hx0
  · linarith
  · linarith
  · exact hx2

private theorem evaluator_unique_121 (a a' : OrdinaryChild evaluatorShape121 → ℝ)
    (h : evaluatorSameMarginals evaluatorShape121 a a') : a = a' := by
  have hy0 := h .Y (0 : Fin 3)
  have hy2 := h .Y (2 : Fin 3)
  have hx0 := h .X (0 : Fin 3)
  have hz0 := h .Z (0 : Fin 3)
  rw [evaluator_univ_121] at hy0 hy2 hx0 hz0
  simp [evaluator121_011, evaluator121_101, evaluator121_110, evaluator121_020,
    evaluatorShape121, coord] at hy0 hy2 hx0 hz0
  change a evaluator121_020 = a' evaluator121_020 at hy2
  change a evaluator121_011 + a evaluator121_020 =
    a' evaluator121_011 + a' evaluator121_020 at hx0
  change a evaluator121_110 + a evaluator121_020 =
    a' evaluator121_110 + a' evaluator121_020 at hz0
  funext u
  have hu : u = evaluator121_011 ∨ u = evaluator121_101 ∨
      u = evaluator121_110 ∨ u = evaluator121_020 := by
    have hm : u ∈ (Finset.univ : Finset (OrdinaryChild evaluatorShape121)) :=
      Finset.mem_univ u
    rw [evaluator_univ_121] at hm
    simpa using hm
  rcases hu with rfl | rfl | rfl | rfl
  · linarith
  · exact hy0
  · linarith
  · exact hy2

private theorem evaluator_unique_112 (a a' : OrdinaryChild evaluatorShape112 → ℝ)
    (h : evaluatorSameMarginals evaluatorShape112 a a') : a = a' := by
  have hz0 := h .Z (0 : Fin 3)
  have hz2 := h .Z (2 : Fin 3)
  have hx0 := h .X (0 : Fin 3)
  have hy0 := h .Y (0 : Fin 3)
  rw [evaluator_univ_112] at hz0 hz2 hx0 hy0
  simp [evaluator112_011, evaluator112_101, evaluator112_110, evaluator112_002,
    evaluatorShape112, coord] at hz0 hz2 hx0 hy0
  change a evaluator112_002 = a' evaluator112_002 at hz2
  change a evaluator112_011 + a evaluator112_002 =
    a' evaluator112_011 + a' evaluator112_002 at hx0
  change a evaluator112_101 + a evaluator112_002 =
    a' evaluator112_101 + a' evaluator112_002 at hy0
  funext u
  have hu : u = evaluator112_011 ∨ u = evaluator112_101 ∨
      u = evaluator112_110 ∨ u = evaluator112_002 := by
    have hm : u ∈ (Finset.univ : Finset (OrdinaryChild evaluatorShape112)) :=
      Finset.mem_univ u
    rw [evaluator_univ_112] at hm
    simpa using hm
  rcases hu with rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · exact hz0
  · exact hz2

private theorem evaluator_unique_interior (v : Shape 2)
    (hx : 0 < coord .X v) (hy : 0 < coord .Y v) (hz : 0 < coord .Z v)
    (a a' : OrdinaryChild v → ℝ) (h : evaluatorSameMarginals v a a') : a = a' := by
  have hsum := v.property
  change coord .X v + coord .Y v + coord .Z v = 4 at hsum
  have hv : v = evaluatorShape211 ∨ v = evaluatorShape121 ∨ v = evaluatorShape112 := by
    unfold evaluatorShape211 evaluatorShape121 evaluatorShape112
    by_cases hx2 : coord .X v = 2
    · left
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        exact hx2
      · apply Prod.ext
        · apply Fin.ext
          change coord .Y v = 1
          omega
        · apply Fin.ext
          change coord .Z v = 1
          omega
    · by_cases hy2 : coord .Y v = 2
      · right; left
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          change coord .X v = 1
          omega
        · apply Prod.ext
          · apply Fin.ext
            exact hy2
          · apply Fin.ext
            change coord .Z v = 1
            omega
      · right; right
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          change coord .X v = 1
          omega
        · apply Prod.ext
          · apply Fin.ext
            change coord .Y v = 1
            omega
          · apply Fin.ext
            change coord .Z v = 2
            omega
  rcases hv with rfl | rfl | rfl
  · exact evaluator_unique_211 a a' h
  · exact evaluator_unique_121 a a' h
  · exact evaluator_unique_112 a a' h

private theorem evaluator_released_same_unique
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence))
    (a a' : ChildShape releasedOrdinaryParent t → ℝ)
    (h : SameConstituentMarginals t a a') : a = a' := by
  let v := (ordinaryOccurrence t).1.2.2.1
  have h' : evaluatorSameMarginals v a a' := by
    intro W x
    exact h W x
  exact evaluator_unique_interior v (ordinaryOccurrence t).2.2.1
    (ordinaryOccurrence t).2.2.2.1 (ordinaryOccurrence t).2.2.2.2 a a' h'

private theorem evaluator_penalty_eq_zero_of_unique {w s : ℕ}
    {p : ConstituentInput w s} (d : ConstituentData p) (t : Fin s) (r : Fin 6)
    (hprob : IsProbability (d.alpha t r))
    (hunique : ∀ a' : ChildShape p t → ℝ,
      SameConstituentMarginals t (d.alpha t r) a' → a' = d.alpha t r) :
    constituentPenalty d t r = 0 := by
  unfold constituentPenalty
  have hset :
      {h : ℝ | ∃ a' : ChildShape p t → ℝ,
        IsProbability a' ∧ SameConstituentMarginals t (d.alpha t r) a' ∧
          h = entropy a'} = {entropy (d.alpha t r)} := by
    ext h
    constructor
    · rintro ⟨a', _, hsame, rfl⟩
      rw [hunique a' hsame]
      exact Set.mem_singleton _
    · intro hh
      have heq : h = entropy (d.alpha t r) := by simpa only [Set.mem_singleton_iff] using hh
      refine ⟨d.alpha t r, hprob, ?_, heq⟩
      intro W x
      rfl
  rw [hset, csSup_singleton]
  ring

theorem released_ordinary_penalty_zero
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) :
    constituentPenalty releasedOrdinaryData2.toPaper t r = 0 := by
  apply evaluator_penalty_eq_zero_of_unique
  · exact ⟨(releasedOrdinaryData2.alpha t r).probR_nonneg,
      (releasedOrdinaryData2.alpha t r).sum_probR⟩
  · intro a' hsame
    exact (evaluator_released_same_unique t _ a' hsame).symm

theorem released_ordinary_zero_semantics :
    ∀ t r, constituentPenalty releasedOrdinaryData2.toPaper t r = 0 ∧
      (∀ X Y Z, constituentEta releasedOrdinaryData2.toPaper t r X Y Z = 0 ∧
        constituentLambda releasedOrdinaryData2.toPaper t r X Y Z = 0) := by
  intro t r
  exact ⟨released_ordinary_penalty_zero t r, fun X Y Z =>
    ⟨released_ordinary_eta_zero t r X Y Z,
      released_ordinary_lambda_zero t r X Y Z⟩⟩

theorem released_ordinary_level2_semantics :
    ∀ t r, constituentPenalty releasedOrdinaryData2.toPaper t r = 0 ∧
      (∀ X Y Z, constituentEta releasedOrdinaryData2.toPaper t r X Y Z = 0 ∧
        constituentLambda releasedOrdinaryData2.toPaper t r X Y Z = 0) ∧
      ∀ W, Real.log 2 * entropy
          (constituentMarginal releasedOrdinaryData2.toPaper t r W) =
          ordinary112Nats t W ∧
        Real.log 2 * splitEntropy (releasedOrdinaryData2.betaRegion W t r) =
          ordinary112Nats t W := by
  intro t r
  refine ⟨(released_ordinary_zero_semantics t r).1,
    (released_ordinary_zero_semantics t r).2, ?_⟩
  intro W
  exact ⟨released_ordinary_marginal_evaluator t r W,
    released_ordinary_regional_split_evaluator t r W⟩

end OmegaBound.ADVXXZGeneral
end

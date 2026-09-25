import OmegaBound.ADVXXZGeneralReleasedOrdinaryPair
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsLevel2Semantic

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_library_suggestions Lean.LibrarySuggestions.empty

private theorem evaluator_sum_chunk_two (f : Chunk 2 → ℝ) :
    (∑ a : Chunk 2, f a) =
      f ![0, 0] + f ![0, 1] + f ![0, 2] + f ![1, 0] + f ![1, 1] +
        f ![1, 2] + f ![2, 0] + f ![2, 1] + f ![2, 2] := by
  rw [show (Finset.univ : Finset (Chunk 2)) =
    {![0, 0], ![0, 1], ![0, 2], ![1, 0], ![1, 1], ![1, 2],
      ![2, 0], ![2, 1], ![2, 2]} by decide +kernel]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_insert (by decide +kernel)]
  rw [Finset.sum_singleton]
  ring

private theorem evaluator_sum_fin_three (f : Fin 3 → ℝ) :
    (∑ a : Fin 3, f a) =
      f 0 + f (Fin.succ 0) + f (Fin.succ (Fin.succ 0)) := by
  simp [Fin.sum_univ_succ]
  ring

private theorem evaluator_probR_zero_of_level_ne (b : SplitDist 2) (k : ℕ)
    (hsupport : Supported b k) (sigma : Chunk 2)
    (hne : chunkLvl sigma ≠ k) : b.probR sigma = 0 := by
  by_contra hp
  apply hne
  apply hsupport sigma
  intro hnum
  apply hp
  simp [RatDist.probR, hnum]

private theorem evaluator_halfMarginal_one (b : SplitDist 2)
    (hsupport : Supported b 1) :
    halfMarginal (w := 1) b = fun a =>
      if a = 0 then b.probR ![0, 1] else
      if a = 1 then b.probR ![1, 0] else 0 := by
  have h00 : b.probR ![0, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h02 : b.probR ![0, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h11 : b.probR ![1, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h12 : b.probR ![1, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h20 : b.probR ![2, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h21 : b.probR ![2, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h22 : b.probR ![2, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  funext a
  fin_cases a <;>
    unfold halfMarginal <;>
    rw [evaluator_sum_chunk_two] <;>
    simp [leftHalf, chunkLvl, Fin.sum_univ_two, h00, h02, h11, h12, h20, h21, h22]

private theorem evaluator_halfMarginal_two (b : SplitDist 2)
    (hsupport : Supported b 2) :
    halfMarginal (w := 1) b = fun a =>
      if a = 0 then b.probR ![0, 2] else
      if a = 1 then b.probR ![1, 1] else b.probR ![2, 0] := by
  have h00 : b.probR ![0, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h01 : b.probR ![0, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h10 : b.probR ![1, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h12 : b.probR ![1, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h21 : b.probR ![2, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h22 : b.probR ![2, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  funext a
  fin_cases a <;>
    unfold halfMarginal <;>
    rw [evaluator_sum_chunk_two] <;>
    simp [leftHalf, chunkLvl, Fin.sum_univ_two, h00, h01, h10, h12, h21, h22]

private theorem evaluator_splitEntropy_eq_halfMarginal_one (b : SplitDist 2)
    (hsupport : Supported b 1) :
    splitEntropy b = entropy (halfMarginal (w := 1) b) := by
  have hm := evaluator_halfMarginal_one b hsupport
  have h00 : b.probR ![0, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h02 : b.probR ![0, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h11 : b.probR ![1, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h12 : b.probR ![1, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h20 : b.probR ![2, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h21 : b.probR ![2, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  have h22 : b.probR ![2, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 1 hsupport _ (by decide +kernel)
  unfold splitEntropy entropy Entropy.H₂ Entropy.H
  rw [evaluator_sum_chunk_two, evaluator_sum_fin_three, hm]
  simp [h00, h02, h11, h12, h20, h21, h22, Real.negMulLog_zero]

private theorem evaluator_splitEntropy_eq_halfMarginal_two (b : SplitDist 2)
    (hsupport : Supported b 2) :
    splitEntropy b = entropy (halfMarginal (w := 1) b) := by
  have hm := evaluator_halfMarginal_two b hsupport
  have h00 : b.probR ![0, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h01 : b.probR ![0, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h10 : b.probR ![1, 0] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h12 : b.probR ![1, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h21 : b.probR ![2, 1] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  have h22 : b.probR ![2, 2] = 0 :=
    evaluator_probR_zero_of_level_ne b 2 hsupport _ (by decide +kernel)
  unfold splitEntropy entropy Entropy.H₂ Entropy.H
  rw [evaluator_sum_chunk_two, evaluator_sum_fin_three, hm]
  simp [h00, h01, h10, h12, h21, h22, Real.negMulLog_zero]

private theorem evaluator_ordinary_regional_support
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) (W : Side) :
    Supported (releasedOrdinaryData2.betaRegion W t r)
      (coord W (ordinaryOccurrence t).1.2.2.1) := by
  have hs := ordinary_regional_support W t r
  cases W <;> simpa only [releasedOrdinaryData2, releasedOrdinaryParent] using hs

private theorem evaluator_ordinary_coord (t : Fin (Fintype.card ReleasedOrdinaryOccurrence))
    (W : Side) :
    coord W (ordinaryOccurrence t).1.2.2.1 = 1 ∨
      coord W (ordinaryOccurrence t).1.2.2.1 = 2 := by
  have hx := (ordinaryOccurrence t).2.2.1
  have hy := (ordinaryOccurrence t).2.2.2.1
  have hz := (ordinaryOccurrence t).2.2.2.2
  have hsum := (ordinaryOccurrence t).1.2.2.1.property
  change coord .X (ordinaryOccurrence t).1.2.2.1 +
    coord .Y (ordinaryOccurrence t).1.2.2.1 +
    coord .Z (ordinaryOccurrence t).1.2.2.1 = 4 at hsum
  cases W <;> omega

private theorem evaluator_probR_eq_cast_prob {iota : Type*} [Fintype iota]
    (P : RatDist iota) (a : iota) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem evaluator_sum_pairProb_left_level {w : ℕ} (L R : SplitDist w)
    (a : Fin (2 * w + 1)) :
    (∑ sigma : Chunk (w + w), if chunkLvl (leftHalf sigma) = (a : ℕ)
      then pairProb L R sigma else 0) =
      ∑ x : Chunk w, if chunkLvl x = (a : ℕ) then L.probR x else 0 := by
  classical
  simp only [pairProb]
  rw [show (∑ sigma : Chunk (w + w),
      if chunkLvl (leftHalf sigma) = (a : ℕ) then
        L.probR (leftHalf sigma) * R.probR (rightHalf sigma) else 0) =
      ∑ q : Chunk w × Chunk w,
        if chunkLvl q.1 = (a : ℕ) then L.probR q.1 * R.probR q.2 else 0 by
    exact Equiv.sum_comp (chunkPairEquiv w w)
      (fun q : Chunk w × Chunk w =>
        if chunkLvl q.1 = (a : ℕ) then L.probR q.1 * R.probR q.2 else 0)]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Chunk w, ∑ y : Chunk w,
        if chunkLvl x = (a : ℕ) then L.probR x * R.probR y else 0) =
        ∑ x : Chunk w, if chunkLvl x = (a : ℕ) then
          L.probR x * (∑ y : Chunk w, R.probR y) else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            by_cases hx : chunkLvl x = (a : ℕ)
            · simp only [if_pos hx, Finset.mul_sum]
            · simp [hx]
    _ = ∑ x : Chunk w, if chunkLvl x = (a : ℕ) then L.probR x else 0 := by
      rw [R.sum_probR]
      simp

private theorem evaluator_levelMarginal_of_supported {w : ℕ}
    (L : SplitDist w) (q : ℕ) (hs : Supported L q) (a : Fin (2 * w + 1)) :
    (∑ x : Chunk w, if chunkLvl x = (a : ℕ) then L.probR x else 0) =
      if q = (a : ℕ) then 1 else 0 := by
  classical
  have hsR : ∀ x, L.probR x ≠ 0 → chunkLvl x = q := by
    intro x hx
    apply hs x
    intro hnum
    apply hx
    simp [RatDist.probR, hnum]
  by_cases hqa : q = (a : ℕ)
  · rw [if_pos hqa]
    calc
      (∑ x : Chunk w, if chunkLvl x = (a : ℕ) then L.probR x else 0) =
          ∑ x : Chunk w, L.probR x := by
            refine Finset.sum_congr rfl fun x _ => ?_
            by_cases hx : L.probR x = 0
            · simp [hx]
            · rw [if_pos]
              exact (hsR x hx).trans hqa
      _ = 1 := L.sum_probR
  · rw [if_neg hqa]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hlevel : chunkLvl x = (a : ℕ)
    · rw [if_pos hlevel]
      by_contra hx
      exact hqa ((hsR x hx).symm.trans hlevel)
    · simp [hlevel]

private theorem evaluator_ordinary_marginal_eq_half
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) (W : Side) :
    constituentMarginal releasedOrdinaryData2.toPaper t r W =
      halfMarginal (w := 1) (releasedOrdinaryData2.betaRegion W t r) := by
  classical
  funext a
  have hpair : ∀ sigma,
      (releasedOrdinaryData2.betaRegion W t r).probR sigma =
        ∑ u, (releasedOrdinaryData2.alpha t r).probR u *
          (releasedOrdinaryData2.betaChild W t r u).probR (leftHalf sigma) *
          (releasedOrdinaryData2.betaChild W t r
            (complement releasedOrdinaryParent t u)).probR (rightHalf sigma) := by
    intro sigma
    have hp := congrArg (fun x : ℚ => (x : ℝ)) (ordinary_pair_mixture W t r sigma)
    simpa only [evaluator_probR_eq_cast_prob, Rat.cast_mul, Rat.cast_sum] using hp
  rw [constituentMarginal, halfMarginal]
  symm
  calc
    (∑ sigma : Chunk (1 + 1), if chunkLvl (leftHalf sigma) = (a : ℕ)
        then (releasedOrdinaryData2.betaRegion W t r).probR sigma else 0) =
        ∑ sigma : Chunk (1 + 1), if chunkLvl (leftHalf sigma) = (a : ℕ) then
          ∑ u, (releasedOrdinaryData2.alpha t r).probR u *
            (releasedOrdinaryData2.betaChild W t r u).probR (leftHalf sigma) *
            (releasedOrdinaryData2.betaChild W t r
              (complement releasedOrdinaryParent t u)).probR (rightHalf sigma)
          else 0 := by
            refine Finset.sum_congr rfl fun sigma _ => ?_
            rw [hpair sigma]
    _ = ∑ sigma : Chunk (1 + 1), ∑ u,
          if chunkLvl (leftHalf sigma) = (a : ℕ) then
            (releasedOrdinaryData2.alpha t r).probR u *
              pairProb (releasedOrdinaryData2.betaChild W t r u)
                (releasedOrdinaryData2.betaChild W t r
                  (complement releasedOrdinaryParent t u)) sigma
          else 0 := by
            refine Finset.sum_congr rfl fun sigma _ => ?_
            by_cases hsigma : chunkLvl (leftHalf sigma) = (a : ℕ) <;>
              simp [hsigma, pairProb, mul_assoc]
    _ = ∑ u, ∑ sigma : Chunk (1 + 1),
          if chunkLvl (leftHalf sigma) = (a : ℕ) then
            (releasedOrdinaryData2.alpha t r).probR u *
              pairProb (releasedOrdinaryData2.betaChild W t r u)
                (releasedOrdinaryData2.betaChild W t r
                  (complement releasedOrdinaryParent t u)) sigma
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ u, (releasedOrdinaryData2.alpha t r).probR u *
          (∑ sigma : Chunk (1 + 1), if chunkLvl (leftHalf sigma) = (a : ℕ) then
            pairProb (releasedOrdinaryData2.betaChild W t r u)
              (releasedOrdinaryData2.betaChild W t r
                (complement releasedOrdinaryParent t u)) sigma else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun sigma _ => ?_
            by_cases hsigma : chunkLvl (leftHalf sigma) = (a : ℕ) <;> simp [hsigma]
    _ = ∑ u, (releasedOrdinaryData2.alpha t r).probR u *
          (∑ x : Chunk 1, if chunkLvl x = (a : ℕ) then
            (releasedOrdinaryData2.betaChild W t r u).probR x else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [evaluator_sum_pairProb_left_level]
    _ = ∑ u, (releasedOrdinaryData2.alpha t r).probR u *
          (if coord W u.1 = (a : ℕ) then 1 else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [evaluator_levelMarginal_of_supported _ _ (ordinary_child_support W t r u)]
    _ = ∑ u, if coord W u.1 = (a : ℕ) then
          (releasedOrdinaryData2.alpha t r).probR u else 0 := by
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : coord W u.1 = (a : ℕ) <;> simp [hu]

theorem released_ordinary_regional_split_evaluator
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) (W : Side) :
    Real.log 2 * splitEntropy (releasedOrdinaryData2.betaRegion W t r) =
      ordinary112Nats t W := by
  have hs := evaluator_ordinary_regional_support t r W
  have hm := evaluator_ordinary_marginal_eq_half t r W
  rcases evaluator_ordinary_coord t W with hcoord | hcoord
  · have he := evaluator_splitEntropy_eq_halfMarginal_one
      (releasedOrdinaryData2.betaRegion W t r) (by simpa only [hcoord] using hs)
    rw [he, ← hm]
    exact released_ordinary_marginal_evaluator t r W
  · have he := evaluator_splitEntropy_eq_halfMarginal_two
      (releasedOrdinaryData2.betaRegion W t r) (by simpa only [hcoord] using hs)
    rw [he, ← hm]
    exact released_ordinary_marginal_evaluator t r W

end OmegaBound.ADVXXZGeneral
end

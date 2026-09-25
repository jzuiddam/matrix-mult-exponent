import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorRetainedSum

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

private theorem mul_min_nonneg32 (c a b : ℝ) (hc : 0 ≤ c) :
    c * min a b = min (c * a) (c * b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hc)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hc)]

private theorem min_div_nonneg32 (a b c : ℝ) (hc : 0 ≤ c) :
    min a b / c = min (a / c) (b / c) := by
  simp only [div_eq_mul_inv]
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc))]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc))]

private theorem log2_nonneg32 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)

/-- The released ordinary region law is the point mass at region `0`. -/
theorem ordinary_A_eq32 (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) :
    releasedOrdinaryData2.toPaper.A t r = if r = 0 then 1 else 0 := by
  simp only [ConstituentSpec.toPaper, releasedOrdinaryData2, ordinaryRegionDist,
    RatDist.probR]
  split_ifs with h <;> norm_num

theorem ordinary_rowX_total32 (V : Side) :
    Real.log 2 * constituentRowX releasedOrdinaryData2.toPaper 0 V
      = ordinaryDirectionalTotal V := by
  unfold constituentRowX ordinaryDirectionalTotal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ordinary_A_eq32 t 0, if_pos rfl, (released_ordinary_level2_semantics t 0).1,
    sub_zero, one_mul, ← ((released_ordinary_level2_semantics t 0).2.2 V).1]
  ring

theorem ordinary_rowY_total32 (U V Z' : Side) :
    Real.log 2 * constituentRowY releasedOrdinaryData2.toPaper 0 U V Z'
      = ordinaryDirectionalTotal V := by
  unfold constituentRowY ordinaryDirectionalTotal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ordinary_A_eq32 t 0, if_pos rfl,
    ((released_ordinary_level2_semantics t 0).2.1 U V Z').1,
    sub_zero, one_mul,
    show releasedOrdinaryData2.toPaper.betaRegion V t 0
      = releasedOrdinaryData2.betaRegion V t 0 from rfl,
    ← ((released_ordinary_level2_semantics t 0).2.2 V).2]
  ring

theorem ordinary_rowZ_total32 (U V Z' : Side) :
    Real.log 2 * constituentRowZ releasedOrdinaryData2.toPaper 0 U V Z'
      = ordinaryDirectionalTotal Z' := by
  unfold constituentRowZ ordinaryDirectionalTotal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ordinary_A_eq32 t 0, if_pos rfl,
    ((released_ordinary_level2_semantics t 0).2.1 U V Z').2,
    sub_zero, one_mul,
    show releasedOrdinaryData2.toPaper.betaRegion Z' t 0
      = releasedOrdinaryData2.betaRegion Z' t 0 from rfl,
    ← ((released_ordinary_level2_semantics t 0).2.2 Z').2]
  ring

/-- Regions other than `0` carry no ordinary mass. -/
theorem ordinary_region_rate_zero32 (r : Fin 6) (hr : r ≠ 0) :
    constituentRegionRate releasedOrdinaryData2.toPaper r = 0 := by
  have hX : ∀ V, constituentRowX releasedOrdinaryData2.toPaper r V = 0 := by
    intro V
    unfold constituentRowX
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rw [ordinary_A_eq32 t r, if_neg hr]
    ring
  have hY : ∀ U V Z', constituentRowY releasedOrdinaryData2.toPaper r U V Z' = 0 := by
    intro U V Z'
    unfold constituentRowY
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rw [ordinary_A_eq32 t r, if_neg hr]
    ring
  have hZ : ∀ U V Z', constituentRowZ releasedOrdinaryData2.toPaper r U V Z' = 0 := by
    intro U V Z'
    unfold constituentRowZ
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rw [ordinary_A_eq32 t r, if_neg hr]
    ring
  simp only [constituentRegionRate, hX, hY, hZ, min_self]

/-- The only surviving region is `0`, whose permutation is the identity, so the
regional rate is the three-way minimum taken **after** the complete directional sums. -/
theorem ordinary_region_rate_at_zero32 :
    Real.log 2 * constituentRegionRate releasedOrdinaryData2.toPaper 0 =
      min (ordinaryDirectionalTotal .X)
        (min (ordinaryDirectionalTotal .Y) (ordinaryDirectionalTotal .Z)) := by
  have hrr : constituentRegionRate releasedOrdinaryData2.toPaper 0 =
      min (constituentRowX releasedOrdinaryData2.toPaper 0 .X)
        (min (constituentRowY releasedOrdinaryData2.toPaper 0 .X .Y .Z)
          (constituentRowZ releasedOrdinaryData2.toPaper 0 .X .Y .Z)) := rfl
  rw [hrr, mul_min_nonneg32 _ _ _ log2_nonneg32,
    mul_min_nonneg32 _ _ _ log2_nonneg32,
    ordinary_rowX_total32, ordinary_rowY_total32, ordinary_rowZ_total32]

theorem ordinary_base_total_ne_zero32 :
    (constituentBaseTotal releasedOrdinaryParent : ℝ) ≠ 0 := by
  haveI : Nonempty (Fin (Fintype.card ReleasedOrdinaryOccurrence)) :=
    ⟨⟨0, Fintype.card_pos⟩⟩
  have hpos : 0 < constituentBaseTotal releasedOrdinaryParent :=
    Finset.sum_pos (fun t _ => releasedOrdinaryParent.baseN_pos t) Finset.univ_nonempty
  exact Nat.cast_ne_zero.2 hpos.ne'

/-- The normalised constituent rate of the
released ordinary level-two stage is the released level-two symmetric rate. -/
theorem released_ordinary_symmetric_rate32 :
    cRate releasedOrdinaryData2 * (constituentBaseTotal releasedOrdinaryParent : ℝ) /
        (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 2 =
      OmegaBound.ADVXXZLevel2Closure.symmetricRate
        OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms := by
  have hD : (releasedOrdinaryCertificatePhysical.D : ℝ) ^ 2 = (ordinaryD : ℝ) ^ 4 := by
    show ((ordinaryD ^ 2 : ℕ) : ℝ) ^ 2 = (ordinaryD : ℝ) ^ 4
    push_cast
    ring
  have hsum : ∑ r, constituentRegionRate releasedOrdinaryData2.toPaper r
      = constituentRegionRate releasedOrdinaryData2.toPaper 0 := by
    rw [Fin.sum_univ_six,
      ordinary_region_rate_zero32 1 (by decide +kernel),
      ordinary_region_rate_zero32 2 (by decide +kernel),
      ordinary_region_rate_zero32 3 (by decide +kernel),
      ordinary_region_rate_zero32 4 (by decide +kernel),
      ordinary_region_rate_zero32 5 (by decide +kernel)]
    ring
  have h0 : OmegaBound.ADVXXZLevel2Closure.retainedRow
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms 0 =
      ordinaryDirectionalTotal .X / (ordinaryD : ℝ) ^ 4 :=
    released_retained_row_census32 .X
  have h1 : OmegaBound.ADVXXZLevel2Closure.retainedRow
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms 1 =
      ordinaryDirectionalTotal .Y / (ordinaryD : ℝ) ^ 4 :=
    released_retained_row_census32 .Y
  have h2 : OmegaBound.ADVXXZLevel2Closure.retainedRow
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms 2 =
      ordinaryDirectionalTotal .Z / (ordinaryD : ℝ) ^ 4 :=
    released_retained_row_census32 .Z
  have hDpos : (0:ℝ) ≤ (ordinaryD : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg _) 4
  unfold cRate OmegaBound.ADVXXZLevel2Closure.symmetricRate
  rw [div_mul_cancel₀ _ ordinary_base_total_ne_zero32, hsum, hD, h0, h1, h2,
    ordinary_region_rate_at_zero32, min_div_nonneg32 _ _ _ hDpos,
    min_div_nonneg32 _ _ _ hDpos]

end OmegaBound.ADVXXZGeneral
end

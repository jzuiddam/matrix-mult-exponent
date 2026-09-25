import OmegaBound.ADVXXZGeneralGridInput29TwinInputStageMoments

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

/-- One oriented cell's paired-chunk statistic on the nested type-class product.
Self-complementary cells use the corrected one-word involution statistic. -/
noncomputable def inputProductCellCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (x : (t : Fin s) → (u : ChildShape p t) →
      Words (Nat.card (InputStageCellPos p d r j t u))
        (stageCounts27 m p d r W t u))
    (t : Fin s) (u : ChildShape p t) (sigma tau : Chunk w) : ℕ :=
  if hu : complement p t u = u then
    selfPairCount (inputStageFirstPositions p d r j t u)
      (inputStageSelfPairPerm p d r j t u hu) sigma tau (x t u).val
  else
    restrictedPairCount (inputStageFirstPositions p d r j t u)
      (Equiv.refl _) sigma tau
      ((x t u).val,
        (inputStageComplementWord p d r j W t u
          (x t (complement p t u))).val)

/-- The exact corrected centre used for one oriented cell. -/
noncomputable def inputProductCellMean {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma tau : Chunk w) : ℝ :=
  if complement p t u = u then
    ((inputStageFirstPositions p d r j t u).card : ℝ) *
      (stageCounts27 m p d r W t u sigma : ℝ) *
      ((stageCounts27 m p d r W t u tau : ℝ) -
        if sigma = tau then 1 else 0) /
      ((Nat.card (InputStageCellPos p d r j t u) : ℝ) *
        ((Nat.card (InputStageCellPos p d r j t u) : ℝ)-1))
  else
    ((inputStageFirstPositions p d r j t u).card : ℝ) *
      (stageCounts27 m p d r W t u sigma : ℝ) *
      (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
      (Nat.card (InputStageCellPos p d r j t u) : ℝ)^2

/-- The product-frequency centre to which every cell is transported. -/
noncomputable def inputProductCellTarget {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma tau : Chunk w) : ℝ :=
  ((inputStageFirstPositions p d r j t u).card : ℝ) *
    (stageCounts27 m p d r W t u sigma : ℝ) *
    (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
    (Nat.card (InputStageCellPos p d r j t u) : ℝ)^2

private theorem inputCellMoment_swapIndex_position {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label)
    (t : Fin s) (u : ChildShape p t)
    (q : Fin (Nat.card (InputStageCellPos p d r j t u))) :
    ((Finite.equivFin
      (InputStageCellPos p d r j t (complement p t u))).symm
        (inputStageCellSwapIndex p d r j t u q)).val =
      (inputStageCellSwap p d r j t u
        ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q)).val := by
  unfold inputStageCellSwapIndex
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

private theorem inputCellMoment_distinct_pointwise {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (sigma tau : Chunk w) :
    restrictedPairCount (inputStageFirstPositions p d r j t u)
        (Equiv.refl _) sigma tau
        ((inputExactPartFibreEquiv p d hd r j W a t u).val,
          (inputStageComplementWord p d r j W t u
            (inputExactPartFibreEquiv p d hd r j W a t
              (complement p t u))).val) =
      inputStageSelfPhysicalCount p d r j W a t u sigma tau := by
  unfold restrictedPairCount inputStageComplementWord
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter, Equiv.refl_apply]
  change q ∈ inputStageFirstPositions p d r j t u ∧
      (inputExactPartFibreEquiv p d hd r j W a t u).val q = sigma ∧
        (inputExactPartFibreEquiv p d hd r j W a t
          (complement p t u)).val
            (inputStageCellSwapIndex p d r j t u q) = tau ↔
    q ∈ inputStageFirstPositions p d r j t u ∧
      a.val ⟨t, ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q).val⟩ = sigma ∧
        a.val ⟨t, (inputStageCellSwap p d r j t u
          ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q)).val⟩ = tau
  rw [inputExactPartFibreEquiv_apply]
  rw [inputExactPartFibreEquiv_apply]
  rw [inputCellMoment_swapIndex_position p d r j t u]

/-- The product statistic transported from an exact part is pointwise the actual
physical half-pair count, in both self and distinct complementary cells. -/
theorem inputProductCellCount_on_exact {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (sigma tau : Chunk w) :
    inputProductCellCount p d r j W
        (inputExactPartFibreEquiv p d hd r j W a) t u sigma tau =
      inputStageSelfPhysicalCount p d r j W a t u sigma tau := by
  unfold inputProductCellCount
  split_ifs with hu
  · exact inputExactPartFibre_selfPairCount p d hd r j W a t u hu sigma tau
  · exact inputCellMoment_distinct_pointwise p d hd r j W a t u sigma tau

private theorem inputCellMoment_count_le_card {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma : Chunk w) :
    stageCounts27 m p d r W t u sigma ≤
      Nat.card (InputStageCellPos p d r J.val t u) := by
  calc
    stageCounts27 m p d r W t u sigma ≤
        ∑ tau, stageCounts27 m p d r W t u tau := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ sigma)
    _ = _ := inputStageCellCounts_sum p d hd hb r J W t u

private theorem inputCellMoment_firstPositions_empty {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (J : AlphaLabel p d b m r) (t : Fin s) (u : ChildShape p t)
    (hzero : Nat.card (InputStageCellPos p d r J.val t u) = 0) :
    inputStageFirstPositions p d r J.val t u = ∅ := by
  apply Finset.card_eq_zero.mp
  have hle := (inputStageFirstPositions p d r J.val t u).card_le_univ
  simp only [Fintype.card_fin, hzero] at hle
  omega

set_option maxHeartbeats 1000000 in
/-- A zero-sized physical cell has identical corrected and product centres. -/
theorem inputProductCellMean_eq_target_of_card_zero {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t)
    (hzero : Nat.card (InputStageCellPos p d r J.val t u) = 0)
    (sigma tau : Chunk w) :
    inputProductCellMean (b := b) (m := m) p d r J.val W t u sigma tau =
      inputProductCellTarget (b := b) (m := m) p d r J.val W t u sigma tau := by
  have hfirst := inputCellMoment_firstPositions_empty p d r J t u hzero
  unfold inputProductCellMean inputProductCellTarget
  rw [hfirst]
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div]
  split_ifs <;> rfl

/-- The corrected local centre differs from the product-frequency centre by at
most two once the occupied cell has at least two positions. -/
theorem inputProductCellMean_sub_target_abs_le_two {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t)
    (hn : 2 ≤ Nat.card (InputStageCellPos p d r J.val t u))
    (sigma tau : Chunk w) :
    |inputProductCellMean p d r J.val W t u sigma tau -
      inputProductCellTarget p d r J.val W t u sigma tau| ≤ 2 := by
  unfold inputProductCellMean inputProductCellTarget
  by_cases hu : complement p t u = u
  · simp only [if_pos hu]
    rw [hu]
    exact selfPairMean_sub_product_abs_le_two
      (Nat.card (InputStageCellPos p d r J.val t u)) hn
      (inputStageFirstPositions p d r J.val t u)
      (stageCounts27 m p d r W t u) sigma tau
      (inputCellMoment_count_le_card p d hd hb r J W t u sigma)
      (inputCellMoment_count_le_card p d hd hb r J W t u tau)
  · simp only [if_neg hu, sub_self, abs_zero]
    norm_num

/-- The local centre correction is uniformly bounded for all cells once the
global multiplier is at least two; zero cells have no correction. -/
theorem inputProductCellMean_sub_target_abs_le_two_all {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (hm : 2 ≤ m) (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) (sigma tau : Chunk w) :
    |inputProductCellMean p d r J.val W t u sigma tau -
      inputProductCellTarget p d r J.val W t u sigma tau| ≤ 2 := by
  by_cases hzero : Nat.card (InputStageCellPos p d r J.val t u) = 0
  · rw [inputProductCellMean_eq_target_of_card_zero p d r J W t u hzero]
    norm_num
  · have hNform := inputStageCell_card p d hd hb r J W t u
    have hout : 0 < d.outBase ⟨t,r,u⟩ := by
      apply Nat.pos_of_ne_zero
      intro hout
      apply hzero
      rw [hNform, hout]
      simp
    apply inputProductCellMean_sub_target_abs_le_two p d hd hb r J W t u
    calc
      2 ≤ m := hm
      _ = m*1 := by omega
      _ ≤ m * d.outBase ⟨t,r,u⟩ := Nat.mul_le_mul_left m hout
      _ = _ := hNform.symm

set_option maxHeartbeats 2000000 in
/-- One constant controls the corrected moment of every oriented physical cell
under every abstract conditioning-fibre equivalence. -/
theorem inputConditionedCell_fourth_moment {w : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {s b m : ℕ}
      (p : ConstituentInput w s) (d : ConstituentSpec p)
      (hd : InputAdm29 d b) (hb : InputInt29 d b m)
      (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
      (Ω : Type*) [Fintype Ω] (hΩ : Nonempty Ω)
      (e : Ω ≃ ((t : Fin s) → (u : ChildShape p t) →
        Words (Nat.card (InputStageCellPos p d r J.val t u))
          (stageCounts27 m p d r W t u)))
      (t : Fin s) (u : ChildShape p t)
      (sigma tau : Chunk w),
      avg (fun x : Ω =>
        ((inputProductCellCount p d r J.val W (e x) t u sigma tau : ℝ) -
          inputProductCellMean p d r J.val W t u sigma tau)^4) ≤
        C * (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 := by
  obtain ⟨C,hC,hDistinct⟩ :=
    (inputConditionedDistinctCell_fourth_moment (w := w))
  let Cself : ℝ := 2479446 * 8^14
  refine ⟨Cself+C, by dsimp [Cself]; positivity, ?_⟩
  intro s b m p d hd hb r J W Ω _ hΩ e t u sigma tau
  by_cases hzero : Nat.card (InputStageCellPos p d r J.val t u) = 0
  · have hfirst := inputCellMoment_firstPositions_empty p d r J t u hzero
    have hcount : ∀ x : Ω,
        inputProductCellCount p d r J.val W (e x) t u sigma tau = 0 := by
      intro x
      unfold inputProductCellCount
      by_cases hu : complement p t u = u
      · simp only [dif_pos hu]
        unfold selfPairCount
        rw [hfirst]
        simp only [Finset.filter_empty, Finset.card_empty]
      · simp only [dif_neg hu]
        unfold restrictedPairCount
        rw [hfirst]
        simp only [Finset.filter_empty, Finset.card_empty]
    have hmean : inputProductCellMean p d r J.val W t u sigma tau = 0 := by
      unfold inputProductCellMean
      rw [hfirst]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div]
      split_ifs <;> rfl
    rw [hzero]
    simp only [Nat.cast_zero, zero_pow, mul_zero]
    have hfun : (fun x : Ω =>
        ((inputProductCellCount p d r J.val W (e x) t u sigma tau : ℝ) -
          inputProductCellMean p d r J.val W t u sigma tau)^4) =
        fun _ => (0 : ℝ) := by
      funext x
      rw [hcount x,hmean]
      norm_num
    rw [hfun]
    unfold avg
    simp
  · have hn : 0 < Nat.card (InputStageCellPos p d r J.val t u) :=
      Nat.pos_of_ne_zero hzero
    by_cases hu : complement p t u = u
    · simp only [inputProductCellCount, dif_pos hu,
        inputProductCellMean, if_pos hu]
      have hs := inputConditionedSelfCell_fourth_moment p d hd hb r J W Ω hΩ e
        t u hu hn sigma tau
      exact hs.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hC.le) (sq_nonneg _))
    · simp only [inputProductCellCount, dif_neg hu,
        inputProductCellMean, if_neg hu]
      have hs := hDistinct p d hd hb r J W Ω hΩ e t u (Ne.symm hu)
        hn sigma tau
      exact hs.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by dsimp [Cself]; positivity)) (sq_nonneg _))

end
end OmegaBound.ADVXXZGeneral.Grid29
end


import OmegaBound.ADVXXZGeneralGridInput29TwinInputFibreTransport

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

private def inputHalfSwap : Equiv.Perm (Fin 2) where
  toFun h := if h = 0 then 1 else 0
  invFun h := if h = 0 then 1 else 0
  left_inv h := by fin_cases h <;> rfl
  right_inv h := by fin_cases h <;> rfl

private theorem inputStageColour_one {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    stageColour27 0 b m p d r j t (i, 1) =
      complement p t (stageColour27 0 b m p d r j t (i, 0)) := by
  exact j.property.2 t i

private theorem inputStageColour_zero {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) :
    stageColour27 0 b m p d r j t (i, 0) =
      complement p t (stageColour27 0 b m p d r j t (i, 1)) := by
  rw [inputStageColour_one p d r j t i, complement_complement]

private theorem inputStageColour_swap {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (i : Fin (StageCandidateRaw.stageParentCount b m p d r t)) (h : Fin 2) :
    stageColour27 0 b m p d r j t (i, inputHalfSwap h) =
      complement p t (stageColour27 0 b m p d r j t (i, h)) := by
  fin_cases h
  · exact inputStageColour_one p d r j t i
  · exact inputStageColour_zero p d r j t i

/-- Swapping the two physical halves sends the cell of `u` to the cell of its
complement.  This is the actual pairing geometry used by `Parent25.paired`. -/
def inputStageCellSwap {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    InputStageCellPos p d r j t u ≃
      InputStageCellPos p d r j t (complement p t u) :=
  Equiv.subtypeEquiv (Equiv.prodCongr (Equiv.refl _) inputHalfSwap) fun z => by
    change stageColour27 0 b m p d r j t z = u ↔
      stageColour27 0 b m p d r j t (z.1, inputHalfSwap z.2) = complement p t u
    rw [inputStageColour_swap p d r j t z.1 z.2]
    constructor
    · exact fun h => congrArg (complement p t) h
    · intro h
      have hc := congrArg (complement p t) h
      simpa only [complement_complement] using hc

/-- The same physical half swap in the canonical numbering of the two cells. -/
noncomputable def inputStageCellSwapIndex {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    Fin (Nat.card (InputStageCellPos p d r j t u)) ≃
      Fin (Nat.card (InputStageCellPos p d r j t (complement p t u))) :=
  (Finite.equivFin (InputStageCellPos p d r j t u)).symm |>.trans
    ((inputStageCellSwap p d r j t u).trans
      (Finite.equivFin (InputStageCellPos p d r j t (complement p t u))))

/-- Coordinates in a cell that come from the first physical half. -/
noncomputable def inputStageFirstPositions {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) :
    Finset (Fin (Nat.card (InputStageCellPos p d r j t u))) :=
  Finset.univ.filter fun q =>
    ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q).val.2 = 0

/-- In a self-complementary cell the physical swap is a permutation of the
single cell word. -/
noncomputable def inputStageSelfPairPerm {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (hu : complement p t u = u) :
    Equiv.Perm (Fin (Nat.card (InputStageCellPos p d r j t u))) :=
  (Finite.equivFin (InputStageCellPos p d r j t u)).symm |>.trans
    ((inputStageCellSwap p d r j t u).trans
      ((Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by rw [hu]; rfl)).trans
        (Finite.equivFin (InputStageCellPos p d r j t u))))

/-- First-half coordinates and their partners are disjoint in a self-complementary
physical cell. -/
theorem inputStageSelfPair_oriented {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p) (r : Fin 6)
    (j : (stagePopulationAt 0 p d b m r).Label) (t : Fin s)
    (u : ChildShape p t) (hu : complement p t u = u) :
    ∀ i ∈ inputStageFirstPositions p d r j t u,
      inputStageSelfPairPerm p d r j t u hu i ∉
        inputStageFirstPositions p d r j t u := by
  intro i hi
  simp only [inputStageFirstPositions, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  unfold inputStageSelfPairPerm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  let z := (Finite.equivFin (InputStageCellPos p d r j t u)).symm i
  have hz : z.val.2 = 0 := hi
  change inputHalfSwap z.val.2 ≠ 0
  rw [hz]
  decide +kernel

set_option maxHeartbeats 1000000 in
-- The dependent stage-label specialization requires additional reduction.
/-- The chunk counts of one physical child cell sum to the cardinality of that cell. -/
theorem inputStageCellCounts_sum {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) :
    ∑ sigma, stageCounts27 m p d r W t u sigma =
      Nat.card (InputStageCellPos p d r J.val t u) := by
  let a : StageExactPart27 0 b m p d r J.val W :=
    Classical.choice (stageExactPart_nonempty27 0 m p d hd hb r J.val J.property W)
  let x := inputExactPartFibreEquiv p d hd r J.val W a t u
  calc
    ∑ sigma, stageCounts27 m p d r W t u sigma =
        ∑ sigma, typeCnt x.val sigma := by
          apply Finset.sum_congr rfl
          intro sigma _
          exact (x.property sigma).symm
    _ = Nat.card (InputStageCellPos p d r J.val t u) := sum_typeCnt x.val

/-- The corrected self-pair fourth moment (`selfPairCount_fourth_moment`), instantiated on one occupied
physical child cell. -/
theorem inputStageSelfCell_fourth_moment {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t) (hu : complement p t u = u)
    (hn : 0 < Nat.card (InputStageCellPos p d r J.val t u))
    (sigma tau : Chunk w) :
    avg (fun x : Words (Nat.card (InputStageCellPos p d r J.val t u))
        (stageCounts27 m p d r W t u) =>
      ((selfPairCount (inputStageFirstPositions p d r J.val t u)
          (inputStageSelfPairPerm p d r J.val t u hu) sigma tau x.val : ℝ) -
        ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
          (stageCounts27 m p d r W t u sigma : ℝ) *
          ((stageCounts27 m p d r W t u tau : ℝ) -
            if sigma = tau then 1 else 0) /
          ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ) *
            ((Nat.card (InputStageCellPos p d r J.val t u) : ℝ) - 1)))^4) ≤
      (2479446 * 8^14 : ℝ) *
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 := by
  obtain ⟨_C, _hC, hmoment⟩ :=
    (selfPairCount_fourth_moment (α := Chunk w))
  exact hmoment _ hn _ _
    (inputStageSelfPair_oriented p d r J.val t u hu)
    _ (inputStageCellCounts_sum p d hd hb r J W t u) sigma tau

private theorem input_typeCnt_reindex {α : Type*} [Fintype α] [DecidableEq α]
    {n k : ℕ} (e : Fin n ≃ Fin k) (x : Fin k → α) (a : α) :
    typeCnt (fun i => x (e i)) a = typeCnt x a := by
  unfold typeCnt
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [e.apply_symm_apply]
    exact hj

private def inputWordsReindexEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {n k : ℕ} (e : Fin n ≃ Fin k) (counts : α → ℕ) :
    Words k counts ≃ Words n counts where
  toFun x := ⟨fun i => x.val (e i), fun a =>
    (input_typeCnt_reindex e x.val a).trans (x.property a)⟩
  invFun x := ⟨fun i => x.val (e.symm i), fun a =>
    (input_typeCnt_reindex e.symm x.val a).trans (x.property a)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

private theorem input_avg_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The restricted independent-matching moment, instantiated on the two
distinct physical cells paired by the half swap.  The complement word is reindexed
through the actual physical swap before applying the theorem. -/
theorem inputStageDistinctCell_fourth_moment {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b) (hb : InputInt29 d b m)
    (r : Fin 6) (J : AlphaLabel p d b m r) (W : Side)
    (t : Fin s) (u : ChildShape p t)
    (hn : 0 < Nat.card (InputStageCellPos p d r J.val t u))
    (sigma tau : Chunk w) :
    ∃ C : ℝ, 0 < C ∧
      avg (fun z :
          Words (Nat.card (InputStageCellPos p d r J.val t u))
              (stageCounts27 m p d r W t u) ×
            Words (Nat.card (InputStageCellPos p d r J.val t (complement p t u)))
              (stageCounts27 m p d r W t (complement p t u)) =>
        let y := inputWordsReindexEquiv
          (inputStageCellSwapIndex p d r J.val t u)
          (stageCounts27 m p d r W t (complement p t u)) z.2
        ((restrictedPairCount (inputStageFirstPositions p d r J.val t u)
            (Equiv.refl _) sigma tau (z.1.val, y.val) : ℝ) -
          ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
            (stageCounts27 m p d r W t u sigma : ℝ) *
            (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
            (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2)^4) ≤
        C * (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2 := by
  obtain ⟨C, hC, hmoment⟩ :=
    (restricted_matching_fourth_moment (α := Chunk w) (β := Chunk w))
  refine ⟨C, hC, ?_⟩
  let E := Equiv.prodCongr
    (Equiv.refl (Words (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)))
    (inputWordsReindexEquiv
      (inputStageCellSwapIndex p d r J.val t u)
      (stageCounts27 m p d r W t (complement p t u)))
  let f : PairWords (Nat.card (InputStageCellPos p d r J.val t u))
      (stageCounts27 m p d r W t u)
      (stageCounts27 m p d r W t (complement p t u)) → ℝ := fun z =>
    ((restrictedPairCount (inputStageFirstPositions p d r J.val t u)
        (Equiv.refl _) sigma tau (z.1.val, z.2.val) : ℝ) -
      ((inputStageFirstPositions p d r J.val t u).card : ℝ) *
        (stageCounts27 m p d r W t u sigma : ℝ) *
        (stageCounts27 m p d r W t (complement p t u) tau : ℝ) /
        (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2)^4
  change avg (fun z => f (E z)) ≤
    C * (Nat.card (InputStageCellPos p d r J.val t u) : ℝ)^2
  rw [input_avg_equiv E f]
  apply hmoment _ hn _ _
  · exact inputStageCellCounts_sum p d hd hb r J W t u
  · have hsum := inputStageCellCounts_sum p d hd hb r J W t (complement p t u)
    exact hsum.trans (Nat.card_congr (inputStageCellSwap p d r J.val t u).symm)

private theorem input_distinctMeanCorrection_real (N S A B : ℝ)
    (hN : 2 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ B) (hBN : B ≤ N) :
    |S*A*B/(N*(N-1)) - S*A*B/N^2| ≤ 2 := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNm : 0 < N-1 := by linarith
  have hden : 0 < N^2*(N-1) := mul_pos (sq_pos_of_pos hN0) hNm
  have hform : S*A*B/(N*(N-1)) - S*A*B/N^2 =
      S*A*B/(N^2*(N-1)) := by
    field_simp
    ring
  rw [hform, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hden).2
  have hprod : S*A*B ≤ N^3 := by
    calc
      S*A*B ≤ N*A*B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSN hA0) hB0
      _ ≤ N*N*B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAN hN0.le) hB0
      _ ≤ N*N*N := mul_le_mul_of_nonneg_left hBN (mul_nonneg hN0.le hN0.le)
      _ = N^3 := by ring
  have hcube : N^3 ≤ 2*(N^2*(N-1)) := by nlinarith [sq_nonneg N]
  exact hprod.trans hcube

private theorem input_sameMeanCorrection_real (N S A : ℝ)
    (hN : 2 ≤ N) (hS0 : 0 ≤ S) (hSN : S ≤ N)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) :
    |S*A*(A-1)/(N*(N-1)) - S*A*A/N^2| ≤ 2 := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNm : 0 < N-1 := by linarith
  have hden : 0 < N^2*(N-1) := mul_pos (sq_pos_of_pos hN0) hNm
  have hform : S*A*(A-1)/(N*(N-1)) - S*A*A/N^2 =
      S*A*(A-N)/(N^2*(N-1)) := by
    field_simp
    ring
  have hnum : S*A*(A-N) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hS0 hA0) (sub_nonpos.mpr hAN)
  rw [hform, abs_div, abs_of_nonpos hnum, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  have hprod : -(S*A*(A-N)) ≤ N^3 := by
    have hNA0 : 0 ≤ N-A := sub_nonneg.mpr hAN
    have hNAN : N-A ≤ N := by linarith
    rw [show -(S*A*(A-N)) = S*A*(N-A) by ring]
    calc
      S*A*(N-A) ≤ N*A*(N-A) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSN hA0) hNA0
      _ ≤ N*N*(N-A) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAN hN0.le) hNA0
      _ ≤ N*N*N := mul_le_mul_of_nonneg_left hNAN (mul_nonneg hN0.le hN0.le)
      _ = N^3 := by ring
  have hcube : N^3 ≤ 2*(N^2*(N-1)) := by nlinarith [sq_nonneg N]
  exact hprod.trans hcube

/-- The corrected self-pair center differs from the product-frequency center by
at most an absolute constant.  This is the `O(1/n)` empirical-frequency correction
that is charged inside the fixed positive input tolerance. -/
theorem selfPairMean_sub_product_abs_le_two {α : Type*} [DecidableEq α]
    (n : ℕ) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (k : α → ℕ) (a b : α)
    (hka : k a ≤ n) (hkb : k b ≤ n) :
    |(S.card : ℝ) * (k a : ℝ) *
          ((k b : ℝ) - if a = b then 1 else 0) /
          ((n : ℝ) * ((n : ℝ)-1)) -
        (S.card : ℝ) * (k a : ℝ) * (k b : ℝ) / (n : ℝ)^2| ≤ 2 := by
  have hSN : S.card ≤ n := by simpa using S.card_le_univ
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    exact input_sameMeanCorrection_real n S.card (k a)
      (by exact_mod_cast hn) (by positivity) (by exact_mod_cast hSN)
      (by positivity) (by exact_mod_cast hka)
  · simp only [if_neg hab, sub_zero]
    exact input_distinctMeanCorrection_real n S.card (k a) (k b)
      (by exact_mod_cast hn) (by positivity) (by exact_mod_cast hSN)
      (by positivity) (by exact_mod_cast hka) (by positivity) (by exact_mod_cast hkb)

/-- The actual physical count in a self-complementary child cell, expressed in
the canonical numbering used by the type-class product. -/
noncomputable def inputStageSelfPhysicalCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (sigma tau : Chunk w) : ℕ :=
  ((inputStageFirstPositions p d r j t u).filter fun q =>
    let z := (Finite.equivFin (InputStageCellPos p d r j t u)).symm q
    a.val ⟨t,z.val⟩ = sigma ∧
      a.val ⟨t,(inputStageCellSwap p d r j t u z).val⟩ = tau).card

private theorem inputStageSelfPairPerm_position {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label)
    (t : Fin s) (u : ChildShape p t) (hu : complement p t u = u)
    (q : Fin (Nat.card (InputStageCellPos p d r j t u))) :
    ((Finite.equivFin (InputStageCellPos p d r j t u)).symm
      (inputStageSelfPairPerm p d r j t u hu q)).val =
        (inputStageCellSwap p d r j t u
          ((Finite.equivFin (InputStageCellPos p d r j t u)).symm q)).val := by
  unfold inputStageSelfPairPerm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Under the event-preserving exact-fibre equivalence, the self-pair statistic is
definitionally the count of the actual paired physical positions. -/
theorem inputExactPartFibre_selfPairCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (hu : complement p t u = u)
    (sigma tau : Chunk w) :
    selfPairCount (inputStageFirstPositions p d r j t u)
        (inputStageSelfPairPerm p d r j t u hu) sigma tau
        (inputExactPartFibreEquiv p d hd r j W a t u).val =
      inputStageSelfPhysicalCount p d r j W a t u sigma tau := by
  unfold selfPairCount inputStageSelfPhysicalCount
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter]
  rw [inputExactPartFibreEquiv_apply]
  rw [inputExactPartFibreEquiv_apply]
  rw [inputStageSelfPairPerm_position p d r j t u hu]

private theorem inputStageCellSwapIndex_position {w s b m : ℕ}
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

/-- Under the exact-fibre equivalence, the restricted count of two complementary
cell coordinates is the actual physical half-pair count.  The second word is
reindexed by the physical half swap, rather than independently rematched. -/
theorem inputExactPartFibre_distinctPairCount {w s b m : ℕ}
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : InputAdm29 d b)
    (r : Fin 6) (j : (stagePopulationAt 0 p d b m r).Label) (W : Side)
    (a : StageExactPart27 0 b m p d r j W) (t : Fin s)
    (u : ChildShape p t) (sigma tau : Chunk w) :
    let x := inputExactPartFibreEquiv p d hd r j W a t u
    let y := inputWordsReindexEquiv
      (inputStageCellSwapIndex p d r j t u)
      (stageCounts27 m p d r W t (complement p t u))
      (inputExactPartFibreEquiv p d hd r j W a t (complement p t u))
    restrictedPairCount (inputStageFirstPositions p d r j t u)
        (Equiv.refl _) sigma tau (x.val, y.val) =
      inputStageSelfPhysicalCount p d r j W a t u sigma tau := by
  dsimp only
  unfold restrictedPairCount inputStageSelfPhysicalCount inputWordsReindexEquiv
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
  rw [inputStageCellSwapIndex_position p d r j t u]

end
end OmegaBound.ADVXXZGeneral.Grid29
end


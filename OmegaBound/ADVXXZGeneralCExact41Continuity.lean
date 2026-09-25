import OmegaBound.ADVXXZGeneralEntropy
import OmegaBound.ADVXXZGeneralPQExponentsParent25
import OmegaBound.ADVXXZGeneralGridInput29Facts
import OmegaBound.ADVXXZConstituentPairing

set_option autoImplicit false

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem c41_probR_eq_cast_prob {ι : Type*} [Fintype ι]
    (P : RatDist ι) (a : ι) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem c41_probR_le_one {ι : Type*} [Fintype ι]
    (P : RatDist ι) (a : ι) : P.probR a ≤ 1 := by
  rw [← P.sum_probR]
  exact Finset.single_le_sum (fun x _ => P.probR_nonneg x) (Finset.mem_univ a)

private theorem constituentGridBeta_close41 {w s b m : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (h : ConstituentFullGrid27 d m ε)
    (hε : 0 ≤ ε) (W : Side) (t : Fin s) (r : Fin 6) (u : ChildShape p t)
    (σ : Chunk w) :
    |(constituentGridBeta27 d m h.val W t r u).probR σ -
      (d.betaChild W t r u).probR σ| ≤ (ε : ℝ) := by
  let i := Fintype.equivFin (ConstituentTerm p) ⟨t, r, u⟩
  by_cases hn : 0 < constituentOutN d.toPaper m i
  · have hrat := h.property i W hn σ
    have hi : constituentIndex (p := p) i = ⟨t, r, u⟩ := by
      exact (Fintype.equivFin (ConstituentTerm p)).symm_apply_apply _
    have hout : constituentOutBeta d.toPaper W i = d.betaChild W t r u := by
      unfold constituentOutBeta
      simp only [ConstituentSpec.toPaper]
      rw [hi]
    have hreal :
        (((|(((h.val.val i W σ).val : ℚ) / constituentOutN d.toPaper m i -
          (d.betaChild W t r u).prob σ)| : ℚ) : ℝ) ≤ (ε : ℝ)) := by
      exact Rat.cast_le.mpr (by simpa only [hout] using hrat)
    rw [c41_probR_eq_cast_prob, c41_probR_eq_cast_prob,
      constituentGridBeta27_prob_pos d m h.val W t r u σ hn]
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hreal
  · unfold constituentGridBeta27
    dsimp only
    rw [dif_neg hn, sub_self, abs_zero]
    exact_mod_cast hε

private theorem c41_product_close {w : ℕ} {ε : ℚ}
    (P₁ P₂ Q₁ Q₂ : SplitDist w)
    (h₁ : ∀ σ, |P₁.probR σ - Q₁.probR σ| ≤ (ε : ℝ))
    (h₂ : ∀ σ, |P₂.probR σ - Q₂.probR σ| ≤ (ε : ℝ))
    (hε : 0 ≤ ε) (σ : Chunk (w + w)) :
    |P₁.probR (leftHalf σ) * P₂.probR (rightHalf σ) -
      Q₁.probR (leftHalf σ) * Q₂.probR (rightHalf σ)| ≤ (2 * ε : ℚ) := by
  let x := leftHalf σ
  let y := rightHalf σ
  have hP₁0 : 0 ≤ P₁.probR x := P₁.probR_nonneg x
  have hQ₂0 : 0 ≤ Q₂.probR y := Q₂.probR_nonneg y
  have hP₁1 : P₁.probR x ≤ 1 := c41_probR_le_one P₁ x
  have hQ₂1 : Q₂.probR y ≤ 1 := c41_probR_le_one Q₂ y
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  calc
    |P₁.probR x * P₂.probR y - Q₁.probR x * Q₂.probR y| =
        |P₁.probR x * (P₂.probR y - Q₂.probR y) +
          (P₁.probR x - Q₁.probR x) * Q₂.probR y| := by ring
    _ ≤ |P₁.probR x * (P₂.probR y - Q₂.probR y)| +
        |(P₁.probR x - Q₁.probR x) * Q₂.probR y| := abs_add_le _ _
    _ = P₁.probR x * |P₂.probR y - Q₂.probR y| +
        |P₁.probR x - Q₁.probR x| * Q₂.probR y := by
      rw [abs_mul, abs_mul, abs_of_nonneg hP₁0, abs_of_nonneg hQ₂0]
    _ ≤ 1 * (ε : ℝ) + (ε : ℝ) * 1 := by
      exact add_le_add
        (mul_le_mul hP₁1 (h₂ y) (abs_nonneg _) (by norm_num))
        (mul_le_mul (h₁ x) hQ₂1 hQ₂0 hεR)
    _ = ((2 * ε : ℚ) : ℝ) := by push_cast; ring

private theorem c41_mixtureDist_probR {A B : Type} [Fintype A] [Fintype B]
    (weights : RatDist A) (P : A → RatDist B) (x : B) :
    (mixtureDist27 weights P).probR x =
      ∑ a, weights.probR a * (P a).probR x := by
  rw [c41_probR_eq_cast_prob, mixtureDist27_prob]
  simp_rw [c41_probR_eq_cast_prob]
  push_cast
  rfl

private theorem constituentGridRegionBeta_close41 {w s b m : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (h : ConstituentFullGrid27 d m ε)
    (hε : 0 ≤ ε) (W : Side) (t : Fin s) (r : Fin 6) (σ : Chunk (w + w)) :
    |(constituentGridRegionBeta27 d m h.val W t r).probR σ -
      (d.betaRegion W t r).probR σ| ≤ (2 * ε : ℚ) := by
  have hgrid : (constituentGridRegionBeta27 d m h.val W t r).probR σ =
      ∑ u, (d.alpha t r).probR u *
        ((constituentGridBeta27 d m h.val W t r u).probR (leftHalf σ) *
          (constituentGridBeta27 d m h.val W t r (complement p t u)).probR
            (rightHalf σ)) := by
    rw [constituentGridRegionBeta27, c41_mixtureDist_probR]
    apply Finset.sum_congr rfl
    intro u _
    rw [c41_probR_eq_cast_prob
      (productSplit27 (constituentGridBeta27 d m h.val W t r u)
        (constituentGridBeta27 d m h.val W t r (complement p t u))) σ,
      productSplit27_prob]
    simp_rw [c41_probR_eq_cast_prob]
    push_cast
    ring
  have horig : (d.betaRegion W t r).probR σ =
      ∑ u, (d.alpha t r).probR u *
        ((d.betaChild W t r u).probR (leftHalf σ) *
          (d.betaChild W t r (complement p t u)).probR (rightHalf σ)) := by
    have hq := hd.pair_mixture W t r σ
    have hr : (((d.betaRegion W t r).prob σ : ℚ) : ℝ) =
        ((∑ u, (d.alpha t r).prob u *
          (d.betaChild W t r u).prob (leftHalf σ) *
          (d.betaChild W t r (complement p t u)).prob (rightHalf σ) : ℚ) : ℝ) :=
      congrArg (fun z : ℚ => (z : ℝ)) hq
    simpa only [c41_probR_eq_cast_prob, Rat.cast_sum, Rat.cast_mul, mul_assoc] using hr
  rw [hgrid, horig, ← Finset.sum_sub_distrib]
  calc
    |∑ u, ((d.alpha t r).probR u *
          ((constituentGridBeta27 d m h.val W t r u).probR (leftHalf σ) *
            (constituentGridBeta27 d m h.val W t r (complement p t u)).probR
              (rightHalf σ)) -
        (d.alpha t r).probR u *
          ((d.betaChild W t r u).probR (leftHalf σ) *
            (d.betaChild W t r (complement p t u)).probR (rightHalf σ)))| ≤
        ∑ u, |(d.alpha t r).probR u *
          ((constituentGridBeta27 d m h.val W t r u).probR (leftHalf σ) *
            (constituentGridBeta27 d m h.val W t r (complement p t u)).probR
              (rightHalf σ)) -
          (d.alpha t r).probR u *
            ((d.betaChild W t r u).probR (leftHalf σ) *
              (d.betaChild W t r (complement p t u)).probR (rightHalf σ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, (d.alpha t r).probR u * ((2 * ε : ℚ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u _
      rw [← mul_sub, abs_mul, abs_of_nonneg ((d.alpha t r).probR_nonneg u)]
      exact mul_le_mul_of_nonneg_left
        (c41_product_close
          (constituentGridBeta27 d m h.val W t r u)
          (constituentGridBeta27 d m h.val W t r (complement p t u))
          (d.betaChild W t r u) (d.betaChild W t r (complement p t u))
          (constituentGridBeta_close41 d hd h hε W t r u)
          (constituentGridBeta_close41 d hd h hε W t r (complement p t u)) hε σ)
        ((d.alpha t r).probR_nonneg u)
    _ = ((2 * ε : ℚ) : ℝ) := by
      rw [← Finset.sum_mul, (d.alpha t r).sum_probR, one_mul]

private noncomputable def c41SelectedMass {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (selected : ι → Prop) [DecidablePred selected] : ℝ :=
  ∑ i, if selected i then a i else 0

private theorem c41SelectedMass_nonneg {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (selected : ι → Prop) [DecidablePred selected] :
    0 ≤ c41SelectedMass a selected := by
  unfold c41SelectedMass
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all

private theorem c41SelectedMass_le_total {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (S : ℝ) (hsum : ∑ i, a i = S)
    (selected : ι → Prop) [DecidablePred selected] :
    c41SelectedMass a selected ≤ S := by
  rw [← hsum]
  unfold c41SelectedMass
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact ha i

private theorem c41WeightedSplit_nonneg {ι : Type*} [Fintype ι]
    {w : ℕ} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ι → SplitDist w) (selected : ι → Prop)
    [DecidablePred selected] (hM : 0 < c41SelectedMass a selected) :
    ∀ σ, 0 ≤ weightedSplit a P selected σ := by
  intro σ
  unfold weightedSplit c41SelectedMass at *
  exact div_nonneg (Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact mul_nonneg (ha i) ((P i).probR_nonneg σ)
    · exact le_rfl) hM.le

private theorem c41WeightedSplit_sum_one {ι : Type*} [Fintype ι]
    {w : ℕ} (a : ι → ℝ) (P : ι → SplitDist w)
    (selected : ι → Prop) [DecidablePred selected]
    (hM : 0 < c41SelectedMass a selected) :
    ∑ σ, weightedSplit a P selected σ = 1 := by
  unfold weightedSplit
  change (∑ σ : Chunk w,
    (∑ i, if selected i then a i * (P i).probR σ else 0) /
      c41SelectedMass a selected) = 1
  have hnum :
      (∑ σ : Chunk w, ∑ i, if selected i then a i * (P i).probR σ else 0) =
        c41SelectedMass a selected := by
    rw [Finset.sum_comm]
    unfold c41SelectedMass
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : selected i
    · simp only [hi, if_pos, ← Finset.mul_sum, (P i).sum_probR, mul_one]
    · simp [hi]
  calc
    (∑ σ : Chunk w,
      (∑ i, if selected i then a i * (P i).probR σ else 0) /
        c41SelectedMass a selected) =
        (∑ σ : Chunk w, ∑ i,
          if selected i then a i * (P i).probR σ else 0) /
          c41SelectedMass a selected := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = c41SelectedMass a selected / c41SelectedMass a selected := by rw [hnum]
    _ = 1 := div_self hM.ne'

private theorem c41WeightedSplit_close {ι : Type*} [Fintype ι]
    {w : ℕ} {ε : ℚ} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P Q : ι → SplitDist w) (selected : ι → Prop)
    [DecidablePred selected] (hM : 0 < c41SelectedMass a selected)
    (hclose : ∀ i σ, |(P i).probR σ - (Q i).probR σ| ≤ (ε : ℝ)) :
    ∀ σ, |weightedSplit a P selected σ - weightedSplit a Q selected σ| ≤
      (ε : ℝ) := by
  intro σ
  have hnum :
      |(∑ i, if selected i then a i * (P i).probR σ else 0) -
        ∑ i, if selected i then a i * (Q i).probR σ else 0| ≤
        c41SelectedMass a selected * (ε : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i, ((if selected i then a i * (P i).probR σ else 0) -
          (if selected i then a i * (Q i).probR σ else 0))| ≤
          ∑ i, |(if selected i then a i * (P i).probR σ else 0) -
            (if selected i then a i * (Q i).probR σ else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, if selected i then a i * (ε : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : selected i
        · simp only [hi, if_pos, ← mul_sub, abs_mul, abs_of_nonneg (ha i)]
          exact mul_le_mul_of_nonneg_left (hclose i σ) (ha i)
        · simp [hi]
      _ = c41SelectedMass a selected * (ε : ℝ) := by
        unfold c41SelectedMass
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : selected i <;> simp [hi]
  unfold weightedSplit
  rw [← sub_div, abs_div]
  change |(∑ i, if selected i then a i * (P i).probR σ else 0) -
      ∑ i, if selected i then a i * (Q i).probR σ else 0| /
      |c41SelectedMass a selected| ≤ (ε : ℝ)
  rw [abs_of_pos hM]
  apply (div_le_iff₀ hM).2
  calc
    |(∑ i, if selected i then a i * (P i).probR σ else 0) -
        ∑ i, if selected i then a i * (Q i).probR σ else 0| ≤
        c41SelectedMass a selected * (ε : ℝ) := hnum
    _ = (ε : ℝ) * c41SelectedMass a selected := mul_comm _ _

private theorem c41WeightedEntropy_abs {ι : Type*} [Fintype ι]
    {w : ℕ} {ε : ℚ} {debit : ℝ} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P Q : ι → SplitDist w) (selected : ι → Prop)
    [DecidablePred selected]
    (hclose : ∀ i σ, |(P i).probR σ - (Q i).probR σ| ≤ (ε : ℝ))
    (hdebit : 0 ≤ debit)
    (hbits : ∀ (x y : Chunk w → ℝ),
      (∀ σ, 0 ≤ x σ) → (∀ σ, 0 ≤ y σ) →
      (∑ σ, x σ = 1) → (∑ σ, y σ = 1) →
      (∀ σ, |x σ - y σ| ≤ (ε : ℝ)) →
      |entropy x - entropy y| ≤ debit) :
    |entropy (weightedSplit a P selected) -
      entropy (weightedSplit a Q selected)| ≤ debit := by
  by_cases hM0 : c41SelectedMass a selected = 0
  · have hPQ : weightedSplit a P selected = weightedSplit a Q selected := by
      funext σ
      unfold weightedSplit
      rw [show (∑ i, if selected i then a i else 0) = 0 by
        simpa only [c41SelectedMass] using hM0]
      simp
    rw [hPQ, sub_self, abs_zero]
    exact hdebit
  · have hM : 0 < c41SelectedMass a selected :=
      lt_of_le_of_ne (c41SelectedMass_nonneg a ha selected) (Ne.symm hM0)
    exact hbits _ _
      (c41WeightedSplit_nonneg a ha P selected hM)
      (c41WeightedSplit_nonneg a ha Q selected hM)
      (c41WeightedSplit_sum_one a P selected hM)
      (c41WeightedSplit_sum_one a Q selected hM)
      (c41WeightedSplit_close a ha P Q selected hM hclose)

private noncomputable def c41EntropyFunctional {ι : Type*} [Fintype ι]
    {w : ℕ} (a : ι → ℝ) (P : ι → SplitDist w)
    (direct : ι → Prop) [DecidablePred direct]
    (family : Fin (2 * w + 1) → ι → Prop)
    [∀ c, DecidablePred (family c)] : ℝ :=
  (∑ u, if direct u then a u * splitEntropy (P u) else 0) +
    ∑ c, c41SelectedMass a (family c) *
      entropy (weightedSplit a P (family c))

private theorem c41EntropyFunctional_sub_le {ι : Type*} [Fintype ι]
    {w : ℕ} {ε : ℚ} {debit S : ℝ}
    (a : ι → ℝ) (ha : ∀ u, 0 ≤ a u) (hsum : ∑ u, a u = S)
    (P Q : ι → SplitDist w)
    (direct : ι → Prop) [DecidablePred direct]
    (family : Fin (2 * w + 1) → ι → Prop)
    [∀ c, DecidablePred (family c)]
    (hclose : ∀ u σ, |(P u).probR σ - (Q u).probR σ| ≤ (ε : ℝ))
    (hdebit : 0 ≤ debit)
    (hbits : ∀ (x y : Chunk w → ℝ),
      (∀ σ, 0 ≤ x σ) → (∀ σ, 0 ≤ y σ) →
      (∑ σ, x σ = 1) → (∑ σ, y σ = 1) →
      (∀ σ, |x σ - y σ| ≤ (ε : ℝ)) →
      |entropy x - entropy y| ≤ debit) :
    c41EntropyFunctional a P direct family -
      c41EntropyFunctional a Q direct family ≤
        ((Fintype.card ι + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * S * debit := by
  have hS : 0 ≤ S := by rw [← hsum]; exact Finset.sum_nonneg fun u _ => ha u
  have hu : ∀ u : ι,
      (if direct u then a u * splitEntropy (P u) else 0) -
        (if direct u then a u * splitEntropy (Q u) else 0) ≤ S * debit := by
    intro u
    by_cases hdirect : direct u
    · simp only [hdirect, if_pos, ← mul_sub]
      have hent : |splitEntropy (P u) - splitEntropy (Q u)| ≤ debit := by
        unfold splitEntropy
        exact hbits _ _ (P u).probR_nonneg (Q u).probR_nonneg
          (P u).sum_probR (Q u).sum_probR (hclose u)
      have hau : a u ≤ S := by
        rw [← hsum]
        exact Finset.single_le_sum (fun v _ => ha v) (Finset.mem_univ u)
      exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hent) (ha u)).trans
        (mul_le_mul hau le_rfl hdebit hS)
    · simp [hdirect, mul_nonneg hS hdebit]
  have hc : ∀ c : Fin (2 * w + 1),
      c41SelectedMass a (family c) * entropy (weightedSplit a P (family c)) -
        c41SelectedMass a (family c) * entropy (weightedSplit a Q (family c)) ≤
          S * debit := by
    intro c
    rw [← mul_sub]
    have hent := c41WeightedEntropy_abs a ha P Q (family c) hclose hdebit hbits
    exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hent)
      (c41SelectedMass_nonneg a ha (family c))).trans
        (mul_le_mul (c41SelectedMass_le_total a ha S hsum (family c)) le_rfl
          hdebit hS)
  unfold c41EntropyFunctional
  calc
    ((∑ u, if direct u then a u * splitEntropy (P u) else 0) +
        ∑ c, c41SelectedMass a (family c) * entropy (weightedSplit a P (family c))) -
      ((∑ u, if direct u then a u * splitEntropy (Q u) else 0) +
        ∑ c, c41SelectedMass a (family c) * entropy (weightedSplit a Q (family c))) =
      (∑ u, ((if direct u then a u * splitEntropy (P u) else 0) -
        (if direct u then a u * splitEntropy (Q u) else 0))) +
      ∑ c, (c41SelectedMass a (family c) * entropy (weightedSplit a P (family c)) -
        c41SelectedMass a (family c) * entropy (weightedSplit a Q (family c))) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ ≤ (∑ _u : ι, S * debit) +
        ∑ _c : Fin (2 * w + 1), S * debit :=
      add_le_add (Finset.sum_le_sum fun u _ => hu u)
        (Finset.sum_le_sum fun c _ => hc c)
    _ = ((Fintype.card ι + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * S * debit := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_add]
      ring

private theorem c41_min_min_sub_le {x y₀ z₀ y₁ z₁ D : ℝ} (hD : 0 ≤ D)
    (hy : y₀ - y₁ ≤ D) (hz : z₀ - z₁ ≤ D) :
    min x (min y₀ z₀) - D ≤ min x (min y₁ z₁) := by
  apply le_min
  · exact (sub_le_self _ hD).trans (min_le_left _ _)
  · apply le_min
    · have hbase : min x (min y₀ z₀) ≤ y₀ :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · have hbase : min x (min y₀ z₀) ≤ z₀ :=
        (min_le_right _ _).trans (min_le_right _ _)
      linarith

private theorem c41_vanishes_add {f g : ℚ → ℝ}
    (hf : VanishesWithTolerance f) (hg : VanishesWithTolerance g) :
    VanishesWithTolerance (fun ε => f ε + g ε) := by
  constructor
  · intro ε
    exact add_nonneg (hf.1 ε) (hg.1 ε)
  · intro ζ hζ
    obtain ⟨εf, hεf, hsmallf⟩ := hf.2 (ζ / 2) (half_pos hζ)
    obtain ⟨εg, hεg, hsmallg⟩ := hg.2 (ζ / 2) (half_pos hζ)
    refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    intro ε hε hεle
    have hf' := hsmallf ε hε (hεle.trans (min_le_left _ _))
    have hg' := hsmallg ε hε (hεle.trans (min_le_right _ _))
    rw [abs_of_nonneg (add_nonneg (hf.1 ε) (hg.1 ε))]
    rw [abs_of_nonneg (hf.1 ε)] at hf'
    rw [abs_of_nonneg (hg.1 ε)] at hg'
    linarith

private theorem c41_vanishes_double {f : ℚ → ℝ}
    (hf : VanishesWithTolerance f) :
    VanishesWithTolerance (fun ε => f (2 * ε)) := by
  constructor
  · intro ε
    exact hf.1 (2 * ε)
  · intro ζ hζ
    obtain ⟨ε₀, hε₀, hsmall⟩ := hf.2 ζ hζ
    refine ⟨ε₀ / 2, div_pos hε₀ (by norm_num), ?_⟩
    intro ε hε hεle
    apply hsmall (2 * ε) (mul_pos (by norm_num) hε)
    linarith

private theorem constituentRegionRate_near41 {w s b m : ℕ} {ε : ℚ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (h : ConstituentFullGrid27 d m ε)
    (hε : 0 ≤ ε) (r : Fin 6) (dChild dRegion : ℝ)
    (hdChild : 0 ≤ dChild) (hdRegion : 0 ≤ dRegion)
    (hbitsChild : ∀ (x y : Chunk w → ℝ),
      (∀ σ, 0 ≤ x σ) → (∀ σ, 0 ≤ y σ) →
      (∑ σ, x σ = 1) → (∑ σ, y σ = 1) →
      (∀ σ, |x σ - y σ| ≤ (ε : ℝ)) →
      |entropy x - entropy y| ≤ dChild)
    (hbitsRegion : ∀ (x y : Chunk (w + w) → ℝ),
      (∀ σ, 0 ≤ x σ) → (∀ σ, 0 ≤ y σ) →
      (∑ σ, x σ = 1) → (∑ σ, y σ = 1) →
      (∀ σ, |x σ - y σ| ≤ ((2 * ε : ℚ) : ℝ)) →
      |entropy x - entropy y| ≤ dRegion) :
    constituentRegionRate d.toPaper r -
      ((∑ t : Fin s, (p.baseN t : ℝ)) * dRegion +
        (∑ t : Fin s, (p.baseN t : ℝ) *
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ)) * dChild) ≤
      constituentRegionRate
        (constituentGridSpec27 d hd m h.val).toPaper r := by
  let dg := constituentGridSpec27 d hd m h.val
  let xSide := d.perm r .X
  let ySide := d.perm r .Y
  let zSide := d.perm r .Z
  have hA0 : ∀ t, 0 ≤ (d.A t).probR r := fun t => (d.A t).probR_nonneg r
  have hA1 : ∀ t, (d.A t).probR r ≤ 1 := fun t => c41_probR_le_one (d.A t) r
  have hchild : ∀ W t u σ,
      |(dg.betaChild W t r u).probR σ - (d.betaChild W t r u).probR σ| ≤
        (ε : ℝ) := by
    intro W t u σ
    exact constituentGridBeta_close41 d hd h hε W t r u σ
  have hregion : ∀ W t σ,
      |(dg.betaRegion W t r).probR σ - (d.betaRegion W t r).probR σ| ≤
        ((2 * ε : ℚ) : ℝ) := by
    intro W t σ
    exact constituentGridRegionBeta_close41 d hd h hε W t r σ
  have htermY : ∀ t : Fin s,
      (splitEntropy (d.betaRegion ySide t r) -
          constituentEta d.toPaper t r xSide ySide zSide) -
        (splitEntropy (dg.betaRegion ySide t r) -
          constituentEta dg.toPaper t r xSide ySide zSide) ≤
        dRegion +
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild := by
    intro t
    let a : ChildShape p t → ℝ := symWeight d.toPaper t r
    let P : ChildShape p t → SplitDist w := fun u => dg.betaChild ySide t r u
    let Q : ChildShape p t → SplitDist w := fun u => d.betaChild ySide t r u
    have ha : ∀ u, 0 ≤ a u := by
      intro u
      rw [show a u = (d.alpha t r).probR u +
          (d.alpha t r).probR (complement p t u) by
        simp only [a, symWeight_eq_add_complement, ConstituentSpec.toPaper]]
      exact add_nonneg ((d.alpha t r).probR_nonneg u)
        ((d.alpha t r).probR_nonneg (complement p t u))
    have hasum : ∑ u, a u = 2 := by
      apply sum_symWeight_eq_two d.toPaper t r
      exact ⟨(d.alpha t r).probR_nonneg, (d.alpha t r).sum_probR⟩
    have heta : constituentEta dg.toPaper t r xSide ySide zSide -
        constituentEta d.toPaper t r xSide ySide zSide ≤
          ((Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * 2 * dChild := by
      have hf := c41EntropyFunctional_sub_le a ha hasum P Q
        (fun u => coord zSide u.1 = 0)
        (fun c u => coord ySide u.1 = c.val ∧ 0 < coord zSide u.1)
        (fun u σ => hchild ySide t u σ) hdChild hbitsChild
      simpa only [a, P, Q, dg, constituentGridSpec27, ConstituentSpec.toPaper,
        constituentEta, constituentAverage, c41EntropyFunctional,
        c41SelectedMass, Nat.cast_ofNat] using hf
    have hregEntropy : splitEntropy (d.betaRegion ySide t r) -
        splitEntropy (dg.betaRegion ySide t r) ≤ dRegion := by
      unfold splitEntropy
      exact (le_abs_self _).trans (hbitsRegion _ _
        (d.betaRegion ySide t r).probR_nonneg
        (dg.betaRegion ySide t r).probR_nonneg
        (d.betaRegion ySide t r).sum_probR
        (dg.betaRegion ySide t r).sum_probR
        (fun σ => by simpa only [abs_sub_comm] using hregion ySide t σ))
    calc
      _ = (splitEntropy (d.betaRegion ySide t r) -
          splitEntropy (dg.betaRegion ySide t r)) +
        (constituentEta dg.toPaper t r xSide ySide zSide -
          constituentEta d.toPaper t r xSide ySide zSide) := by ring
      _ ≤ dRegion +
          ((Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * 2 * dChild :=
        add_le_add hregEntropy heta
      _ = dRegion +
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild := by
        push_cast
        ring
  have htermZ : ∀ t : Fin s,
      (splitEntropy (d.betaRegion zSide t r) -
          constituentLambda d.toPaper t r xSide ySide zSide) -
        (splitEntropy (dg.betaRegion zSide t r) -
          constituentLambda dg.toPaper t r xSide ySide zSide) ≤
        dRegion +
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild := by
    intro t
    let a : ChildShape p t → ℝ := symWeight d.toPaper t r
    let P : ChildShape p t → SplitDist w := fun u => dg.betaChild zSide t r u
    let Q : ChildShape p t → SplitDist w := fun u => d.betaChild zSide t r u
    have ha : ∀ u, 0 ≤ a u := by
      intro u
      rw [show a u = (d.alpha t r).probR u +
          (d.alpha t r).probR (complement p t u) by
        simp only [a, symWeight_eq_add_complement, ConstituentSpec.toPaper]]
      exact add_nonneg ((d.alpha t r).probR_nonneg u)
        ((d.alpha t r).probR_nonneg (complement p t u))
    have hasum : ∑ u, a u = 2 := by
      apply sum_symWeight_eq_two d.toPaper t r
      exact ⟨(d.alpha t r).probR_nonneg, (d.alpha t r).sum_probR⟩
    have hlambda : constituentLambda dg.toPaper t r xSide ySide zSide -
        constituentLambda d.toPaper t r xSide ySide zSide ≤
          ((Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * 2 * dChild := by
      have hf := c41EntropyFunctional_sub_le a ha hasum P Q
        (fun u => coord xSide u.1 = 0 ∨ coord ySide u.1 = 0)
        (fun c u => 0 < coord xSide u.1 ∧ 0 < coord ySide u.1 ∧
          coord zSide u.1 = c.val)
        (fun u σ => hchild zSide t u σ) hdChild hbitsChild
      simpa only [a, P, Q, dg, constituentGridSpec27, ConstituentSpec.toPaper,
        constituentLambda, c41EntropyFunctional, c41SelectedMass,
        Nat.cast_ofNat] using hf
    have hregEntropy : splitEntropy (d.betaRegion zSide t r) -
        splitEntropy (dg.betaRegion zSide t r) ≤ dRegion := by
      unfold splitEntropy
      exact (le_abs_self _).trans (hbitsRegion _ _
        (d.betaRegion zSide t r).probR_nonneg
        (dg.betaRegion zSide t r).probR_nonneg
        (d.betaRegion zSide t r).sum_probR
        (dg.betaRegion zSide t r).sum_probR
        (fun σ => by simpa only [abs_sub_comm] using hregion zSide t σ))
    calc
      _ = (splitEntropy (d.betaRegion zSide t r) -
          splitEntropy (dg.betaRegion zSide t r)) +
        (constituentLambda dg.toPaper t r xSide ySide zSide -
          constituentLambda d.toPaper t r xSide ySide zSide) := by ring
      _ ≤ dRegion +
          ((Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * 2 * dChild :=
        add_le_add hregEntropy hlambda
      _ = dRegion +
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild := by
        push_cast
        ring
  have hrowY : constituentRowY d.toPaper r xSide ySide zSide -
      constituentRowY dg.toPaper r xSide ySide zSide ≤
      (∑ t : Fin s, (p.baseN t : ℝ)) * dRegion +
        (∑ t : Fin s, (p.baseN t : ℝ) *
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ)) * dChild := by
    unfold constituentRowY
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ t, ((d.A t).probR r * (p.baseN t : ℝ) *
          (splitEntropy (d.betaRegion ySide t r) -
            constituentEta d.toPaper t r xSide ySide zSide) -
        (d.A t).probR r * (p.baseN t : ℝ) *
          (splitEntropy (dg.betaRegion ySide t r) -
            constituentEta dg.toPaper t r xSide ySide zSide))) ≤
        ∑ t, (p.baseN t : ℝ) *
          (dRegion + ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) := by
          apply Finset.sum_le_sum
          intro t _
          rw [← mul_sub]
          have hweight : 0 ≤ (d.A t).probR r * (p.baseN t : ℝ) :=
            mul_nonneg (hA0 t) (Nat.cast_nonneg _)
          calc
            _ ≤ ((d.A t).probR r * (p.baseN t : ℝ)) *
                (dRegion + ((2 * (Fintype.card (ChildShape p t) +
                  Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) :=
              mul_le_mul_of_nonneg_left (htermY t) hweight
            _ ≤ (p.baseN t : ℝ) *
                (dRegion + ((2 * (Fintype.card (ChildShape p t) +
                  Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) := by
              apply mul_le_mul_of_nonneg_right
              · simpa only [one_mul] using
                  mul_le_mul_of_nonneg_right (hA1 t)
                    (Nat.cast_nonneg (p.baseN t))
              · exact add_nonneg hdRegion (mul_nonneg (Nat.cast_nonneg _) hdChild)
      _ = _ := by
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  have hrowZ : constituentRowZ d.toPaper r xSide ySide zSide -
      constituentRowZ dg.toPaper r xSide ySide zSide ≤
      (∑ t : Fin s, (p.baseN t : ℝ)) * dRegion +
        (∑ t : Fin s, (p.baseN t : ℝ) *
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ)) * dChild := by
    unfold constituentRowZ
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ t, ((d.A t).probR r * (p.baseN t : ℝ) *
          (splitEntropy (d.betaRegion zSide t r) -
            constituentLambda d.toPaper t r xSide ySide zSide) -
        (d.A t).probR r * (p.baseN t : ℝ) *
          (splitEntropy (dg.betaRegion zSide t r) -
            constituentLambda dg.toPaper t r xSide ySide zSide))) ≤
        ∑ t, (p.baseN t : ℝ) *
          (dRegion + ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) := by
          apply Finset.sum_le_sum
          intro t _
          rw [← mul_sub]
          have hweight : 0 ≤ (d.A t).probR r * (p.baseN t : ℝ) :=
            mul_nonneg (hA0 t) (Nat.cast_nonneg _)
          calc
            _ ≤ ((d.A t).probR r * (p.baseN t : ℝ)) *
                (dRegion + ((2 * (Fintype.card (ChildShape p t) +
                  Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) :=
              mul_le_mul_of_nonneg_left (htermZ t) hweight
            _ ≤ (p.baseN t : ℝ) *
                (dRegion + ((2 * (Fintype.card (ChildShape p t) +
                  Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ) * dChild) := by
              apply mul_le_mul_of_nonneg_right
              · simpa only [one_mul] using
                  mul_le_mul_of_nonneg_right (hA1 t)
                    (Nat.cast_nonneg (p.baseN t))
              · exact add_nonneg hdRegion (mul_nonneg (Nat.cast_nonneg _) hdChild)
      _ = _ := by
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  have hx : constituentRowX d.toPaper r xSide = constituentRowX dg.toPaper r xSide := by
    rfl
  change min (constituentRowX d.toPaper r xSide)
      (min (constituentRowY d.toPaper r xSide ySide zSide)
        (constituentRowZ d.toPaper r xSide ySide zSide)) -
      ((∑ t : Fin s, (p.baseN t : ℝ)) * dRegion +
        (∑ t : Fin s, (p.baseN t : ℝ) *
          ((2 * (Fintype.card (ChildShape p t) +
            Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ)) * dChild) ≤
    min (constituentRowX dg.toPaper r xSide)
      (min (constituentRowY dg.toPaper r xSide ySide zSide)
        (constituentRowZ dg.toPaper r xSide ySide zSide))
  rw [← hx]
  exact c41_min_min_sub_le
    (add_nonneg (mul_nonneg (Finset.sum_nonneg fun t _ => Nat.cast_nonneg _) hdRegion)
      (mul_nonneg (Finset.sum_nonneg fun t _ =>
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hdChild))
    hrowY hrowZ

private theorem entropy_bits_bound41 {α : Type*} [Fintype α]
    {ε : ℚ} {delta : ℚ → ℝ}
    (hlog : 0 < Real.log 2)
    (hcontinuity : ∀ (η : ℚ), 0 < η → ∀ (x y : α → ℝ),
      (∀ a, 0 ≤ x a) → (∀ a, 0 ≤ y a) →
      (∑ a, x a = 1) → (∑ a, y a = 1) →
      (∀ a, |x a - y a| ≤ η) →
      |entropyNats x - entropyNats y| ≤ delta η)
    (hε : 0 < ε) :
    ∀ (x y : α → ℝ),
      (∀ a, 0 ≤ x a) → (∀ a, 0 ≤ y a) →
      (∑ a, x a = 1) → (∑ a, y a = 1) →
      (∀ a, |x a - y a| ≤ (ε : ℝ)) →
      |entropy x - entropy y| ≤ (1 / Real.log 2) * delta ε := by
  intro x y hx hy hxsum hysum hxy
  have hnats := hcontinuity ε hε x y hx hy hxsum hysum hxy
  have hmul : Real.log 2 * |entropy x - entropy y| ≤ delta ε := by
    rw [← abs_of_pos hlog, ← abs_mul, mul_sub,
      ← entropyNats_eq_log_two_mul_entropy,
      ← entropyNats_eq_log_two_mul_entropy]
    exact hnats
  rw [one_div, inv_mul_eq_div]
  exact (le_div_iff₀ hlog).2 (by simpa only [mul_comm] using hmul)

set_option maxHeartbeats 2000000 in
-- The two finite alphabets and all parent terms are normalized in one final rate comparison.
/-- Uniform continuity of every regional constituent rate under the empirical full grid.
The modulus is fixed from the original width and parent multiplicities before the grid. -/
theorem constituent_grid_rate_ge_rate_sub_rho {w s b : ℕ}
    {p : ConstituentInput w s} (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) :
    ∃ rho : ℚ → ℝ, VanishesWithTolerance rho ∧
      ∀ ε : ℚ, 0 < ε → ∀ m : ℕ, ∀ h : ConstituentFullGrid27 d m ε,
        ∀ r : Fin 6,
          Real.log 2 * constituentRegionRate d.toPaper r - rho ε ≤
            Real.log 2 * constituentRegionRate
              (constituentGridSpec27 d hd m h.val).toPaper r := by
  obtain ⟨deltaChild, hdeltaChild, hcontinuityChild⟩ :=
    entropy_uniform_continuity (α := Chunk w)
  obtain ⟨deltaRegion, hdeltaRegion, hcontinuityRegion⟩ :=
    entropy_uniform_continuity (α := Chunk (w + w))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let childBits : ℚ → ℝ := fun ε => (1 / Real.log 2) * deltaChild ε
  let regionBits : ℚ → ℝ := fun ε => (1 / Real.log 2) * deltaRegion (2 * ε)
  let CRegion : ℝ := ∑ t : Fin s, (p.baseN t : ℝ)
  let CChild : ℝ := ∑ t : Fin s, (p.baseN t : ℝ) *
    ((2 * (Fintype.card (ChildShape p t) +
      Fintype.card (Fin (2 * w + 1))) : ℕ) : ℝ)
  let rho : ℚ → ℝ := fun ε => Real.log 2 *
    (CRegion * regionBits ε + CChild * childBits ε)
  have hchildBits : VanishesWithTolerance childBits :=
    vanishesWithTolerance_const_mul (1 / Real.log 2) (by positivity) hdeltaChild
  have hregionBits : VanishesWithTolerance regionBits := by
    apply vanishesWithTolerance_const_mul (1 / Real.log 2) (by positivity)
    exact c41_vanishes_double hdeltaRegion
  have hCRegion : 0 ≤ CRegion := Finset.sum_nonneg fun t _ => Nat.cast_nonneg _
  have hCChild : 0 ≤ CChild := Finset.sum_nonneg fun t _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hrho : VanishesWithTolerance rho := by
    apply vanishesWithTolerance_const_mul (Real.log 2) hlog.le
    exact c41_vanishes_add
      (vanishesWithTolerance_const_mul CRegion hCRegion hregionBits)
      (vanishesWithTolerance_const_mul CChild hCChild hchildBits)
  refine ⟨rho, hrho, ?_⟩
  intro ε hε m h r
  have hbitsChild := entropy_bits_bound41 (ε := ε) hlog hcontinuityChild hε
  have hbitsRegion := entropy_bits_bound41 (ε := 2 * ε) hlog hcontinuityRegion
    (mul_pos (by norm_num) hε)
  have hreg := constituentRegionRate_near41 d hd h hε.le r
    (childBits ε) (regionBits ε) (hchildBits.1 ε) (hregionBits.1 ε)
    hbitsChild (by
      intro x y hx hy hxsum hysum hxy
      simpa only [regionBits] using hbitsRegion x y hx hy hxsum hysum hxy)
  change Real.log 2 * constituentRegionRate d.toPaper r -
      Real.log 2 * (CRegion * regionBits ε + CChild * childBits ε) ≤ _
  calc
    _ = Real.log 2 * (constituentRegionRate d.toPaper r -
        (CRegion * regionBits ε + CChild * childBits ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [CRegion, CChild] using hreg) hlog.le

end
end OmegaBound.ADVXXZGeneral

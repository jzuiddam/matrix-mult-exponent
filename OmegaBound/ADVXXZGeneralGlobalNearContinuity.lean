import OmegaBound.ADVXXZGeneralEntropy
import OmegaBound.ADVXXZGeneralGlobalExactExponentIdentities
import OmegaBound.ADVXXZGeneralGridFull

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

private theorem near_probR_eq_cast_prob {iota : Type*} [Fintype iota]
    (P : RatDist iota) (a : iota) : P.probR a = ((P.prob a : ℚ) : ℝ) := by
  simp [RatDist.probR, RatDist.prob, Rat.cast_div]

private theorem globalExactGridBeta_close {w n : ℕ} {ε : ℚ} (g : GlobalSpec w)
    (xi : FullGrid g n ε) (hε : 0 ≤ ε) (W : Side) (r : Fin 6) (u : Shape w)
    (sigma : Chunk w) :
    |(globalExactGridBeta27 g xi.val W r u).probR sigma -
      (g.beta W r u).probR sigma| ≤ (ε : ℝ) := by
  let k := (((n : ℚ) * g.joint.prob (r, u)).floor.toNat)
  by_cases hk : 0 < k
  · have h := xi.property W r u hk sigma
    rw [globalExactGridBeta_probR27 g xi.val W r u sigma hk,
      near_probR_eq_cast_prob]
    have h' :
        (((|((xi.val.count W r u sigma : ℚ) / k -
          (g.beta W r u).prob sigma)| : ℚ) : ℝ) ≤ (ε : ℝ)) :=
      Rat.cast_le.mpr h
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using h'
  · unfold globalExactGridBeta27
    rw [dif_neg hk]
    simpa only [sub_self, abs_zero, Rat.cast_nonneg] using hε

private noncomputable def nearSelectedMass {iota : Type*} [Fintype iota]
    (a : iota → ℝ) (selected : iota → Prop) [DecidablePred selected] : ℝ :=
  ∑ i, if selected i then a i else 0

private theorem nearSelectedMass_nonneg {iota : Type*} [Fintype iota]
    (a : iota → ℝ) (ha : ∀ i, 0 ≤ a i)
    (selected : iota → Prop) [DecidablePred selected] :
    0 ≤ nearSelectedMass a selected := by
  unfold nearSelectedMass
  exact Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact ha i
    · exact le_rfl

private theorem nearSelectedMass_le_one {iota : Type*} [Fintype iota]
    (a : iota → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (selected : iota → Prop) [DecidablePred selected] :
    nearSelectedMass a selected ≤ 1 := by
  rw [← hsum]
  unfold nearSelectedMass
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact ha i

private theorem nearWeightedSplit_nonneg {iota : Type*} [Fintype iota]
    {w : ℕ} (a : iota → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : iota → SplitDist w) (selected : iota → Prop)
    [DecidablePred selected] (hM : 0 < nearSelectedMass a selected) :
    ∀ sigma, 0 ≤ weightedSplit a P selected sigma := by
  intro sigma
  unfold weightedSplit nearSelectedMass at *
  exact div_nonneg (Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact mul_nonneg (ha i) ((P i).probR_nonneg sigma)
    · exact le_rfl) hM.le

private theorem nearWeightedSplit_sum_one {iota : Type*} [Fintype iota]
    {w : ℕ} (a : iota → ℝ) (P : iota → SplitDist w)
    (selected : iota → Prop) [DecidablePred selected]
    (hM : 0 < nearSelectedMass a selected) :
    ∑ sigma, weightedSplit a P selected sigma = 1 := by
  unfold weightedSplit
  change (∑ sigma : Chunk w,
    (∑ i, if selected i then a i * (P i).probR sigma else 0) /
      nearSelectedMass a selected) = 1
  have hnum :
      (∑ sigma : Chunk w, ∑ i, if selected i then a i * (P i).probR sigma else 0) =
        nearSelectedMass a selected := by
    rw [Finset.sum_comm]
    unfold nearSelectedMass
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : selected i
    · simp only [hi, if_pos, ← Finset.mul_sum, (P i).sum_probR, mul_one]
    · simp [hi]
  calc
    (∑ sigma : Chunk w,
      (∑ i, if selected i then a i * (P i).probR sigma else 0) /
        nearSelectedMass a selected) =
        (∑ sigma : Chunk w, ∑ i,
          if selected i then a i * (P i).probR sigma else 0) /
          nearSelectedMass a selected := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = nearSelectedMass a selected / nearSelectedMass a selected := by rw [hnum]
    _ = 1 := div_self hM.ne'

private theorem nearWeightedSplit_close {iota : Type*} [Fintype iota]
    {w : ℕ} {ε : ℚ} (a : iota → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P Q : iota → SplitDist w) (selected : iota → Prop)
    [DecidablePred selected] (hM : 0 < nearSelectedMass a selected)
    (hclose : ∀ i sigma, |(P i).probR sigma - (Q i).probR sigma| ≤ (ε : ℝ)) :
    ∀ sigma, |weightedSplit a P selected sigma - weightedSplit a Q selected sigma| ≤
      (ε : ℝ) := by
  intro sigma
  have hnum :
      |(∑ i, if selected i then a i * (P i).probR sigma else 0) -
        ∑ i, if selected i then a i * (Q i).probR sigma else 0| ≤
        nearSelectedMass a selected * (ε : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |(∑ i, ((if selected i then a i * (P i).probR sigma else 0) -
          (if selected i then a i * (Q i).probR sigma else 0)))| ≤
          ∑ i, |(if selected i then a i * (P i).probR sigma else 0) -
            (if selected i then a i * (Q i).probR sigma else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, if selected i then a i * (ε : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : selected i
        · simp only [hi, if_pos, ← mul_sub, abs_mul, abs_of_nonneg (ha i)]
          exact mul_le_mul_of_nonneg_left (hclose i sigma) (ha i)
        · simp [hi]
      _ = nearSelectedMass a selected * (ε : ℝ) := by
        unfold nearSelectedMass
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : selected i <;> simp [hi]
  unfold weightedSplit
  rw [← sub_div, abs_div]
  change |(∑ i, if selected i then a i * (P i).probR sigma else 0) -
      ∑ i, if selected i then a i * (Q i).probR sigma else 0| /
      |nearSelectedMass a selected| ≤ (ε : ℝ)
  rw [abs_of_pos hM]
  apply (div_le_iff₀ hM).2
  calc
    |(∑ i, if selected i then a i * (P i).probR sigma else 0) -
        ∑ i, if selected i then a i * (Q i).probR sigma else 0| ≤
        nearSelectedMass a selected * (ε : ℝ) := hnum
    _ = (ε : ℝ) * nearSelectedMass a selected := mul_comm _ _

private theorem nearWeightedEntropy_abs {iota : Type*} [Fintype iota]
    {w : ℕ} {ε : ℚ} {d : ℝ} (a : iota → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P Q : iota → SplitDist w) (selected : iota → Prop)
    [DecidablePred selected]
    (hclose : ∀ i sigma, |(P i).probR sigma - (Q i).probR sigma| ≤ (ε : ℝ))
    (hd : 0 ≤ d)
    (hbits : ∀ (p q : Chunk w → ℝ),
      (∀ sigma, 0 ≤ p sigma) → (∀ sigma, 0 ≤ q sigma) →
      (∑ sigma, p sigma = 1) → (∑ sigma, q sigma = 1) →
      (∀ sigma, |p sigma - q sigma| ≤ (ε : ℝ)) →
      |entropy p - entropy q| ≤ d) :
    |entropy (weightedSplit a P selected) - entropy (weightedSplit a Q selected)| ≤ d := by
  by_cases hM0 : nearSelectedMass a selected = 0
  · have hPQ : weightedSplit a P selected = weightedSplit a Q selected := by
      funext sigma
      unfold weightedSplit
      rw [show (∑ i, if selected i then a i else 0) = 0 by
        simpa only [nearSelectedMass] using hM0]
      simp
    rw [hPQ, sub_self, abs_zero]
    exact hd
  · have hM : 0 < nearSelectedMass a selected :=
      lt_of_le_of_ne (nearSelectedMass_nonneg a ha selected) (Ne.symm hM0)
    exact hbits _ _
      (nearWeightedSplit_nonneg a ha P selected hM)
      (nearWeightedSplit_nonneg a ha Q selected hM)
      (nearWeightedSplit_sum_one a P selected hM)
      (nearWeightedSplit_sum_one a Q selected hM)
      (nearWeightedSplit_close a ha P Q selected hM hclose)

private noncomputable def nearAverage {iota : Type*} [Fintype iota]
    {w : ℕ} (a : iota → ℝ) (P : iota → SplitDist w) (sigma : Chunk w) : ℝ :=
  ∑ i, a i * (P i).probR sigma

private theorem nearWeightedSplit_all_eq_average {iota : Type*} [Fintype iota]
    {w : ℕ} (a : iota → ℝ) (hsum : ∑ i, a i = 1)
    (P : iota → SplitDist w) :
    weightedSplit a P (fun _ => True) = nearAverage a P := by
  funext sigma
  unfold weightedSplit nearAverage
  simp only [if_true, hsum, div_one]

private theorem nearAverageEntropy_abs {iota : Type*} [Fintype iota]
    {w : ℕ} {ε : ℚ} {d : ℝ} (a : iota → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
    (P Q : iota → SplitDist w)
    (hclose : ∀ i sigma, |(P i).probR sigma - (Q i).probR sigma| ≤ (ε : ℝ))
    (hd : 0 ≤ d)
    (hbits : ∀ (p q : Chunk w → ℝ),
      (∀ sigma, 0 ≤ p sigma) → (∀ sigma, 0 ≤ q sigma) →
      (∑ sigma, p sigma = 1) → (∑ sigma, q sigma = 1) →
      (∀ sigma, |p sigma - q sigma| ≤ (ε : ℝ)) →
      |entropy p - entropy q| ≤ d) :
    |entropy (nearAverage a P) - entropy (nearAverage a Q)| ≤ d := by
  rw [← nearWeightedSplit_all_eq_average a hsum P,
    ← nearWeightedSplit_all_eq_average a hsum Q]
  exact nearWeightedEntropy_abs a ha P Q (fun _ => True) hclose hd hbits

private noncomputable def nearEntropyFunctional {w : ℕ}
    (a : Shape w → ℝ) (P : Shape w → SplitDist w)
    (direct : Shape w → Prop) [DecidablePred direct]
    (family : Fin (2 * w + 1) → Shape w → Prop)
    [∀ c, DecidablePred (family c)] : ℝ :=
  (∑ u, if direct u then a u * splitEntropy (P u) else 0) +
    ∑ c, nearSelectedMass a (family c) *
      entropy (weightedSplit a P (family c))

private theorem nearEntropyFunctional_sub_le {w : ℕ} {ε : ℚ} {d : ℝ}
    (a : Shape w → ℝ) (ha : ∀ u, 0 ≤ a u) (hsum : ∑ u, a u = 1)
    (P Q : Shape w → SplitDist w)
    (direct : Shape w → Prop) [DecidablePred direct]
    (family : Fin (2 * w + 1) → Shape w → Prop)
    [∀ c, DecidablePred (family c)]
    (hclose : ∀ u sigma, |(P u).probR sigma - (Q u).probR sigma| ≤ (ε : ℝ))
    (hd : 0 ≤ d)
    (hbits : ∀ (p q : Chunk w → ℝ),
      (∀ sigma, 0 ≤ p sigma) → (∀ sigma, 0 ≤ q sigma) →
      (∑ sigma, p sigma = 1) → (∑ sigma, q sigma = 1) →
      (∀ sigma, |p sigma - q sigma| ≤ (ε : ℝ)) →
      |entropy p - entropy q| ≤ d) :
    nearEntropyFunctional a P direct family - nearEntropyFunctional a Q direct family ≤
      ((Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * d := by
  have hu : ∀ u : Shape w,
      (if direct u then a u * splitEntropy (P u) else 0) -
        (if direct u then a u * splitEntropy (Q u) else 0) ≤ d := by
    intro u
    by_cases hdirect : direct u
    · simp only [hdirect, if_pos, ← mul_sub]
      have hent : |splitEntropy (P u) - splitEntropy (Q u)| ≤ d := by
        unfold splitEntropy
        exact hbits _ _ (P u).probR_nonneg (Q u).probR_nonneg
          (P u).sum_probR (Q u).sum_probR (hclose u)
      calc
        a u * (splitEntropy (P u) - splitEntropy (Q u)) ≤ a u * d :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hent) (ha u)
        _ ≤ 1 * d := mul_le_mul_of_nonneg_right (by
          rw [← hsum]
          exact Finset.single_le_sum (fun v _ => ha v) (Finset.mem_univ u)) hd
        _ = d := one_mul d
    · simp [hdirect, hd]
  have hc : ∀ c : Fin (2 * w + 1),
      nearSelectedMass a (family c) * entropy (weightedSplit a P (family c)) -
        nearSelectedMass a (family c) * entropy (weightedSplit a Q (family c)) ≤ d := by
    intro c
    rw [← mul_sub]
    have hent := nearWeightedEntropy_abs a ha P Q (family c) hclose hd hbits
    calc
      nearSelectedMass a (family c) *
          (entropy (weightedSplit a P (family c)) -
            entropy (weightedSplit a Q (family c))) ≤
          nearSelectedMass a (family c) * d :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hent)
          (nearSelectedMass_nonneg a ha (family c))
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right
        (nearSelectedMass_le_one a ha hsum (family c)) hd
      _ = d := one_mul d
  unfold nearEntropyFunctional
  calc
    ((∑ u, if direct u then a u * splitEntropy (P u) else 0) +
        ∑ c, nearSelectedMass a (family c) * entropy (weightedSplit a P (family c))) -
      ((∑ u, if direct u then a u * splitEntropy (Q u) else 0) +
        ∑ c, nearSelectedMass a (family c) * entropy (weightedSplit a Q (family c))) =
      (∑ u, ((if direct u then a u * splitEntropy (P u) else 0) -
        (if direct u then a u * splitEntropy (Q u) else 0))) +
      ∑ c, (nearSelectedMass a (family c) * entropy (weightedSplit a P (family c)) -
        nearSelectedMass a (family c) * entropy (weightedSplit a Q (family c))) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ ≤ (∑ _u : Shape w, d) + ∑ _c : Fin (2 * w + 1), d :=
      add_le_add (Finset.sum_le_sum fun u _ => hu u) (Finset.sum_le_sum fun c _ => hc c)
    _ = ((Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * d := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
      ring

private theorem min_min_sub_le {x y₀ z₀ y₁ z₁ D : ℝ} (hD : 0 ≤ D)
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

private theorem globalRegionRate_near {w n : ℕ} {ε : ℚ} (g : GlobalSpec w)
    (xi : FullGrid g n ε) (hε : 0 ≤ ε) (r : Fin 6) (d : ℝ) (hd : 0 ≤ d)
    (hbits : ∀ (p q : Chunk w → ℝ),
      (∀ sigma, 0 ≤ p sigma) → (∀ sigma, 0 ≤ q sigma) →
      (∑ sigma, p sigma = 1) → (∑ sigma, q sigma = 1) →
      (∀ sigma, |p sigma - q sigma| ≤ (ε : ℝ)) →
      |entropy p - entropy q| ≤ d) :
    globalRegionRate g.toPaper r -
      ((1 + Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * d ≤
      globalRegionRate (globalExactGridData27 g xi.val) r := by
  let a : Shape w → ℝ := fun u => (g.alpha r).probR u
  let xSide := g.perm r .X
  let ySide := g.perm r .Y
  let zSide := g.perm r .Z
  let P (W : Side) : Shape w → SplitDist w := fun u =>
    globalExactGridBeta27 g xi.val W r u
  let Q (W : Side) : Shape w → SplitDist w := fun u => g.beta W r u
  have ha : ∀ u, 0 ≤ a u := (g.alpha r).probR_nonneg
  have hasum : ∑ u, a u = 1 := (g.alpha r).sum_probR
  have hclose : ∀ W u sigma, |(P W u).probR sigma - (Q W u).probR sigma| ≤ (ε : ℝ) :=
    fun W u sigma => globalExactGridBeta_close g xi hε W r u sigma
  let K : ℝ := ((Fintype.card (Shape w) +
    Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ)
  let D : ℝ := (1 + K) * d
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hD : 0 ≤ D := mul_nonneg (by dsimp [K]; positivity) hd
  have hyAvg : entropy (nearAverage a (Q ySide)) - entropy (nearAverage a (P ySide)) ≤ d :=
    (le_abs_self _).trans (nearAverageEntropy_abs a ha hasum (Q ySide) (P ySide)
      (fun u sigma => by simpa only [abs_sub_comm] using hclose ySide u sigma) hd hbits)
  have hzAvg : entropy (nearAverage a (Q zSide)) - entropy (nearAverage a (P zSide)) ≤ d :=
    (le_abs_self _).trans (nearAverageEntropy_abs a ha hasum (Q zSide) (P zSide)
      (fun u sigma => by simpa only [abs_sub_comm] using hclose zSide u sigma) hd hbits)
  have hyFun :
      nearEntropyFunctional a (P ySide) (fun u => coord zSide u = 0)
          (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u) -
        nearEntropyFunctional a (Q ySide) (fun u => coord zSide u = 0)
          (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u) ≤ K * d := by
    simpa only [K] using nearEntropyFunctional_sub_le a ha hasum (P ySide) (Q ySide)
      (fun u => coord zSide u = 0)
      (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u) (hclose ySide) hd hbits
  have hzFun :
      nearEntropyFunctional a (P zSide)
          (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
          (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val) -
        nearEntropyFunctional a (Q zSide)
          (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
          (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val) ≤ K * d := by
    simpa only [K] using nearEntropyFunctional_sub_le a ha hasum (P zSide) (Q zSide)
      (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
      (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val)
      (hclose zSide) hd hbits
  have hy :
      (entropy (nearAverage a (Q ySide)) -
          nearEntropyFunctional a (Q ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u)) -
        (entropy (nearAverage a (P ySide)) -
          nearEntropyFunctional a (P ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u)) ≤ D := by
    calc
      _ = (entropy (nearAverage a (Q ySide)) - entropy (nearAverage a (P ySide))) +
          (nearEntropyFunctional a (P ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u) -
           nearEntropyFunctional a (Q ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u)) := by ring
      _ ≤ d + K * d := add_le_add hyAvg hyFun
      _ = D := by dsimp [D]; ring
  have hz :
      (entropy (nearAverage a (Q zSide)) -
          nearEntropyFunctional a (Q zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val)) -
        (entropy (nearAverage a (P zSide)) -
          nearEntropyFunctional a (P zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val)) ≤ D := by
    calc
      _ = (entropy (nearAverage a (Q zSide)) - entropy (nearAverage a (P zSide))) +
          (nearEntropyFunctional a (P zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val) -
           nearEntropyFunctional a (Q zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val)) := by ring
      _ ≤ d + K * d := add_le_add hzAvg hzFun
      _ = D := by dsimp [D]; ring
  have hcoeff :
      (((1 + Fintype.card (Shape w) + Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ) * d) = D := by
    dsimp [D, K]
    push_cast
    ring
  rw [hcoeff]
  unfold globalRegionRate
  dsimp only [GlobalSpec.toPaper, globalExactGridData27]
  unfold globalAverage globalEta globalLambda
  change min (entropy (marginal a xSide) - penalty a)
      (min (entropy (nearAverage a (Q ySide)) -
          nearEntropyFunctional a (Q ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u))
        (entropy (nearAverage a (Q zSide)) -
          nearEntropyFunctional a (Q zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val))) - D ≤
    min (entropy (marginal a xSide) - penalty a)
      (min (entropy (nearAverage a (P ySide)) -
          nearEntropyFunctional a (P ySide) (fun u => coord zSide u = 0)
            (fun c u => coord ySide u = c.val ∧ 0 < coord zSide u))
        (entropy (nearAverage a (P zSide)) -
          nearEntropyFunctional a (P zSide)
            (fun u => coord xSide u = 0 ∨ coord ySide u = 0)
            (fun c u => 0 < coord xSide u ∧ 0 < coord ySide u ∧ coord zSide u = c.val)))
  simpa only [D, K, Nat.cast_add, Nat.cast_one] using
    min_min_sub_le hD hy hz

/-- Uniform continuity of the full exact-grid rate around the global center. -/
theorem gridRate_ge_gRate_sub_delta {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) :
    ∃ delta : ℚ → ℝ, VanishesWithTolerance delta ∧
      ∀ ε : ℚ, 0 < ε → ∀ m : ℕ, ∀ xi : FullGrid g (b * m) ε,
        gRate g - delta ε ≤ gridRate g (b * m) xi.val := by
  obtain ⟨delta₀, hdelta₀, hcontinuity⟩ := entropy_uniform_continuity (α := Chunk w)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : ℝ := ((1 + Fintype.card (Shape w) +
    Fintype.card (Fin (2 * w + 1)) : ℕ) : ℝ)
  let deltaBits : ℚ → ℝ := fun ε => (1 / Real.log 2) * delta₀ ε
  let delta : ℚ → ℝ := fun ε => (Real.log 2 * K) * deltaBits ε
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hdeltaBits : VanishesWithTolerance deltaBits :=
    vanishesWithTolerance_const_mul (1 / Real.log 2) (by positivity) hdelta₀
  refine ⟨delta, vanishesWithTolerance_const_mul (Real.log 2 * K)
    (mul_nonneg hlog.le hK) hdeltaBits, ?_⟩
  intro ε hε m xi
  have hbits : ∀ (p q : Chunk w → ℝ),
      (∀ sigma, 0 ≤ p sigma) → (∀ sigma, 0 ≤ q sigma) →
      (∑ sigma, p sigma = 1) → (∑ sigma, q sigma = 1) →
      (∀ sigma, |p sigma - q sigma| ≤ (ε : ℝ)) →
      |entropy p - entropy q| ≤ deltaBits ε := by
    intro p q hp hq hpsum hqsum hpq
    have hnats := hcontinuity ε hε p q hp hq hpsum hqsum hpq
    have hmul : Real.log 2 * |entropy p - entropy q| ≤ delta₀ ε := by
      rw [← abs_of_pos hlog, ← abs_mul, mul_sub,
        ← entropyNats_eq_log_two_mul_entropy,
        ← entropyNats_eq_log_two_mul_entropy]
      exact hnats
    change |entropy p - entropy q| ≤ (1 / Real.log 2) * delta₀ ε
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hlog).2 (by simpa only [mul_comm] using hmul)
  have hreg : ∀ r : Fin 6,
      globalRegionRate g.toPaper r - K * deltaBits ε ≤
        globalRegionRate (globalExactGridData27 g xi.val) r := by
    intro r
    simpa only [K] using globalRegionRate_near g xi hε.le r (deltaBits ε)
      (hdeltaBits.1 ε) hbits
  have hsum :
      (∑ r, g.A.probR r * globalRegionRate g.toPaper r) - K * deltaBits ε ≤
        ∑ r, g.A.probR r * globalRegionRate (globalExactGridData27 g xi.val) r := by
    calc
      (∑ r, g.A.probR r * globalRegionRate g.toPaper r) - K * deltaBits ε =
          ∑ r, g.A.probR r *
            (globalRegionRate g.toPaper r - K * deltaBits ε) := by
        calc
          _ = (∑ r, g.A.probR r * globalRegionRate g.toPaper r) -
              (∑ r, g.A.probR r) * (K * deltaBits ε) := by
            rw [g.A.sum_probR, one_mul]
          _ = ∑ r, (g.A.probR r * globalRegionRate g.toPaper r -
              g.A.probR r * (K * deltaBits ε)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ ≤ ∑ r, g.A.probR r *
          globalRegionRate (globalExactGridData27 g xi.val) r := by
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left (hreg r) (g.A.probR_nonneg r)
  rw [gRate, gridRate_eq_globalExactGridData27]
  change Real.log 2 * (∑ r, g.A.probR r * globalRegionRate g.toPaper r) -
      delta ε ≤ Real.log 2 *
        ∑ r, g.A.probR r * globalRegionRate (globalExactGridData27 g xi.val) r
  change Real.log 2 * (∑ r, g.A.probR r * globalRegionRate g.toPaper r) -
      (Real.log 2 * K) * deltaBits ε ≤ _
  calc
    Real.log 2 * (∑ r, g.A.probR r * globalRegionRate g.toPaper r) -
        (Real.log 2 * K) * deltaBits ε =
      Real.log 2 * ((∑ r, g.A.probR r * globalRegionRate g.toPaper r) -
        K * deltaBits ε) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hlog.le

end
end OmegaBound.ADVXXZGeneral
end

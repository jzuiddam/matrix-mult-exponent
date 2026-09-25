import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem ordinary_large_coord_rows
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) :
    coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1)
      (ordinaryOccurrence t).1.2.2.1 = 2 := by
  have hx := (ordinaryOccurrence t).2.2.1
  have hy := (ordinaryOccurrence t).2.2.2.1
  have hz := (ordinaryOccurrence t).2.2.2.2
  have hs := (ordinaryOccurrence t).1.2.2.1.property
  change coord .X (ordinaryOccurrence t).1.2.2.1 +
    coord .Y (ordinaryOccurrence t).1.2.2.1 +
    coord .Z (ordinaryOccurrence t).1.2.2.1 = 4 at hs
  simp only [ordinaryLargeSide]
  split
  · assumption
  · split
    · assumption
    · omega

private theorem negMulLog_half_rows :
    Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
  rw [Real.negMulLog, one_div, Real.log_inv]
  ring

private def ordinaryMarginalLargeCount (v : Shape 2) (W : Side) (a : Fin 3) : ℕ :=
  (Finset.univ.filter fun x : OrdinaryChild v =>
    coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 = 1).card

private def ordinaryMarginalOtherCount (v : Shape 2) (W : Side) (a : Fin 3) : ℕ :=
  (Finset.univ.filter fun x : OrdinaryChild v =>
    coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 ≠ 1).card

private def ordinaryMarginalLargeExpected (same : Bool) (a : Fin 3) : ℕ :=
  if same then if a = 1 then 2 else 0 else if a = 2 then 0 else 1

private def ordinaryMarginalOtherExpected (same : Bool) (a : Fin 3) : ℕ :=
  if same then if a = 1 then 0 else 1 else if a = 2 then 0 else 1

private theorem ordinary_marginal_counts (v : Shape 2)
    (hx : 0 < coord .X v) (hy : 0 < coord .Y v) (hz : 0 < coord .Z v)
    (W : Side) (a : Fin 3) :
    ordinaryMarginalLargeCount v W a =
        ordinaryMarginalLargeExpected (W == ordinaryLargeSide v) a ∧
      ordinaryMarginalOtherCount v W a =
        ordinaryMarginalOtherExpected (W == ordinaryLargeSide v) a := by
  revert v W a
  decide +kernel

private theorem ordinary_marginal_sum (v : Shape 2) (W : Side) (a : Fin 3)
    (large other : ℝ) :
    (∑ x : OrdinaryChild v,
      if coord W x.1 = a.val then
        if coord (ordinaryLargeSide v) x.1 = 1 then large else other
      else 0) =
      (ordinaryMarginalLargeCount v W a : ℝ) * large +
        (ordinaryMarginalOtherCount v W a : ℝ) * other := by
  classical
  calc
    _ = (∑ x : OrdinaryChild v,
          if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 = 1
          then large else 0) +
        ∑ x : OrdinaryChild v,
          if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 ≠ 1
          then other else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hW : coord W x.1 = a.val <;>
        by_cases hL : coord (ordinaryLargeSide v) x.1 = 1 <;> simp [hW, hL]
    _ = _ := by
      have hlarge :
          (∑ x : OrdinaryChild v,
            if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 = 1
            then large else 0) =
            (ordinaryMarginalLargeCount v W a : ℝ) * large := by
        change (∑ x ∈ (Finset.univ : Finset (OrdinaryChild v)),
          if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 = 1
          then large else 0) = _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl
      have hother :
          (∑ x : OrdinaryChild v,
            if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 ≠ 1
            then other else 0) =
            (ordinaryMarginalOtherCount v W a : ℝ) * other := by
        change (∑ x ∈ (Finset.univ : Finset (OrdinaryChild v)),
          if coord W x.1 = a.val ∧ coord (ordinaryLargeSide v) x.1 ≠ 1
          then other else 0) = _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hlarge, hother]

private theorem ordinary_marginal_probability
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (W : Side) (a : Fin 3) :
    constituentMarginal releasedOrdinaryData2.toPaper t 0 W a =
      if W = ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1 then
        ![((ordinaryTarget t).muNum : ℝ) / ordinaryD,
          1 - 2 * ((ordinaryTarget t).muNum : ℝ) / ordinaryD,
          ((ordinaryTarget t).muNum : ℝ) / ordinaryD] a
      else ![(1 : ℝ) / 2, (1 : ℝ) / 2, 0] a := by
  let v := (ordinaryOccurrence t).1.2.2.1
  let mu := (ordinaryTarget t).muNum
  have hc := ordinary_marginal_counts v (ordinaryOccurrence t).2.2.1
    (ordinaryOccurrence t).2.2.2.1 (ordinaryOccurrence t).2.2.2.2 W a
  have hD : (ordinaryD : ℝ) ≠ 0 := by norm_num [ordinaryD, OmegaBound.ADVXXZT2.certDen]
  have hmu : mu ≤ ordinaryD / 2 := ordinaryTarget_mu_bound t
  unfold constituentMarginal
  simp only [ConstituentSpec.toPaper, releasedOrdinaryData2, ordinaryAlphaDist,
    RatDist.probR, RatDist.prob]
  dsimp only [v, mu] at hc ⊢
  simp only [Nat.cast_ite, ite_div]
  change (∑ x : OrdinaryChild (ordinaryOccurrence t).1.2.2.1,
    if coord W x.1 = a.val then
      if coord (ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) x.1 = 1 then
        ((ordinaryD / 2 - (ordinaryTarget t).muNum : ℕ) : ℝ) / ordinaryD
      else ((ordinaryTarget t).muNum : ℝ) / ordinaryD
    else 0) = _
  rw [ordinary_marginal_sum
    (v := (ordinaryOccurrence t).1.2.2.1) (W := W) (a := a)
    (large := ((ordinaryD / 2 - (ordinaryTarget t).muNum : ℕ) : ℝ) /
      (ordinaryD : ℝ))
    (other := ((ordinaryTarget t).muNum : ℝ) / (ordinaryD : ℝ))]
  have heven : 2 * (ordinaryD / 2) = ordinaryD := by decide +kernel
  have hevenR : (2 : ℝ) * (ordinaryD / 2 : ℕ) = (ordinaryD : ℝ) := by
    exact_mod_cast heven
  have hcastsub :
      ((ordinaryD / 2 - (ordinaryTarget t).muNum : ℕ) : ℝ) =
        ((ordinaryD / 2 : ℕ) : ℝ) - ((ordinaryTarget t).muNum : ℝ) := by
    exact Nat.cast_sub hmu
  by_cases hW : W = ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1
  · subst W
    rw [if_pos rfl]
    simp only [beq_self_eq_true, ordinaryMarginalLargeExpected,
      ordinaryMarginalOtherExpected] at hc
    simp only [if_true] at hc
    fin_cases a <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_fin_one,
        Matrix.empty_val', Fin.isValue, Fin.reduceFinMk, Fin.zero_eta] at hc ⊢ <;>
      (try simp only [Fin.ext_iff] at hc) <;> norm_num at hc <;>
      rcases hc with ⟨hcL, hcO⟩ <;> rw [hcL, hcO] <;>
      (try simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul,
        mul_zero, zero_add, add_zero]) <;>
      (try simp only [hcastsub]) <;> field_simp [hD] <;> linarith [hevenR]
  · rw [if_neg hW]
    have hb : (W == ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1) = false := by
      cases hbeq : W == ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1 with
      | false => rfl
      | true => exact (hW (beq_iff_eq.mp hbeq)).elim
    simp only [hb, Bool.false_eq_true, if_false, ordinaryMarginalLargeExpected,
      ordinaryMarginalOtherExpected] at hc
    fin_cases a <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_fin_one,
        Matrix.empty_val', Fin.isValue, Fin.reduceFinMk, Fin.zero_eta] at hc ⊢ <;>
      (try simp only [Fin.ext_iff] at hc) <;> norm_num at hc <;>
      rcases hc with ⟨hcL, hcO⟩ <;> rw [hcL, hcO] <;>
      (try simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul,
        mul_zero, zero_add, add_zero]) <;>
      (try simp only [hcastsub]) <;> field_simp [hD] <;> linarith [hevenR]

theorem released_ordinary_marginal_evaluator
    (t : Fin (Fintype.card ReleasedOrdinaryOccurrence)) (r : Fin 6) (W : Side) :
    Real.log 2 * entropy (constituentMarginal releasedOrdinaryData2.toPaper t r W) =
      ordinary112Nats t W := by
  have hr : constituentMarginal releasedOrdinaryData2.toPaper t r W =
      constituentMarginal releasedOrdinaryData2.toPaper t 0 W := by
    funext a
    rfl
  rw [hr, mul_comm]
  unfold entropy
  rw [Entropy.H_mul_log_two]
  rw [show Entropy.H Finset.univ
      (constituentMarginal releasedOrdinaryData2.toPaper t 0 W) =
      ∑ a : Fin 3, Real.negMulLog
        (constituentMarginal releasedOrdinaryData2.toPaper t 0 W a) by rfl]
  simp_rw [ordinary_marginal_probability]
  unfold ordinary112Nats
  by_cases hW : W = ordinaryLargeSide (ordinaryOccurrence t).1.2.2.1
  · simp only [hW, if_true]
    have hlarge := ordinary_large_coord_rows t
    simp only [hlarge, if_true]
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_fin_one,
      Matrix.empty_val', Fin.isValue, Fin.reduceFinMk, Fin.zero_eta]
    unfold OmegaBound.ADVXXZLevel2Closure.entropyMu
    have harg : 1 - 2 * ((ordinaryTarget t).muNum : ℝ) / ordinaryD =
        1 - 2 * (((ordinaryTarget t).muNum : ℝ) / ordinaryD) := by ring
    rw [harg]
    ring
  · have hcoord : coord W (ordinaryOccurrence t).1.2.2.1 ≠ 2 := by
      intro htwo
      have hx := (ordinaryOccurrence t).2.2.1
      have hy := (ordinaryOccurrence t).2.2.2.1
      have hz := (ordinaryOccurrence t).2.2.2.2
      have hs := (ordinaryOccurrence t).1.2.2.1.property
      change coord .X (ordinaryOccurrence t).1.2.2.1 +
        coord .Y (ordinaryOccurrence t).1.2.2.1 +
        coord .Z (ordinaryOccurrence t).1.2.2.1 = 4 at hs
      cases W with
      | X =>
          apply hW
          simp [ordinaryLargeSide, htwo]
      | Y =>
          have hX : coord .X (ordinaryOccurrence t).1.2.2.1 ≠ 2 := by omega
          apply hW
          simp [ordinaryLargeSide, hX, htwo]
      | Z =>
          have hX : coord .X (ordinaryOccurrence t).1.2.2.1 ≠ 2 := by omega
          have hY : coord .Y (ordinaryOccurrence t).1.2.2.1 ≠ 2 := by omega
          apply hW
          simp [ordinaryLargeSide, hX, hY]
    rw [if_neg hcoord]
    simp only [hW, if_false]
    rw [Fin.sum_univ_three]
    change Real.negMulLog ((1 : ℝ) / 2) + Real.negMulLog ((1 : ℝ) / 2) +
      Real.negMulLog 0 = Real.log 2
    rw [Real.negMulLog_zero, add_zero]
    rw [negMulLog_half_rows]
    ring

end OmegaBound.ADVXXZGeneral
end

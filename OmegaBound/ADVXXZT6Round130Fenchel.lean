import OmegaBound.ADVXXZT6DenominatorBase
import OmegaBound.ADVXXZT6Round61ReleasedCountProbe
import OmegaBound.ADVXXZT6Round82RealDisintegration
import Mathlib.Topology.Instances.Rat

/-!
# Exact Fenchel transport

The released X evaluator uses the exponential Fenchel dual.  This file proves the scalar
inequality behind that evaluator directly from `Real.add_one_le_exp`; no rounded logarithm or
saved maximum-entropy witness enters the theorem.
-/

set_option linter.style.longLine false

namespace OmegaBound.ADVXXZT6Round130

open Finset
open OmegaBound.ADVXXZPaper
open OmegaBound.ADVXXZT9R16PositiveParents (releasedPositiveInput)

/-- Scalar entropy/Fenchel inequality, including the zero-mass case. -/
theorem negMulLog_le_exp_sub_mul130 (x y : Real) (hx : 0 ≤ x) :
    Real.negMulLog x ≤ Real.exp (y - 1) - x * y := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using (Real.exp_pos (y - 1)).le
  · have h := Real.add_one_le_exp (y - 1 - Real.log x)
    rw [Real.exp_sub, Real.exp_log hx] at h
    have hmul := mul_le_mul_of_nonneg_left h hx.le
    rw [mul_div_cancel₀ _ hx.ne'] at hmul
    rw [Real.negMulLog_eq_neg]
    nlinarith

/-- A direct exponential Fenchel expression bounds entropy on any finite support. -/
theorem entropy_le_fenchel130 {A : Type*} [Fintype A]
    (rho : A → Real) (linear : A → Real)
    (hrho : ∀ a, 0 ≤ rho a) :
    Entropy.H Finset.univ rho ≤
      (∑ a, Real.exp (linear a - 1)) - ∑ a, rho a * linear a := by
  rw [Entropy.H, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun a _ => negMulLog_le_exp_sub_mul130 _ _ (hrho a)

/-- The coordinate of a paper child shape as a value of its literal five-level alphabet. -/
def childLevel130 (p : Fin 126) (W : Side)
    (u : ChildShape releasedPositiveInput p) : Fin 5 :=
  match W with
  | .X => u.1.1.1
  | .Y => u.1.1.2.1
  | .Z => u.1.1.2.2

@[simp] theorem childLevel130_val (p : Fin 126) (W : Side)
    (u : ChildShape releasedPositiveInput p) :
    (childLevel130 p W u : Nat) = coord W u.1 := by
  cases W <;> rfl

/-- The released row-index spelling of a child coordinate. -/
def releasedKidLevel130 (p : Fin 126)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) (W : Side) : Fin 5 :=
  match W with
  | .X => (OmegaBound.ADVXXZT6Selection.kidPat p d).1.1
  | .Y => (OmegaBound.ADVXXZT6Selection.kidPat p d).1.2.1
  | .Z => (OmegaBound.ADVXXZT6Selection.kidPat p d).1.2.2

@[simp] theorem childLevel_childRowEquiv_symm130 (p : Fin 126)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) (W : Side) :
    childLevel130 p W (OmegaBound.ADVXXZT6Round78.childRowEquiv p |>.symm d) =
      releasedKidLevel130 p d W := by
  let u := OmegaBound.ADVXXZT6Round78.childRowEquiv p |>.symm d
  have hi : OmegaBound.ADVXXZT6Round78.childIndex p u = d := by
    exact (OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply d
  have hk := OmegaBound.ADVXXZT6Round82.kidPat_childIndex p u
  rw [hi] at hk
  cases W
  · exact (congrArg (fun z => z.1.1) hk).symm
  · exact (congrArg (fun z => z.1.2.1) hk).symm
  · exact (congrArg (fun z => z.1.2.2) hk).symm

/-- The released alpha row, reindexed by its committed finite row order. -/
@[simp] theorem releasedCorrectedData_alpha_childRowEquiv_symm130
    (p : Fin 126) (r : Fin 6)
    (d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length) :
    OmegaBound.ADVXXZT6Round82.releasedCorrectedData.alpha p r
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) =
      (OmegaBound.ADVXXZT6Round82.releasedChildRowDist p r).probR d := by
  change (OmegaBound.ADVXXZT6Round82.releasedChildRowDist p r).probR
      (OmegaBound.ADVXXZT6Round78.childIndex p
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d)) = _
  have hi : OmegaBound.ADVXXZT6Round78.childIndex p
      ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) = d :=
    (OmegaBound.ADVXXZT6Round78.childRowEquiv p).apply_symm_apply d
  rw [hi]

/-- Exact rational-multiplier expression used by the released parentwise X evaluator. -/
noncomputable def constituentFenchelUpper130 (p : Fin 126)
    (a : ChildShape releasedPositiveInput p → Real)
    (lambdaSum : Real) (lambdaMargin : Side → Fin 5 → Real) : Real :=
  let linear := fun u : ChildShape releasedPositiveInput p =>
    lambdaSum + ∑ W : Side, lambdaMargin W (childLevel130 p W u)
  (∑ u, Real.exp (linear u - 1)) - ∑ u, a u * linear u

/-- Reindex the finite Fenchel expression by the committed child-row order. -/
theorem constituentFenchelUpper_reindex130 (p : Fin 126)
    (a : ChildShape releasedPositiveInput p → Real)
    (lambdaSum : Real) (lambdaMargin : Side → Fin 5 → Real) :
    constituentFenchelUpper130 p a lambdaSum lambdaMargin =
      (∑ d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length,
        Real.exp
          (lambdaSum + ∑ W : Side, lambdaMargin W (releasedKidLevel130 p d W) - 1)) -
      ∑ d : Fin (OmegaBound.ADVXXZT2.parKids p.val).length,
        a ((OmegaBound.ADVXXZT6Round78.childRowEquiv p).symm d) *
          (lambdaSum + ∑ W : Side,
            lambdaMargin W (releasedKidLevel130 p d W)) := by
  classical
  unfold constituentFenchelUpper130
  dsimp only
  have hlevel (u : ChildShape releasedPositiveInput p) (W : Side) :
      childLevel130 p W u = releasedKidLevel130 p
        ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W := by
    simpa using childLevel_childRowEquiv_symm130 p
      ((OmegaBound.ADVXXZT6Round78.childRowEquiv p) u) W
  congr 1
  · exact Fintype.sum_equiv (OmegaBound.ADVXXZT6Round78.childRowEquiv p)
      _ _ (fun u => by simp_rw [hlevel u])
  · exact Fintype.sum_equiv (OmegaBound.ADVXXZT6Round78.childRowEquiv p)
      _ _ (fun u => by simp_rw [hlevel u]; simp)

private theorem sum_marginal_mul130 (p : Fin 126)
    (a : ChildShape releasedPositiveInput p → Real)
    (W : Side) (lambda : Fin 5 → Real) :
    (∑ x : Fin 5,
        (∑ u, if coord W u.1 = (x : Nat) then a u else 0) * lambda x) =
      ∑ u, a u * lambda (childLevel130 p W u) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single (childLevel130 p W u)]
  · rw [if_pos]
    exact (childLevel130_val p W u).symm
  · intro x _ hx
    rw [if_neg]
    · simp
    · intro heq
      apply hx
      apply Fin.ext
      rw [childLevel130_val]
      exact heq.symm
  · simp

private theorem sum_linear_eq_of_same_marginals130 (p : Fin 126)
    {a a' : ChildShape releasedPositiveInput p → Real}
    (ha : IsProbability a) (ha' : IsProbability a')
    (hsame : SameConstituentMarginals p a a')
    (lambdaSum : Real) (lambdaMargin : Side → Fin 5 → Real) :
    (∑ u, a' u *
        (lambdaSum + ∑ W : Side, lambdaMargin W (childLevel130 p W u))) =
      ∑ u, a u *
        (lambdaSum + ∑ W : Side, lambdaMargin W (childLevel130 p W u)) := by
  classical
  have hside : ∀ W : Side,
      (∑ u, a' u * lambdaMargin W (childLevel130 p W u)) =
        ∑ u, a u * lambdaMargin W (childLevel130 p W u) := by
    intro W
    rw [← sum_marginal_mul130 p a' W, ← sum_marginal_mul130 p a W]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hsame W x]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ha'.2, ha.2]
  apply congrArg (fun z => 1 * lambdaSum + z)
  calc
    (∑ u, ∑ W : Side, a' u * lambdaMargin W (childLevel130 p W u)) =
        ∑ W : Side, ∑ u, a' u * lambdaMargin W (childLevel130 p W u) :=
      Finset.sum_comm
    _ = ∑ W : Side, ∑ u, a u * lambdaMargin W (childLevel130 p W u) :=
      Finset.sum_congr rfl fun W _ => hside W
    _ = ∑ u, ∑ W : Side, a u * lambdaMargin W (childLevel130 p W u) :=
      Finset.sum_comm

/-- Every same-marginal probability law is bounded by the released exponential Fenchel
expression, including laws with zero coordinates. -/
theorem entropy_le_constituentFenchel130 (p : Fin 126)
    {a a' : ChildShape releasedPositiveInput p → Real}
    (ha : IsProbability a) (ha' : IsProbability a')
    (hsame : SameConstituentMarginals p a a')
    (lambdaSum : Real) (lambdaMargin : Side → Fin 5 → Real) :
    Entropy.H Finset.univ a' ≤
      constituentFenchelUpper130 p a lambdaSum lambdaMargin := by
  let linear := fun u : ChildShape releasedPositiveInput p =>
    lambdaSum + ∑ W : Side, lambdaMargin W (childLevel130 p W u)
  have h := entropy_le_fenchel130 a' linear ha'.1
  rw [sum_linear_eq_of_same_marginals130 p ha ha' hsame lambdaSum lambdaMargin] at h
  exact h

/-- Nats conversion of the paper `ChildShape` penalty, bounded directly by the same released
Fenchel expression.  The proof never divides by a parent coefficient. -/
theorem log_two_mul_constituentPenalty_le_fenchel130
    (d : ConstituentData releasedPositiveInput) (p : Fin 126) (r : Fin 6)
    (ha : IsProbability (d.alpha p r))
    (lambdaSum : Real) (lambdaMargin : Side → Fin 5 → Real) :
    Real.log 2 * constituentPenalty d p r ≤
      constituentFenchelUpper130 p (d.alpha p r) lambdaSum lambdaMargin -
        Entropy.H Finset.univ (d.alpha p r) := by
  let S : Set Real := {h : Real | ∃ a' : ChildShape releasedPositiveInput p → Real,
    IsProbability a' ∧ SameConstituentMarginals p (d.alpha p r) a' ∧ h = entropy a'}
  have hSne : S.Nonempty := by
    refine ⟨entropy (d.alpha p r), d.alpha p r, ha, ?_, rfl⟩
    intro W x
    rfl
  have hsup : sSup S ≤
      constituentFenchelUpper130 p (d.alpha p r) lambdaSum lambdaMargin / Real.log 2 := by
    apply csSup_le hSne
    intro h hh
    obtain ⟨a', ha', hsame, rfl⟩ := hh
    apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : Real) < 2))).2
    exact entropy_le_constituentFenchel130 p ha ha' hsame lambdaSum lambdaMargin
  have hmul := mul_le_mul_of_nonneg_left hsup
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le
  have halpha := Entropy.H_mul_log_two Finset.univ (d.alpha p r)
  change Real.log 2 * (sSup S - entropy (d.alpha p r)) ≤ _
  dsimp only [S] at hmul
  rw [mul_div_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < 2)))] at hmul
  have halpha' :
      Real.log 2 * entropy (d.alpha p r) = Entropy.H Finset.univ (d.alpha p r) := by
    rw [mul_comm]
    exact halpha
  nlinarith [halpha']

end OmegaBound.ADVXXZT6Round130

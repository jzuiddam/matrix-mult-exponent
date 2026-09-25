import OmegaBound.ADVXXZGeneralReleasedRetainedLegs
import OmegaBound.ADVXXZT6Round130Fenchel

/-!
# Generic Fenchel bridge for the released global penalty

The existing finite-alphabet Fenchel theorem is independent of the constituent alphabet.  This
module packages its `sSup` consequence for a global shape law, in nats, so the released global
dual values can be compared directly with `globalRegionRate`.
-/

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

/-- The finite Fenchel dual objective for a real-valued law on `Shape w`. -/
noncomputable def globalFenchelUpper {w : ℕ}
    (a : Shape w → ℝ) (linear : Shape w → ℝ) : ℝ :=
  (∑ u, Real.exp (linear u - 1)) - ∑ u, a u * linear u

/-- A shape coordinate retaining its finite alphabet type. -/
def globalShapeLevel {w : ℕ} (W : Side) (u : Shape w) : Fin (2 * w + 1) :=
  match W with
  | .X => u.1.1
  | .Y => u.1.2.1
  | .Z => u.1.2.2

@[simp] theorem globalShapeLevel_val {w : ℕ} (W : Side) (u : Shape w) :
    (globalShapeLevel W u : ℕ) = coord W u := by
  cases W <;> rfl

/-- The affine coordinate form used by a global maximum-entropy dual. -/
noncomputable def globalFenchelLinear {w : ℕ}
    (lambdaSum : ℝ) (lambdaMargin : Side → Fin (2 * w + 1) → ℝ)
    (u : Shape w) : ℝ :=
  lambdaSum + ∑ W : Side, lambdaMargin W (globalShapeLevel W u)

private theorem sum_global_marginal_mul {w : ℕ}
    (a : Shape w → ℝ) (W : Side) (lambda : Fin (2 * w + 1) → ℝ) :
    (∑ x : Fin (2 * w + 1), marginal a W x * lambda x) =
      ∑ u, a u * lambda (globalShapeLevel W u) := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single (globalShapeLevel W u)]
  · rw [if_pos]
    exact (globalShapeLevel_val W u).symm
  · intro x _ hx
    rw [if_neg]
    · simp
    · intro heq
      apply hx
      apply Fin.ext
      rw [globalShapeLevel_val]
      exact heq.symm
  · simp

private theorem sum_global_linear_eq_of_same_marginals {w : ℕ}
    {a a' : Shape w → ℝ} (ha : IsProbability a) (ha' : IsProbability a')
    (hsame : SameMarginals a a') (lambdaSum : ℝ)
    (lambdaMargin : Side → Fin (2 * w + 1) → ℝ) :
    (∑ u, a' u * globalFenchelLinear lambdaSum lambdaMargin u) =
      ∑ u, a u * globalFenchelLinear lambdaSum lambdaMargin u := by
  classical
  have hside : ∀ W : Side,
      (∑ u, a' u * lambdaMargin W (globalShapeLevel W u)) =
        ∑ u, a u * lambdaMargin W (globalShapeLevel W u) := by
    intro W
    rw [← sum_global_marginal_mul a' W, ← sum_global_marginal_mul a W]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hsame W x]
  unfold globalFenchelLinear
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ha'.2, ha.2]
  apply congrArg (fun z => 1 * lambdaSum + z)
  calc
    (∑ u, ∑ W : Side, a' u * lambdaMargin W (globalShapeLevel W u)) =
        ∑ W : Side, ∑ u, a' u * lambdaMargin W (globalShapeLevel W u) :=
      Finset.sum_comm
    _ = ∑ W : Side, ∑ u, a u * lambdaMargin W (globalShapeLevel W u) :=
      Finset.sum_congr rfl fun W _ => hside W
    _ = ∑ u, ∑ W : Side, a u * lambdaMargin W (globalShapeLevel W u) :=
      Finset.sum_comm

/-- A Fenchel dual objective bounds the global same-marginal entropy penalty in nats. -/
theorem log_two_mul_globalPenalty_le_fenchel {w : ℕ}
    (a : Shape w → ℝ) (ha : IsProbability a) (linear : Shape w → ℝ)
    (hlinear : ∀ a' : Shape w → ℝ, IsProbability a' → SameMarginals a a' →
      ∑ u, a' u * linear u = ∑ u, a u * linear u) :
    Real.log 2 * penalty a ≤
      globalFenchelUpper a linear - Entropy.H Finset.univ a := by
  let S : Set ℝ := {h : ℝ | ∃ a' : Shape w → ℝ,
    IsProbability a' ∧ SameMarginals a a' ∧ h = entropy a'}
  have hSne : S.Nonempty := by
    refine ⟨entropy a, a, ha, ?_, rfl⟩
    intro W x
    rfl
  have hsup : sSup S ≤ globalFenchelUpper a linear / Real.log 2 := by
    apply csSup_le hSne
    intro h hh
    obtain ⟨a', ha', hsame, rfl⟩ := hh
    apply (div_le_div_iff_of_pos_right
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    unfold globalFenchelUpper
    have hfenchel := OmegaBound.ADVXXZT6Round130.entropy_le_fenchel130
      a' linear ha'.1
    rw [hlinear a' ha' hsame] at hfenchel
    exact hfenchel
  have hmul := mul_le_mul_of_nonneg_left hsup
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have halpha := Entropy.H_mul_log_two Finset.univ a
  change Real.log 2 * (sSup S - entropy a) ≤ _
  dsimp only [S] at hmul
  rw [mul_div_cancel₀ _
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))] at hmul
  have halpha' : Real.log 2 * entropy a = Entropy.H Finset.univ a := by
    rw [mul_comm]
    exact halpha
  nlinarith [halpha']

/-- Packaged global penalty bound for an affine coordinate dual. -/
theorem log_two_mul_globalPenalty_le_coordinate_fenchel {w : ℕ}
    (a : Shape w → ℝ) (ha : IsProbability a) (lambdaSum : ℝ)
    (lambdaMargin : Side → Fin (2 * w + 1) → ℝ) :
    Real.log 2 * penalty a ≤
      globalFenchelUpper a (globalFenchelLinear lambdaSum lambdaMargin) -
        Entropy.H Finset.univ a := by
  apply log_two_mul_globalPenalty_le_fenchel a ha
  intro a' ha' hsame
  exact sum_global_linear_eq_of_same_marginals ha ha' hsame lambdaSum lambdaMargin

/-- The dual value is a lower bound for the nats-scaled global X-direction term. -/
theorem global_x_fenchel_value_le {w : ℕ}
    (a : Shape w → ℝ) (ha : IsProbability a) (weight : ℝ) (hweight : 0 ≤ weight)
    (W : Side) (lambdaSum : ℝ)
    (lambdaMargin : Side → Fin (2 * w + 1) → ℝ) :
    weight * (Entropy.H Finset.univ (marginal a W) + Entropy.H Finset.univ a -
      globalFenchelUpper a (globalFenchelLinear lambdaSum lambdaMargin)) ≤
      Real.log 2 * weight * (entropy (marginal a W) - penalty a) := by
  have hpen := log_two_mul_globalPenalty_le_coordinate_fenchel
    a ha lambdaSum lambdaMargin
  have hmul := mul_le_mul_of_nonneg_left hpen hweight
  have hmarg := Entropy.H_mul_log_two Finset.univ (marginal a W)
  have halpha := Entropy.H_mul_log_two Finset.univ a
  have hmarg' : Entropy.H Finset.univ (marginal a W) =
      Real.log 2 * entropy (marginal a W) := by
    calc
      _ = entropy (marginal a W) * Real.log 2 := hmarg.symm
      _ = Real.log 2 * entropy (marginal a W) := mul_comm _ _
  have halpha' : Entropy.H Finset.univ a = Real.log 2 * entropy a := by
    calc
      _ = entropy a * Real.log 2 := halpha.symm
      _ = Real.log 2 * entropy a := mul_comm _ _
  rw [hmarg', halpha']
  nlinarith

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.log_two_mul_globalPenalty_le_coordinate_fenchel

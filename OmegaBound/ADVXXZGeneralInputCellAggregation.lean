import OmegaBound.ADVXXZGeneralInputConditionedMoments
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem inputAggregation_avg_mono {Ω : Type*} [Fintype Ω]
    (hΩ : 0 < Fintype.card Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := by
  unfold avg
  have hc : 0 ≤ (Fintype.card Ω : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) hc

private theorem inputAggregation_avg_sum {Ω I : Type*}
    [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    avg (fun x => ∑ i, f i x) = ∑ i, avg (f i) := by
  unfold avg
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

private theorem inputAggregation_avg_const_mul {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f : Ω → ℝ) : avg (fun x => c * f x) = c * avg f := by
  unfold avg
  rw [← Finset.mul_sum]
  ring

private theorem inputAggregation_avg_add {Ω : Type*} [Fintype Ω]
    (f g : Ω → ℝ) : avg (fun x => f x + g x) = avg f + avg g := by
  unfold avg
  rw [Finset.sum_add_distrib]
  ring

private theorem inputAggregation_avg_const {Ω : Type*} [Fintype Ω]
    (hΩ : 0 < Fintype.card Ω) (c : ℝ) : avg (fun _ : Ω => c) = c := by
  unfold avg
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩ.ne'
  simp [hc]

private theorem inputAggregation_add_fourth_le (x y : ℝ) :
    (x + y)^4 ≤ 8 * (x^4 + y^4) := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x^2-y^2),
    sq_nonneg ((x+y)^2 - 2*(x^2+y^2))]

private theorem inputAggregation_sum_fourth_le {I : Type*} [Fintype I]
    (f : I → ℝ) :
    (∑ i, f i)^4 ≤ (Fintype.card I : ℝ)^3 * ∑ i, f i ^ 4 := by
  have habs : |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
  have hpow : |∑ i, f i|^4 ≤ (∑ i, |f i|)^4 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 4
  have hjensen : (∑ i, |f i|)^4 ≤
      (Fintype.card I : ℝ)^3 * ∑ i, |f i|^4 := by
    simpa only [Finset.card_univ, Nat.cast_pow] using
      (pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset I)) (f := fun i => |f i|)
        (fun _ _ => abs_nonneg _) 3)
  calc
    (∑ i, f i)^4 = |∑ i, f i|^4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ (∑ i, |f i|)^4 := hpow
    _ ≤ (Fintype.card I : ℝ)^3 * ∑ i, |f i|^4 := hjensen
    _ = (Fintype.card I : ℝ)^3 * ∑ i, f i^4 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← abs_pow, abs_of_nonneg (by positivity)]

/-- A finite sum of fourth-moment-controlled cell statistics remains fourth-moment
controlled after moving every corrected local centre to its product-frequency centre.
This is the abstract finite-cell aggregation used by the constituent input proof. -/
theorem avg_sum_fourth_moment_of_local
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (hΩ : 0 < Fintype.card Ω)
    (X : I → Ω → ℝ) (mu nu B D : I → ℝ)
    (hmoment : ∀ i, avg (fun x => (X i x - mu i)^4) ≤ B i)
    (hcenter : ∀ i, |mu i - nu i| ≤ D i) :
    avg (fun x => ((∑ i, X i x) - ∑ i, nu i)^4) ≤
      (Fintype.card I : ℝ)^3 *
        ∑ i, 8 * (B i + (D i)^4) := by
  have hpoint : ∀ x : Ω,
      ((∑ i, X i x) - ∑ i, nu i)^4 ≤
        (Fintype.card I : ℝ)^3 *
          ∑ i, 8 * ((X i x - mu i)^4 + (mu i - nu i)^4) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i, (X i x - nu i))^4 ≤
          (Fintype.card I : ℝ)^3 * ∑ i, (X i x - nu i)^4 :=
        inputAggregation_sum_fourth_le _
      _ ≤ (Fintype.card I : ℝ)^3 *
          ∑ i, 8 * ((X i x - mu i)^4 + (mu i - nu i)^4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        convert inputAggregation_add_fourth_le (X i x - mu i) (mu i - nu i) using 1
        ring
  calc
    avg (fun x => ((∑ i, X i x) - ∑ i, nu i)^4) ≤
        avg (fun x => (Fintype.card I : ℝ)^3 *
          ∑ i, 8 * ((X i x - mu i)^4 + (mu i - nu i)^4)) :=
      inputAggregation_avg_mono hΩ hpoint
    _ = (Fintype.card I : ℝ)^3 *
        ∑ i, 8 * (avg (fun x => (X i x - mu i)^4) + (mu i - nu i)^4) := by
      rw [inputAggregation_avg_const_mul, inputAggregation_avg_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [inputAggregation_avg_const_mul, inputAggregation_avg_add,
        inputAggregation_avg_const hΩ]
    _ ≤ (Fintype.card I : ℝ)^3 * ∑ i, 8 * (B i + (D i)^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (hmoment i)
      calc
        (mu i - nu i)^4 = |mu i - nu i|^4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ (D i)^4 := pow_le_pow_left₀ (abs_nonneg _) (hcenter i) 4

end OmegaBound.ADVXXZGeneral
end

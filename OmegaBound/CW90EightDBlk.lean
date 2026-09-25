import OmegaBound.CW90EightStrassen
import OmegaBound.CW90EightValD

/-!
# Degeneration along a substitution of variables

`Degenerates.of_sub`: if `A'` is obtained from `A` by renaming variables
(`A' x y z = A (f₁ x) (f₂ y) (f₃ z)`, no injectivity required) and `A'` degenerates to `S`, then
so does `A`.  `DDecomp.ofSub` transports a degeneration decomposition along such a substitution,
with the same weight (`DDecomp.wt_ofSub`).
-/

open Tensor3 Finset

namespace OmegaBound

namespace CW90Eight

/-! ## Reindexing sums -/

/-- Moving the innermost of four summation variables to the outside. -/
private theorem sum_move3 {A B C D M : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [AddCommMonoid M] (T : A → B → C → D → M) :
    (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, T a b c d)
      = ∑ d : D, ∑ a : A, ∑ b : B, ∑ c : C, T a b c d := by
  have h1 : ∀ a b, (∑ c : C, ∑ d : D, T a b c d) = ∑ d : D, ∑ c : C, T a b c d :=
    fun a b => Finset.sum_comm
  simp only [h1]
  have h2 : ∀ a, (∑ b : B, ∑ d : D, ∑ c : C, T a b c d)
      = ∑ d : D, ∑ b : B, ∑ c : C, T a b c d := fun a => Finset.sum_comm
  simp only [h2]
  exact Finset.sum_comm

/-! ## Degeneration pulls back along a substitution of variables -/

/-- **Degeneration pulls back along a substitution of variables.**  If `A'` is obtained from
`A` by renaming variables, and `A'` degenerates to `S`, then `A` degenerates to `S`.

No injectivity is required of the renaming, only that it produce `A'` from `A`. -/
theorem Degenerates.of_sub {F : Type*} [Field F] {X Y Z X' Y' Z' α β γ : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype α] [Fintype β] [Fintype γ]
    {A : Tensor3 F X Y Z} {A' : Tensor3 F X' Y' Z'} {S : Tensor3 F α β γ}
    (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z)
    (hsub : ∀ x y z, A' x y z = A (f₁ x) (f₂ y) (f₃ z))
    (h : Degenerates F A' S) : Degenerates F A S := by
  classical
  obtain ⟨N, A₁, A₂, A₃, hvan, hco⟩ := h
  have key : ∀ (i : α) (j : β) (k : γ),
      (∑ a : X, ∑ b : Y, ∑ c : Z,
        (∑ x : X', A₁ i x * (if a = f₁ x then 1 else 0)) *
          (∑ y : Y', A₂ j y * (if b = f₂ y then 1 else 0)) *
          (∑ z : Z', A₃ k z * (if c = f₃ z then 1 else 0)) * Polynomial.C (A a b c))
        = ∑ x : X', ∑ y : Y', ∑ z : Z',
            A₁ i x * A₂ j y * A₃ k z * Polynomial.C (A' x y z) := by
    intro i j k
    have step1 : ∀ (a : X) (b : Y) (c : Z),
        (∑ x : X', A₁ i x * (if a = f₁ x then 1 else 0)) *
            (∑ y : Y', A₂ j y * (if b = f₂ y then 1 else 0)) *
            (∑ z : Z', A₃ k z * (if c = f₃ z then 1 else 0)) * Polynomial.C (A a b c)
          = ∑ x : X', ∑ y : Y', ∑ z : Z',
              A₁ i x * A₂ j y * A₃ k z *
                ((if a = f₁ x then 1 else 0) * (if b = f₂ y then 1 else 0) *
                  (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)) := by
      intro a b c
      rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => step1 a b c]
    rw [sum_move3 (fun a b c x => ∑ y : Y', ∑ z : Z', A₁ i x * A₂ j y * A₃ k z *
      ((if a = f₁ x then 1 else 0) * (if b = f₂ y then 1 else 0) *
        (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sum_move3 (fun a b c y => ∑ z : Z', A₁ i x * A₂ j y * A₃ k z *
      ((if a = f₁ x then 1 else 0) * (if b = f₂ y then 1 else 0) *
        (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sum_move3 (fun a b c z => A₁ i x * A₂ j y * A₃ k z *
      ((if a = f₁ x then 1 else 0) * (if b = f₂ y then 1 else 0) *
        (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)))]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hinner : (∑ a : X, ∑ b : Y, ∑ c : Z,
        (if a = f₁ x then (1 : Polynomial F) else 0) * (if b = f₂ y then 1 else 0) *
          (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c))
        = 1 * 1 * 1 * Polynomial.C (A (f₁ x) (f₂ y) (f₃ z)) :=
      indicator_triple_sum A (f₁ x) (f₂ y) (f₃ z) 1 1 1
    calc (∑ a : X, ∑ b : Y, ∑ c : Z, A₁ i x * A₂ j y * A₃ k z *
            ((if a = f₁ x then (1 : Polynomial F) else 0) * (if b = f₂ y then 1 else 0) *
              (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)))
        = A₁ i x * A₂ j y * A₃ k z * ∑ a : X, ∑ b : Y, ∑ c : Z,
            ((if a = f₁ x then (1 : Polynomial F) else 0) * (if b = f₂ y then 1 else 0) *
              (if c = f₃ z then 1 else 0) * Polynomial.C (A a b c)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = A₁ i x * A₂ j y * A₃ k z * Polynomial.C (A' x y z) := by
          rw [hinner, hsub x y z]; ring
  exact ⟨N, fun i a => ∑ x : X', A₁ i x * (if a = f₁ x then 1 else 0),
    fun j b => ∑ y : Y', A₂ j y * (if b = f₂ y then 1 else 0),
    fun k c => ∑ z : Z', A₃ k z * (if c = f₃ z then 1 else 0),
    fun i j k m hm => by rw [key i j k]; exact hvan i j k m hm,
    fun i j k => by rw [key i j k]; exact hco i j k⟩

/-- A decomposition transports along a substitution of variables. -/
def DDecomp.ofSub {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] {A : Tensor3 ℚ X Y Z} {A' : Tensor3 ℚ X' Y' Z'}
    (D : DDecomp A') (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z)
    (hsub : ∀ x y z, A' x y z = A (f₁ x) (f₂ y) (f₃ z)) : DDecomp A where
  ι := D.ι
  fι := D.fι
  dι := D.dι
  ne := D.ne
  P := D.P
  Q := D.Q
  R := D.R
  fP := D.fP
  fQ := D.fQ
  fR := D.fR
  dP := D.dP
  dQ := D.dQ
  dR := D.dR
  big := D.big
  deg := Degenerates.of_sub f₁ f₂ f₃ hsub D.deg

@[simp] theorem DDecomp.wt_ofSub {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] {A : Tensor3 ℚ X Y Z} {A' : Tensor3 ℚ X' Y' Z'}
    (D : DDecomp A') (f₁ : X' → X) (f₂ : Y' → Y) (f₃ : Z' → Z)
    (hsub : ∀ x y z, A' x y z = A (f₁ x) (f₂ y) (f₃ z)) (t : ℝ) :
    (D.ofSub f₁ f₂ f₃ hsub).wt t = D.wt t := rfl

namespace BlkMM

variable {X Y Z : Type} {A : Tensor3 ℚ X Y Z} {I J K : Type} {m n p : ℕ}


end BlkMM

namespace BlkMM

variable {X Y Z : Type} {A : Tensor3 ℚ X Y Z} {I J K : Type} {m n p : ℕ}

end BlkMM

end CW90Eight

end OmegaBound

/-
Copyright (c) 2025-2026 Jeroen Zuiddam.
Released under the Apache License 2.0; see LICENSE.
3-tensors, restriction, direct sum and the matrix-multiplication tensor.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# 3-tensors, restriction, and the matrix-multiplication tensor

The tensor vocabulary of this development:

* `Tensor3 R α β γ`: a 3-tensor over `R` with index types `α`, `β`, `γ`, as a function
  `α → β → γ → R`;
* `Tensor3.act A₁ A₂ A₃ T`: the action `(A₁ ⊗ A₂ ⊗ A₃) · T` of three matrices on a tensor;
* `Tensor3.Restricts S T`, written `S ≤ₜ T`: `S` is a restriction of `T`, that is,
  `S = act A₁ A₂ A₃ T` for some matrices `A₁`, `A₂`, `A₃`;
* `Tensor3.directSum T S`, written `T ⊕ₜ S`: the direct sum of two tensors;
* `Tensor3.matMul a b c`: the matrix-multiplication tensor `⟨a,b,c⟩`;
* `Tensor3.matMul'`, the product of matrices given as functions, and `Tensor3.act_act`: acting
  by `A₁, A₂, A₃` and then by `H₁, H₂, H₃` is acting by the products `Hᵢ · Aᵢ`.
-/

/-! ## Basic Definitions -/

variable (R : Type*) [CommSemiring R]

/-- A 3-tensor over R with index sets α, β, γ -/
abbrev Tensor3 (α β γ : Type*) := α → β → γ → R

namespace Tensor3

variable {R}
variable {α β γ α' β' γ' : Type*}

section Action

variable [Fintype α] [Fintype β] [Fintype γ]

/-- The action (A₁ ⊗ A₂ ⊗ A₃) · T of three matrices on a tensor.
    The result at index (i, j, k) is ∑_{i',j',k'} A₁(i,i') A₂(j,j') A₃(k,k') T(i',j',k'). -/
def act (A₁ : α' → α → R) (A₂ : β' → β → R) (A₃ : γ' → γ → R)
    (T : Tensor3 R α β γ) : Tensor3 R α' β' γ' :=
  fun i j k => ∑ i' : α, ∑ j' : β, ∑ k' : γ, A₁ i i' * A₂ j j' * A₃ k k' * T i' j' k'

end Action

section Restriction

variable [Fintype α] [Fintype β] [Fintype γ]

/-- `S ≤ₜ T`: `S` is a restriction of `T`, that is, there exist matrices A₁, A₂, A₃
    such that S = (A₁ ⊗ A₂ ⊗ A₃) · T -/
def Restricts (S : Tensor3 R α' β' γ') (T : Tensor3 R α β γ) : Prop :=
  ∃ (A₁ : α' → α → R) (A₂ : β' → β → R) (A₃ : γ' → γ → R),
    S = act A₁ A₂ A₃ T

scoped infix:50 " ≤ₜ " => Restricts

end Restriction

section DirectSum

/-- Direct sum of two tensors. The result has format (α ⊕ α') × (β ⊕ β') × (γ ⊕ γ').
    Entries are from T when all indices are in the left component,
    from S when all are in the right component, and 0 otherwise. -/
def directSum (T : Tensor3 R α β γ) (S : Tensor3 R α' β' γ') :
    Tensor3 R (α ⊕ α') (β ⊕ β') (γ ⊕ γ') :=
  fun i j k => match i, j, k with
    | .inl a, .inl b, .inl c => T a b c
    | .inr a, .inr b, .inr c => S a b c
    | _, _, _ => 0

scoped infixl:65 " ⊕ₜ " => directSum

end DirectSum

section MatMul

/-- The matrix multiplication tensor ⟨a,b,c⟩ of format (a·b) × (b·c) × (c·a).
    Defined as ∑_{i ∈ [a]} ∑_{j ∈ [b]} ∑_{k ∈ [c]} e_{i,j} ⊗ e_{j,k} ⊗ e_{k,i}.
    This tensor encodes the bilinear map (A, B) ↦ A·B for matrix multiplication. -/
def matMul (a b c : ℕ) : Tensor3 R (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun ⟨i, j⟩ ⟨j', k⟩ ⟨k', i'⟩ => if j = j' ∧ k = k' ∧ i = i' then 1 else 0


end MatMul

end Tensor3

/-! ## Auxiliary Lemmas -/

open Tensor3

namespace Tensor3

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' α'' β'' γ'' : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [Fintype α'] [Fintype β'] [Fintype γ']
variable [Fintype α''] [Fintype β''] [Fintype γ'']

/-- Matrix multiplication for function-represented matrices -/
def matMul' (A : α → β → R) (B : β → γ → R) : α → γ → R :=
  fun i k => ∑ j : β, A i j * B j k

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Tensor action composition: acting twice is the same as acting by composed matrices.
    Mathematically: (H₁ H₂ H₃) · ((A₁ A₂ A₃) · T) = ((H₁·A₁) (H₂·A₂) (H₃·A₃)) · T -/
theorem act_act (H₁ : α → α' → R) (H₂ : β → β' → R) (H₃ : γ → γ' → R)
    (A₁ : α' → α'' → R) (A₂ : β' → β'' → R) (A₃ : γ' → γ'' → R)
    (T : Tensor3 R α'' β'' γ'') :
    act H₁ H₂ H₃ (act A₁ A₂ A₃ T) = act (matMul' H₁ A₁) (matMul' H₂ A₂) (matMul' H₃ A₃) T := by
  funext i j k
  simp only [act, matMul']
  -- After distributing, both are sums over the same 6 indices, just in different order.
  simp only [Finset.mul_sum, Finset.sum_mul]
  -- LHS: ∑ i', ∑ j', ∑ k', ∑ i'', ∑ j'', ∑ k'', f(i',j',k',i'',j'',k'')
  -- RHS: ∑ i'', ∑ j'', ∑ k'', ∑ k', ∑ j', ∑ i', g(i',j',k',i'',j'',k'')
  -- Use Finset.sum_comm to swap adjacent sum pairs repeatedly
  -- Move k' from position 3 to position 4: swap with the i'' sum
  rw [show (∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i' : α', ∑ j' : β', ∑ i'' : α'', ∑ k' : γ', ∑ j'' : β'', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i' _; apply Finset.sum_congr rfl; intro j' _;
          rw [Finset.sum_comm]]
  -- Move j' from position 2 to position 3: swap with i'' sum
  rw [show (∑ i' : α', ∑ j' : β', ∑ i'' : α'', ∑ k' : γ', ∑ j'' : β'', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i' : α', ∑ i'' : α'', ∑ j' : β', ∑ k' : γ', ∑ j'' : β'', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i' _; rw [Finset.sum_comm]]
  -- Move i' from position 1 to position 2: swap with i'' sum
  rw [Finset.sum_comm]
  -- Now: ∑ i'', ∑ i', ∑ j', ∑ k', ∑ j'', ∑ k''
  -- Move k' from position 4 to position 5: swap with j'' sum
  rw [show (∑ i'' : α'', ∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ j'' : β'', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ i' : α', ∑ j' : β', ∑ j'' : β'', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro i' _;
          apply Finset.sum_congr rfl; intro j' _; rw [Finset.sum_comm]]
  -- Move j' from position 3 to position 4: swap with j'' sum
  rw [show (∑ i'' : α'', ∑ i' : α', ∑ j' : β', ∑ j'' : β'', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ i' : α', ∑ j'' : β'', ∑ j' : β', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro i' _;
          rw [Finset.sum_comm]]
  -- Move i' from position 2 to position 5: swap with j'', then j', then k'
  rw [show (∑ i'' : α'', ∑ i' : α', ∑ j'' : β'', ∑ j' : β', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; rw [Finset.sum_comm]]
  -- Move k' from position 5 to position 6: swap with k'' sum
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ j' : β', ∑ k' : γ', ∑ k'' : γ'',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ j' : β', ∑ k'' : γ'', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          apply Finset.sum_congr rfl; intro i' _; apply Finset.sum_congr rfl; intro j' _;
          rw [Finset.sum_comm]]
  -- Move j' from position 4 to position 6: swap with k'', then k'
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ j' : β', ∑ k'' : γ'', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ k'' : γ'', ∑ j' : β', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          apply Finset.sum_congr rfl; intro i' _; rw [Finset.sum_comm]]
  -- Move i' from position 3 to position 6: swap with k'', then j', then k'
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ i' : α', ∑ k'' : γ'', ∑ j' : β', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ i' : α', ∑ j' : β', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          rw [Finset.sum_comm]]
  -- Now: ∑ i'', ∑ j'', ∑ k'', ∑ i', ∑ j', ∑ k'
  -- RHS has: ∑ i'', ∑ j'', ∑ k'', ∑ k', ∑ j', ∑ i' (inner three reversed)
  -- Swap i' and k': move i' from position 4 to position 6
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ i' : α', ∑ j' : β', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ j' : β', ∑ i' : α', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          apply Finset.sum_congr rfl; intro k'' _; rw [Finset.sum_comm]]
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ j' : β', ∑ i' : α', ∑ k' : γ',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ j' : β', ∑ k' : γ', ∑ i' : α',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          apply Finset.sum_congr rfl; intro k'' _; apply Finset.sum_congr rfl; intro j' _;
          rw [Finset.sum_comm]]
  -- Now swap j' and k': move j' from position 4 to position 5
  rw [show (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ j' : β', ∑ k' : γ', ∑ i' : α',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k'')) =
          (∑ i'' : α'', ∑ j'' : β'', ∑ k'' : γ'', ∑ k' : γ', ∑ j' : β', ∑ i' : α',
           H₁ i i' * H₂ j j' * H₃ k k' * (A₁ i' i'' * A₂ j' j'' * A₃ k' k'' * T i'' j'' k''))
       by apply Finset.sum_congr rfl; intro i'' _; apply Finset.sum_congr rfl; intro j'' _;
          apply Finset.sum_congr rfl; intro k'' _; rw [Finset.sum_comm]]
  -- Now we have ∑ i'', ∑ j'', ∑ k'', ∑ k', ∑ j', ∑ i' matching the RHS structure
  -- Show the summands are equal by ring
  congr 1; funext i''; congr 1; funext j''; congr 1; funext k''
  congr 1; funext k'; congr 1; funext j'; congr 1; funext i'; ring

end Tensor3

open Tensor3 in
/-- Unfolds `directSum` and `matMul` by `simp`, so that Lean generates their equation lemmas in this
file rather than on first use in a later file; the proofs of the later files then elaborate with
the same auxiliary names as in the development build. -/
private theorem directSum_matMul_equations (T : Tensor3 ℕ (Fin 1) (Fin 1) (Fin 1)) (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    (T ⊕ₜ T) (.inl 0) (.inl 0) (.inl 0) = T 0 0 0 ∧ (T ⊕ₜ T) (.inr 0) (.inr 0) (.inr 0) = T 0 0 0 ∧
      (T ⊕ₜ T) (.inl 0) (.inr 0) (.inr 0) = 0 ∧ matMul (R := ℕ) a b c (i, j) (j, k) (k, i) = 1 := by
  simp [directSum, matMul]

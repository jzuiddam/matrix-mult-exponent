import OmegaBound.Basic

/-!
# Tensor product and monotonicity

Definition of the tensor product (Kronecker product) of 3-tensors and
proof that restriction is monotone under tensor product:
  S ≤ₜ T → S ⊗ U ≤ₜ T ⊗ U.

## Main results

* `tensorProd`: tensor product of two 3-tensors
* `Restricts.tensorProd_right`: S ≤ₜ T → tensorProd S U ≤ₜ tensorProd T U
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' α₁ β₁ γ₁ : Type*}

/-- Tensor product (Kronecker product) of two 3-tensors.
    The result has product index sets: (α × α') × (β × β') × (γ × γ'). -/
def tensorProd (T : Tensor3 R α β γ) (S : Tensor3 R α' β' γ') :
    Tensor3 R (α × α') (β × β') (γ × γ') :=
  fun ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ => T a b c * S a' b' c'

/-- Tensor product is monotone in the first argument:
    S ≤ₜ T → tensorProd S U ≤ₜ tensorProd T U.

Construction: Kronecker product of restriction matrices with identity:
  B₁(a₁,a')(a,a'') = A₁ a₁ a * δ(a',a'')
  B₂(b₁,b')(b,b'') = A₂ b₁ b * δ(b',b'')
  B₃(c₁,c')(c,c'') = A₃ c₁ c * δ(c',c'') -/
theorem Restricts.tensorProd_right
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype α'] [Fintype β'] [Fintype γ']
    [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']
    {S : Tensor3 R α₁ β₁ γ₁} {T : Tensor3 R α β γ}
    (h : S ≤ₜ T) (U : Tensor3 R α' β' γ') :
    tensorProd S U ≤ₜ tensorProd T U := by
  obtain ⟨A₁, A₂, A₃, hS⟩ := h
  subst hS
  refine ⟨
    fun ⟨a₁, a'⟩ ⟨a, a''⟩ => A₁ a₁ a * if a' = a'' then 1 else 0,
    fun ⟨b₁, b'⟩ ⟨b, b''⟩ => A₂ b₁ b * if b' = b'' then 1 else 0,
    fun ⟨c₁, c'⟩ ⟨c, c''⟩ => A₃ c₁ c * if c' = c'' then 1 else 0,
    ?_⟩
  funext ⟨a₁, a₀⟩ ⟨b₁, b₀⟩ ⟨c₁, c₀⟩
  simp only [act, tensorProd, Fintype.sum_prod_type]
  -- Push ite through multiplication in both directions, collapse δ-sums
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Distribute U a₀ b₀ c₀ into the sum
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  ring

end OmegaBound

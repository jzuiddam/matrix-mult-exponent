import OmegaBound.Basic

/-!
# Mode permutation for matrix multiplication tensors

Cyclic permutation of the three modes of a tensor.

## Main results

* `cycleTensor`: the mode rotation `(α,β,γ) ↦ (β,γ,α)`
* `matMul_cycle`: rotating `⟨a,b,c⟩` gives `⟨b,c,a⟩`
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-! ## Cyclic permutation -/

/-- Cyclic permutation of tensor modes: (α,β,γ) ↦ (β,γ,α). -/
def cycleTensor (T : Tensor3 R α β γ) : Tensor3 R β γ α :=
  fun b c a => T a b c

private lemma matMul_ite_cycle (j' j : Fin b) (k k' : Fin c) (i' i : Fin a) :
    (if j' = j ∧ k = k' ∧ i' = i then (1 : R) else 0) =
    if k = k' ∧ i = i' ∧ j = j' then 1 else 0 := by
  have : (j' = j ∧ k = k' ∧ i' = i) ↔ (k = k' ∧ i = i' ∧ j = j') :=
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h3.symm, h1.symm⟩,
     fun ⟨h1, h2, h3⟩ => ⟨h3.symm, h1, h2.symm⟩⟩
  simp only [this]

/-- matMul is invariant under cyclic permutation of its parameters. -/
lemma matMul_cycle (a b c : ℕ) :
    cycleTensor (matMul (R := R) a b c) = matMul b c a := by
  funext ⟨j, k⟩ ⟨k', i⟩ ⟨i', j'⟩
  simp only [cycleTensor, matMul]
  exact matMul_ite_cycle j' j k k' i' i

end OmegaBound

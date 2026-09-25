import OmegaBound.Tensor.Basic

/-!
# Basic infrastructure for matrix multiplication tensor restriction proofs

Imports the tensor vocabulary of `OmegaBound.Tensor.Basic` and adds transitivity of restriction
(`Tensor3.Restricts.trans`).
-/

open Tensor3

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-! ## Restriction helpers -/

/-- Transitivity of tensor restriction. -/
theorem Tensor3.Restricts.trans
    [Fintype α'] [Fintype β'] [Fintype γ']
    {α'' β'' γ'' : Type*} [Fintype α''] [Fintype β''] [Fintype γ'']
    {S : Tensor3 R α β γ} {T : Tensor3 R α' β' γ'} {U : Tensor3 R α'' β'' γ''}
    (hST : S ≤ₜ T) (hTU : T ≤ₜ U) : S ≤ₜ U := by
  obtain ⟨A₁, A₂, A₃, hS⟩ := hST
  obtain ⟨B₁, B₂, B₃, hT⟩ := hTU
  exact ⟨Tensor3.matMul' A₁ B₁, Tensor3.matMul' A₂ B₂, Tensor3.matMul' A₃ B₃,
    by rw [hS, hT, act_act]⟩

end OmegaBound

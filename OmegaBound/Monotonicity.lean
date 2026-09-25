import OmegaBound.Basic

/-!
# Direct sum monotonicity

If S ≤ₜ T then S ⊕ₜ U ≤ₜ T ⊕ₜ U.

Construction: extend the restriction matrices A₁, A₂, A₃ to block-diagonal
matrices with identity on the U-indices.
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable {α' β' γ' : Type*}
variable {α'' β'' γ'' : Type*} [Fintype α''] [Fintype β''] [Fintype γ'']

/-- Direct sum is monotone in the first argument: S ≤ₜ T → S ⊕ₜ U ≤ₜ T ⊕ₜ U. -/
theorem Restricts.directSum_right
    {S : Tensor3 R α' β' γ'} {T : Tensor3 R α β γ} {U : Tensor3 R α'' β'' γ''}
    (h : S ≤ₜ T) : (S ⊕ₜ U) ≤ₜ (T ⊕ₜ U) := by
  classical
  obtain ⟨A₁, A₂, A₃, hS⟩ := h
  refine ⟨
    Sum.elim (fun a' => Sum.elim (A₁ a') (fun _ => 0))
             (fun a'' => Sum.elim (fun _ => 0) (fun a₂ => if a'' = a₂ then 1 else 0)),
    Sum.elim (fun b' => Sum.elim (A₂ b') (fun _ => 0))
             (fun b'' => Sum.elim (fun _ => 0) (fun b₂ => if b'' = b₂ then 1 else 0)),
    Sum.elim (fun c' => Sum.elim (A₃ c') (fun _ => 0))
             (fun c'' => Sum.elim (fun _ => 0) (fun c₂ => if c'' = c₂ then 1 else 0)),
    ?_⟩
  subst hS
  funext i j k
  match i, j, k with
  | .inl i, .inl j, .inl k =>
    simp [act, directSum, Fintype.sum_sum_type]
  | .inr i', .inr j', .inr k' =>
    simp [act, directSum, Fintype.sum_sum_type]
  | .inl _, .inl _, .inr _ | .inl _, .inr _, .inl _ | .inl _, .inr _, .inr _
  | .inr _, .inl _, .inl _ | .inr _, .inl _, .inr _ | .inr _, .inr _, .inl _ =>
    simp [act, directSum, Fintype.sum_sum_type]

end OmegaBound

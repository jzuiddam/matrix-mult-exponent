import OmegaBound.Basic

/-!
# Zero-padding restriction

If `a' ≤ a`, `b' ≤ b`, `c' ≤ c`, then `⟨a',b',c'⟩ ≤ₜ ⟨a,b,c⟩`.
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-- Acting with delta-function matrices composes the tensor with the given functions. -/
theorem act_delta [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f₁ : α' → α) (f₂ : β' → β) (f₃ : γ' → γ)
    (T : Tensor3 R α β γ) (a : α') (b : β') (c : γ') :
    act (fun a' x => if f₁ a' = x then 1 else 0)
        (fun b' y => if f₂ b' = y then 1 else 0)
        (fun c' z => if f₃ c' = z then 1 else 0) T a b c =
    T (f₁ a) (f₂ b) (f₃ c) := by
  simp only [act, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (f₁ a)]
  · simp only [if_true]
    rw [Finset.sum_eq_single (f₂ b)]
    · simp only [if_true]
      rw [Finset.sum_eq_single (f₃ c)]
      · simp
      · intro x _ hx; simp [Ne.symm hx]
      · simp
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  · intro x _ hx; simp [Ne.symm hx]
  · simp

/-- Zero-padding: ⟨a',b',c'⟩ is a restriction of ⟨a,b,c⟩ when dimensions are ≤. -/
theorem matMul_restricts_of_le (a' b' c' a b c : ℕ)
    (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    (Tensor3.matMul (R := R) a' b' c') ≤ₜ (Tensor3.matMul (R := R) a b c) := by
  let f₁ : Fin a' × Fin b' → Fin a × Fin b :=
    fun ⟨i, j⟩ => (Fin.castLE ha i, Fin.castLE hb j)
  let f₂ : Fin b' × Fin c' → Fin b × Fin c :=
    fun ⟨j, k⟩ => (Fin.castLE hb j, Fin.castLE hc k)
  let f₃ : Fin c' × Fin a' → Fin c × Fin a :=
    fun ⟨k, i⟩ => (Fin.castLE hc k, Fin.castLE ha i)
  refine ⟨fun p q => if f₁ p = q then 1 else 0,
          fun p q => if f₂ p = q then 1 else 0,
          fun p q => if f₃ p = q then 1 else 0, ?_⟩
  funext ⟨i', j'⟩ ⟨j'₂, k'⟩ ⟨k'₂, i'₂⟩
  rw [act_delta f₁ f₂ f₃]
  simp only [f₁, f₂, f₃, matMul, Fin.castLE_inj]

end OmegaBound

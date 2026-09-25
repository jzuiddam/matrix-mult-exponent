import OmegaBound.Rank
import OmegaBound.Omega
import OmegaBound.ModePermutation

/-!
# Rectangular matrix multiplication and the exponent

A rank bound for a *rectangular* matrix multiplication tensor
`⟨a,b,c⟩` bounds `ω`.  The mechanism is that the three cyclic rotations multiply to a
square format,

  `⟨a,b,c⟩ ⊗ ⟨b,c,a⟩ ⊗ ⟨c,a,b⟩ ≥ ⟨abc,abc,abc⟩`,

and each rotation has the same rank as `⟨a,b,c⟩` because the identity tensor is
invariant under cyclic permutation of its three modes.

## Main results

* `rankLE_iff` — rank in the "sum of `r` rank-one terms" form
* `RankLE.cycle` — rank is invariant under cyclic permutation of the modes
* `RankLE.matMul_rect` — `R(⟨a,b,c⟩) ≤ r` implies `R(⟨abc,abc,abc⟩) ≤ r³`
* `omegaMM_le_logb_rect` — hence `ω ≤ 3 · log_{abc} r`
-/

open Tensor3 Finset

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-! ## Rank as a sum of rank-one terms -/

/-- Acting on the identity tensor collapses the triple sum to a diagonal sum. -/
theorem act_identity (r : ℕ) (A₁ : α' → Fin r → R) (A₂ : β' → Fin r → R)
    (A₃ : γ' → Fin r → R) (i : α') (j : β') (k : γ') :
    act A₁ A₂ A₃ (identity R r) i j k = ∑ ℓ : Fin r, A₁ i ℓ * A₂ j ℓ * A₃ k ℓ := by
  simp only [act, identity, mul_ite, mul_one, mul_zero, ite_and]
  simp only [← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `RankLE T r` unfolded: `T` is a sum of `r` rank-one tensors. -/
theorem rankLE_iff {T : Tensor3 R α β γ} {r : ℕ} :
    RankLE T r ↔ ∃ (A₁ : α → Fin r → R) (A₂ : β → Fin r → R) (A₃ : γ → Fin r → R),
      ∀ i j k, T i j k = ∑ ℓ : Fin r, A₁ i ℓ * A₂ j ℓ * A₃ k ℓ := by
  constructor
  · rintro ⟨A₁, A₂, A₃, hT⟩
    exact ⟨A₁, A₂, A₃, fun i j k => by rw [hT]; exact act_identity r A₁ A₂ A₃ i j k⟩
  · rintro ⟨A₁, A₂, A₃, hT⟩
    refine ⟨A₁, A₂, A₃, ?_⟩
    funext i j k
    rw [hT, act_identity]

/-! ## Cyclic invariance -/

/-- **Rank is invariant under cyclic permutation of the three modes.** -/
theorem RankLE.cycle {T : Tensor3 R α β γ} {r : ℕ} (h : RankLE T r) :
    RankLE (cycleTensor T) r := by
  rw [rankLE_iff] at h ⊢
  obtain ⟨A₁, A₂, A₃, hT⟩ := h
  refine ⟨A₂, A₃, A₁, fun b c a => ?_⟩
  show T a b c = _
  rw [hT]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- Transporting a rank bound along equalities of the format. -/
theorem RankLE.congr_matMul {a b c a' b' c' r : ℕ}
    (h : RankLE (Tensor3.matMul (R := R) a b c) r)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    RankLE (Tensor3.matMul (R := R) a' b' c') r := by
  subst ha; subst hb; subst hc; exact h

/-- The cyclic rotation of a matrix multiplication tensor has the same rank. -/
theorem RankLE.matMul_cyc {a b c r : ℕ}
    (h : RankLE (Tensor3.matMul (R := R) a b c) r) :
    RankLE (Tensor3.matMul (R := R) b c a) r := by
  have := h.cycle
  rwa [matMul_cycle] at this

/-! ## The rectangular power rule -/

/-- A rank bound for a rectangular format gives one for the square format
obtained by multiplying the three dimensions: `R(⟨a,b,c⟩) ≤ r` implies
`R(⟨abc,abc,abc⟩) ≤ r³`. -/
theorem RankLE.matMul_rect {a b c r : ℕ}
    (h : RankLE (Tensor3.matMul (R := R) a b c) r) :
    RankLE (Tensor3.matMul (R := R) (a * b * c) (a * b * c) (a * b * c)) (r ^ 3) := by
  have h2 : RankLE (Tensor3.matMul (R := R) b c a) r := h.matMul_cyc
  have h3 : RankLE (Tensor3.matMul (R := R) c a b) r := h2.matMul_cyc
  have h12 : RankLE (Tensor3.matMul (R := R) (a * b) (b * c) (c * a)) (r * r) :=
    OmegaBound.RankLE.mono (matMul_restricts_tensorProd a b c b c a) (h.tensorProd h2)
  have h123 : RankLE (Tensor3.matMul (R := R)
      (a * b * c) (b * c * a) (c * a * b)) (r * r * r) :=
    OmegaBound.RankLE.mono (matMul_restricts_tensorProd (a * b) (b * c) (c * a) c a b)
      (h12.tensorProd h3)
  have := h123.congr_matMul (a' := a * b * c) (b' := a * b * c) (c' := a * b * c)
    rfl (by ring) (by ring)
  simpa [pow_succ, mul_assoc] using this

/-! ## The exponent bound -/

/-- **`ω ≤ 3 · log_{abc} r` from a rectangular rank decomposition.** -/
theorem omegaMM_le_logb_rect [Nontrivial R] {a b c r : ℕ} (habc : 2 ≤ a * b * c)
    (h : RankLE (Tensor3.matMul (R := R) a b c) r) :
    omegaMM R ≤ 3 * Real.logb (a * b * c) r := by
  have hmain := omegaMM_le_logb (R := R) (a := a * b * c) (r := r ^ 3) habc h.matMul_rect
  have hcast : ((r ^ 3 : ℕ) : ℝ) = (r : ℝ) ^ (3 : ℕ) := by push_cast; ring
  rw [hcast, Real.logb_pow] at hmain
  simpa using hmain

end OmegaBound

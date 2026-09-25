import OmegaBound.BlockDiag
import OmegaBound.BorderRank
import OmegaBound.Omega
import OmegaBound.Rectangular

/-!
# Elementary lemmas for the asymptotic sum inequality

`matMul_congr_le` transports a restriction along equalities of the format; `log_le_two_sqrt` and
`rpow_pow_comm` are real estimates; `exists_dominant_type` is the counting step: among the `N+1`
types of a binomial expansion one carries at least a `1/(N+1)` fraction of the total weight.
-/

open Tensor3 Finset

namespace OmegaBound

/-! ## Transport along equalities of the format -/

theorem matMul_congr_le {R : Type*} [CommSemiring R] {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] {a b c a' b' c' : ℕ} {X : Tensor3 R α β γ}
    (h : Tensor3.matMul (R := R) a b c ≤ₜ X) (ha : a = a') (hb : b = b') (hc : c = c') :
    Tensor3.matMul (R := R) a' b' c' ≤ₜ X := by
  subst ha; subst hb; subst hc; exact h

/-! ## Elementary estimates -/

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h1
  linarith

lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (t : ℝ) :
    (x ^ n : ℝ) ^ t = (x ^ t) ^ n := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_natCast (x ^ t) n, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx, mul_comm]

/-- **The counting step.**  Among the `N+1` types, one carries at least a `1/(N+1)`
fraction of the total weight — by the binomial theorem, no Stirling estimate needed. -/
lemma exists_dominant_type (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (N : ℕ) :
    ∃ j, j ≤ N ∧ (q₁ + q₂) ^ N / ((N : ℝ) + 1)
      ≤ (N.choose j : ℝ) * (q₁ ^ j * q₂ ^ (N - j)) := by
  have hbin : (q₁ + q₂) ^ N
      = ∑ j ∈ Finset.range (N + 1), q₁ ^ j * q₂ ^ (N - j) * (N.choose j : ℝ) :=
    add_pow q₁ q₂ N
  have hconst : ∑ _j ∈ Finset.range (N + 1), (q₁ + q₂) ^ N / ((N : ℝ) + 1)
      = (q₁ + q₂) ^ N := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  obtain ⟨j, hjmem, hj⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_succ)
    (f := fun _ => (q₁ + q₂) ^ N / ((N : ℝ) + 1))
    (g := fun j => q₁ ^ j * q₂ ^ (N - j) * (N.choose j : ℝ))
    (by rw [hconst, hbin])
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem), by
    calc (q₁ + q₂) ^ N / ((N : ℝ) + 1) ≤ q₁ ^ j * q₂ ^ (N - j) * (N.choose j : ℝ) := hj
      _ = (N.choose j : ℝ) * (q₁ ^ j * q₂ ^ (N - j)) := by ring⟩

end OmegaBound

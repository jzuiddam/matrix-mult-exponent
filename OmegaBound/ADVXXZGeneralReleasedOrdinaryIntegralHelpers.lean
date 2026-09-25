import OmegaBound.ADVXXZGeneralReleasedOrdinaryCertificate

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem integral_nat_mul_prob {ι : Type*} [Fintype ι]
    (scale mass : ℕ) (P : RatDist ι) (i : ι)
    (hdiv : P.den ∣ scale) :
    integral ((scale : ℚ) * mass * P.prob i) := by
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨k * mass * P.num i, ?_⟩
  rw [RatDist.prob]
  push_cast
  field_simp [P.den_ne_zero]

theorem integral_nat_mul_two_probs {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (scale mass : ℕ) (P : RatDist ι) (i : ι)
    (Q : RatDist κ) (j : κ)
    (hdiv : P.den * Q.den ∣ scale) :
    integral ((scale : ℚ) * mass * P.prob i * Q.prob j) := by
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨k * mass * P.num i * Q.num j, ?_⟩
  rw [RatDist.prob, RatDist.prob]
  push_cast
  field_simp [P.den_ne_zero, Q.den_ne_zero]

theorem integral_nat_mul_four_probs {ι κ ν ξ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ξ]
    (scale mass : ℕ) (P : RatDist ι) (i : ι)
    (Q : RatDist κ) (j : κ) (R : RatDist ν) (k : ν)
    (S : RatDist ξ) (l : ξ)
    (hdiv : P.den * Q.den * R.den * S.den ∣ scale) :
    integral ((scale : ℚ) * mass * P.prob i * Q.prob j *
      R.prob k * S.prob l) := by
  obtain ⟨a, rfl⟩ := hdiv
  refine ⟨a * mass * P.num i * Q.num j * R.num k * S.num l, ?_⟩
  rw [RatDist.prob, RatDist.prob, RatDist.prob, RatDist.prob]
  push_cast
  field_simp [P.den_ne_zero, Q.den_ne_zero, R.den_ne_zero, S.den_ne_zero]

end OmegaBound.ADVXXZGeneral

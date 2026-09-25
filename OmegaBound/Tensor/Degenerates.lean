/-
Copyright (c) 2026 Jeroen Zuiddam.
Released under the Apache License 2.0; see LICENSE.
Polynomial degenerations of tensors.
-/
import OmegaBound.Tensor.Identity
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial degenerations of tensors

`Tensor3.Degenerates T S`: `S` is a degeneration of `T`, that is, `S` is a polynomial coefficient
of a restriction of `T` by polynomial matrices, the cleared-denominators form of
[KMZ23, Definition 5.1]; see [KMZ23, Section 5] for border subrank and the lower semicontinuity
of geometric rank.

## References

* [KMZ23] Kopparty, Moshkovitz, Zuiddam. "Geometric Rank of Tensors and Subrank of
  Matrix Multiplication." Discrete Analysis 2023:1. Section 5.
* [BCS97] Bürgisser, Clausen, Shokrollahi. Algebraic Complexity Theory. Theorem 20.24.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Tensor3

variable {R : Type*} [CommSemiring R]
variable {α β γ : Type*} [instFA : Fintype α] [instFB : Fintype β] [instFG : Fintype γ]
variable [instDA : DecidableEq α] [instDB : DecidableEq β] [instDC : DecidableEq γ]

/-! ### Degenerations -/

section BorderSubrankBound

variable (F : Type*) [Field F]

/-- A tensor T degenerates to S (written S ≤_degen T) if S arises as a polynomial
    coefficient of a restriction of T.

    Algebraic formulation (cleared denominators): there exist polynomial matrices
    A₁(ε), A₂(ε), A₃(ε) with entries in F[ε] and N ∈ ℕ such that the N-th
    polynomial coefficient of act(A(ε))(T) equals S:

      coeff_N(∑_{a,b,c} A₁(ε)(i,a) · A₂(ε)(j,b) · A₃(ε)(k,c) · T(a,b,c)) = S(i,j,k)

    The matrices A₁, A₂, A₃ may be rectangular (different source and target
    index types). When the index types are the same, this is equivalent to the
    orbit closure condition: S ∈ cl(GL · T) [Bürgisser et al., Theorem 20.24].

    References: [KMZ23] Definition 5.1 (cleared denominators version). -/
def Degenerates {α' β' γ' : Type*} [Fintype α'] [Fintype β'] [Fintype γ']
    (T : Tensor3 F α β γ) (S : Tensor3 F α' β' γ') : Prop :=
  ∃ (N : ℕ)
    (A₁ : α' → α → Polynomial F) (A₂ : β' → β → Polynomial F)
    (A₃ : γ' → γ → Polynomial F),
    -- Lower coefficients vanish (cleared-denominator condition from the paper)
    (∀ i j k, ∀ m : ℕ, m < N →
      (∑ a : α, ∑ b : β, ∑ c : γ,
        A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)).coeff m = 0) ∧
    -- The N-th coefficient equals S
    (∀ i j k,
      (∑ a : α, ∑ b : β, ∑ c : γ,
        A₁ i a * A₂ j b * A₃ k c * Polynomial.C (T a b c)).coeff N =
      S i j k)

end BorderSubrankBound

end Tensor3

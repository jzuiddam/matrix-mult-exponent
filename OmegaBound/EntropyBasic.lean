import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

/-!
# Shannon entropy of a finite probability vector

The laser method of VXXZ24/ADVXXZ is stated throughout in entropy, so this file supplies
the definition and the handful of facts the counting layer (`EntropyCount`) and the
max-entropy step need.

## What Mathlib already provides, and what it does not

Mathlib has `Real.negMulLog x = -x * log x` (`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`)
together with its continuity, derivatives, and **strict concavity** on `Set.Ici 0`; and it has
`Real.log_le_sub_one_of_pos`, which is the engine of Gibbs' inequality.  It does **not** have the
Shannon entropy of a discrete distribution in any form: everything under
`Mathlib.InformationTheory` is either `Hamming` distance or the measure-theoretic
Kullback–Leibler divergence `klDiv` of two measures, and everything named `entropy` under
`Mathlib.Dynamics` is topological entropy of a dynamical system.  So `H` below is new, but every
analytic input to it is Mathlib's.

## Conventions

* `H s p = ∑ i ∈ s, negMulLog (p i)` is in **nats**; `H₂ = H / log 2` is in **bits**.  The laser
  method is usually written base `2` (`binom(N; αN) = 2^{N(H(α)±o(1))}`); the natural-log form is
  the one that composes with `Real.exp`, so both are provided and `EntropyCount` proves the
  counting bounds in both.
* `Real.log 0 = 0`, so a zero coordinate contributes `0` to `H` — the correct value, and the
  same convention that makes `0 ^ 0 = 1` in `ℕ` the right normalisation for the multinomial
  bounds.  See the note at the head of `IntervalXLogX` on why this is right for the right
  reason.
* `p` is *never* assumed to be a probability vector in the definition; each lemma states the
  hypotheses it needs.  This matters because the empirical distribution of a count vector is
  only a probability vector once `N > 0`.

## Main results

* `H`, `H₂` — the definitions.
* `H_nonneg` — `0 ≤ H s p` for `p` taking values in `[0,1]`.
* `H_le_sum_neg_mul_log` — **Gibbs' inequality** `H(p) ≤ -∑ p log q`, the first-order
  optimality statement.
* `H_le_log_card` — `H(p) ≤ log |s|`, with `H_uniform` showing the bound is attained.
* `H_le_H_of_log_eq_add` — **max entropy in an exponential family**: if `log q` is affine in a
  statistic `g` and `p` has the same `g`-average as `q`, then `H(p) ≤ H(q)`.  This is the
  characterisation "the maximiser over a marginal polytope is the member of the exponential
  family with those marginals", and it is what the product-form weight
  `α_{IJK} ∝ u_I u_J u_K` of the laser method is an instance of.
* `exists_isMaxOn_H_stdSimplex`, `exists_isMaxOn_H_marginal` — **existence** of a maximiser on
  the simplex and on a marginal polytope, by compactness.
-/

open Finset

namespace OmegaBound

namespace Entropy

variable {ι : Type*}

/-! ## The definition -/

/-- **Shannon entropy in nats**: `H s p = -∑_{i ∈ s} p i · log (p i)`.

No hypothesis is imposed on `p`; the lemmas below state what they need.  With Mathlib's
`Real.log 0 = 0` a vanishing coordinate contributes `0`, which is the correct entropy value. -/
noncomputable def H (s : Finset ι) (p : ι → ℝ) : ℝ := ∑ i ∈ s, Real.negMulLog (p i)

/-- **Shannon entropy in bits**, `H₂ = H / log 2`.  This is the `H` of the statement
`binom(N; α₁N, …, α_sN) = 2^{N(H(α) ± o(1))}`. -/
noncomputable def H₂ (s : Finset ι) (p : ι → ℝ) : ℝ := H s p / Real.log 2

/-- Pointwise form of Mathlib's `Real.negMulLog_eq_neg`, which is an equation of *functions*
and so cannot be `rw`-applied to a value. -/
theorem negMulLog_eq (x : ℝ) : Real.negMulLog x = -(x * Real.log x) := neg_mul _ _

theorem H_def (s : Finset ι) (p : ι → ℝ) : H s p = ∑ i ∈ s, Real.negMulLog (p i) := rfl

theorem H₂_def (s : Finset ι) (p : ι → ℝ) : H₂ s p = H s p / Real.log 2 := rfl

/-- `H` written out with `log`, the form the counting layer manipulates. -/
theorem H_eq_neg_sum (s : Finset ι) (p : ι → ℝ) :
    H s p = -∑ i ∈ s, p i * Real.log (p i) := by
  rw [H, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => negMulLog_eq _

theorem H_mul_log_two (s : Finset ι) (p : ι → ℝ) : H₂ s p * Real.log 2 = H s p := by
  rw [H₂, div_mul_cancel₀]
  exact ne_of_gt (Real.log_pos (by norm_num))

@[simp] theorem H_empty (p : ι → ℝ) : H (∅ : Finset ι) p = 0 := Finset.sum_empty

theorem H_cons {a : ι} {s : Finset ι} (h : a ∉ s) (p : ι → ℝ) :
    H (Finset.cons a s h) p = Real.negMulLog (p a) + H s p := Finset.sum_cons _

theorem H_congr {s : Finset ι} {p q : ι → ℝ} (h : ∀ i ∈ s, p i = q i) : H s p = H s q :=
  Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-- Entropy is nonnegative on `[0,1]`-valued vectors — in particular on probability vectors. -/
theorem H_nonneg {s : Finset ι} {p : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) :
    0 ≤ H s p :=
  Finset.sum_nonneg fun i hi => Real.negMulLog_nonneg (h0 i hi) (h1 i hi)

/-- The uniform distribution on `s` has entropy `log |s|`. -/
theorem H_uniform {s : Finset ι} (hs : s.Nonempty) :
    H s (fun _ => (s.card : ℝ)⁻¹) = Real.log s.card := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  rw [H, Finset.sum_const, nsmul_eq_mul, negMulLog_eq, Real.log_inv]
  field_simp

/-! ## Gibbs' inequality -/

/-- **Gibbs' inequality.**  For a probability vector `p` and a strictly positive subprobability
vector `q` on `s`, `H(p) ≤ -∑ p log q`, with equality exactly at `p = q`.

This is the first-order optimality statement of the max-entropy problem: `-∑ p log q` is linear
in `p`, so the inequality says that the concave function `H` lies below its tangent plane at `q`.

Strict positivity of `q` is not decorative: with Mathlib's `log 0 = 0` the statement is *false*
for `q` having a zero coordinate where `p` does not (take `s = {0,1}`, `p = (½,½)`,
`q = (1,0)`: the right-hand side is `0 < log 2`). -/
theorem H_le_sum_neg_mul_log {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hp1 : ∑ i ∈ s, p i = 1) (hq1 : ∑ i ∈ s, q i ≤ 1) :
    H s p ≤ ∑ i ∈ s, -(p i * Real.log (q i)) := by
  have key : ∀ i ∈ s, Real.negMulLog (p i) + p i * Real.log (q i) ≤ q i - p i := by
    intro i hi
    have hqi := hq i hi
    rcases eq_or_lt_of_le (hp i hi) with h0 | h0
    · rw [← h0]
      simp only [Real.negMulLog_zero, zero_mul, add_zero, sub_zero]
      linarith
    · have hlog : Real.log (q i) - Real.log (p i) ≤ q i / p i - 1 := by
        have h := Real.log_le_sub_one_of_pos (div_pos hqi h0)
        rwa [Real.log_div (ne_of_gt hqi) (ne_of_gt h0)] at h
      calc Real.negMulLog (p i) + p i * Real.log (q i)
          = p i * (Real.log (q i) - Real.log (p i)) := by
            rw [negMulLog_eq]; ring
        _ ≤ p i * (q i / p i - 1) := mul_le_mul_of_nonneg_left hlog h0.le
        _ = q i - p i := by field_simp
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp1] at hsum
  rw [Finset.sum_neg_distrib, H]
  linarith

/-- **The entropy of a probability vector on `s` is at most `log |s|`.** -/
theorem H_le_log_card {s : Finset ι} {p : ι → ℝ} (hs : s.Nonempty)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) :
    H s p ≤ Real.log s.card := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hq1 : ∑ _i ∈ s, ((s.card : ℝ))⁻¹ ≤ 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  have h := H_le_sum_neg_mul_log (q := fun _ => ((s.card : ℝ))⁻¹) hp
    (fun _ _ => by positivity) hp1 hq1
  refine h.trans (le_of_eq ?_)
  have : ∀ i ∈ s, -(p i * Real.log (((s.card : ℝ))⁻¹)) = p i * Real.log s.card := by
    intro i _
    rw [Real.log_inv]; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hp1, one_mul]

/-! ## Max entropy in an exponential family -/

/-- **The max-entropy characterisation.**  Suppose `q` is a strictly positive probability vector
whose log is affine in a statistic `g`, `log (q i) = c + g i` — i.e. `q` lies in the exponential
family generated by `g` — and `p` is a probability vector with the same `g`-average as `q`.
Then `H(p) ≤ H(q)`.

Every "the symmetric type is optimal for its marginals" claim in the laser method is this lemma:
the marginal constraints are exactly the statement that `p` and `q` have the same `g`-averages
for the coordinate-indicator statistics `g`, and a product-form weight `α_{IJK} ∝ u_I u_J u_K`
has `log α` affine in those statistics.  Compare
`Entropy.multinomial_mul_prod_pow_le`, which is the same fact in unnormalised integer form. -/
theorem H_le_H_of_log_eq_add {s : Finset ι} {p q g : ι → ℝ} {c : ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hp1 : ∑ i ∈ s, p i = 1) (hq1 : ∑ i ∈ s, q i = 1)
    (hlog : ∀ i ∈ s, Real.log (q i) = c + g i)
    (hmom : ∑ i ∈ s, p i * g i = ∑ i ∈ s, q i * g i) :
    H s p ≤ H s q := by
  have expand : ∀ r : ι → ℝ, (∑ i ∈ s, r i = 1) →
      ∑ i ∈ s, -(r i * Real.log (q i)) = -c - ∑ i ∈ s, r i * g i := by
    intro r hr
    have hstep : ∀ i ∈ s, -(r i * Real.log (q i)) = -(c * r i) - r i * g i := by
      intro i hi
      rw [hlog i hi]; ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hr]
    ring
  have h1 : H s p ≤ ∑ i ∈ s, -(p i * Real.log (q i)) :=
    H_le_sum_neg_mul_log hp hq hp1 hq1.le
  rw [expand p hp1, hmom] at h1
  have h2 : H s q = ∑ i ∈ s, -(q i * Real.log (q i)) :=
    Finset.sum_congr rfl fun i _ => negMulLog_eq _
  rw [h2, expand q hq1]
  exact h1

/-! ## Existence of a maximiser -/

section Compact

variable [Fintype ι]

/-- `p ↦ H univ p` is continuous, since `Real.negMulLog` is. -/
theorem continuous_H : Continuous fun p : ι → ℝ => H Finset.univ p :=
  continuous_finset_sum _ fun i _ => Real.continuous_negMulLog.comp (continuous_apply i)

/-- Entropy attains a maximum on any nonempty compact set of vectors. -/
theorem exists_isMaxOn_H {K : Set (ι → ℝ)} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ q ∈ K, ∀ p ∈ K, H Finset.univ p ≤ H Finset.univ q := by
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hne continuous_H.continuousOn
  exact ⟨q, hqK, fun p hp => hq hp⟩

/-- Entropy attains a maximum on the standard simplex. -/
theorem exists_isMaxOn_H_stdSimplex [Nonempty ι] :
    ∃ q ∈ stdSimplex ℝ ι, ∀ p ∈ stdSimplex ℝ ι, H Finset.univ p ≤ H Finset.univ q := by
  refine exists_isMaxOn_H (isCompact_stdSimplex ι) ⟨fun _ => (Fintype.card ι : ℝ)⁻¹, ?_, ?_⟩
  · intro x; positivity
  · have : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp

/-- **Existence of the max-entropy point of a marginal polytope.**  The constraints are `‹f j, p›
= b j` for finitely many linear functionals `f j` — the shape every marginal constraint of the
laser method has.  If the polytope is nonempty, entropy attains a maximum on it.

Together with `H_le_H_of_log_eq_add` this is the "the maximiser exists and is characterised by
first-order optimality" pair. -/
theorem exists_isMaxOn_H_marginal {J : Type*} (f : J → ι → ℝ) (b : J → ℝ)
    (hne : {p : ι → ℝ | p ∈ stdSimplex ℝ ι ∧ ∀ j, ∑ i, f j i * p i = b j}.Nonempty) :
    ∃ q ∈ {p : ι → ℝ | p ∈ stdSimplex ℝ ι ∧ ∀ j, ∑ i, f j i * p i = b j},
      ∀ p ∈ {p : ι → ℝ | p ∈ stdSimplex ℝ ι ∧ ∀ j, ∑ i, f j i * p i = b j},
        H Finset.univ p ≤ H Finset.univ q := by
  refine exists_isMaxOn_H ?_ hne
  have hclosed : IsClosed {p : ι → ℝ | ∀ j, ∑ i, f j i * p i = b j} := by
    have : {p : ι → ℝ | ∀ j, ∑ i, f j i * p i = b j} =
        ⋂ j, {p : ι → ℝ | ∑ i, f j i * p i = b j} := by
      ext p; simp [Set.mem_iInter]
    rw [this]
    refine isClosed_iInter fun j => ?_
    exact isClosed_eq (continuous_finset_sum _ fun i _ =>
      continuous_const.mul (continuous_apply i)) continuous_const
  have hEq : {p : ι → ℝ | p ∈ stdSimplex ℝ ι ∧ ∀ j, ∑ i, f j i * p i = b j} =
      stdSimplex ℝ ι ∩ {p : ι → ℝ | ∀ j, ∑ i, f j i * p i = b j} := rfl
  rw [hEq]
  exact (isCompact_stdSimplex ι).inter_right hclosed

end Compact

end Entropy

end OmegaBound

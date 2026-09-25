import OmegaBound.EntropyBasic
import OmegaBound.CW90Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# General-alphabet type counting

The statement the laser method needs is

  `binom(N; α₁N, …, α_sN) = 2^{N(H(α) ± o(1))}`,

over alphabets of size up to `3^4 = 81`.  This file proves it as two explicit inequalities with
a **named, concrete** error term — never as an asymptotic equality.  The error is

  `errRate s N = (s − 1) · log (N+1) / N`,

and `tendsto_errRate` proves it tends to `0`, so a later limit argument can kill it.

## The two directions, and the sign trap

The whole file rests on a single sandwich in `ℕ`, with `n = ∑ k`:

  `multinomial(n; k) · ∏ᵢ kᵢ^{kᵢ}  ≤  n^n  ≤  (n+1)^{s−1} · multinomial(n; k) · ∏ᵢ kᵢ^{kᵢ}`.

The two halves run in **opposite** directions:

* the **left** inequality (`multinomial_mul_prod_pow_self_le`) is one term of the multinomial
  theorem; it gives the entropy
  **upper** bound on the count;
* the **right** inequality (`pow_sum_le_multinomial`) is the largest-term argument, engine
  `CW90.pow_add_self_le_choose_mul`, and it gives the entropy **lower** bound on the count.

## The general-alphabet lower bound

`pow_sum_le_multinomial` is stated for an arbitrary `Finset ι` and arbitrary counts.  It
subsumes `CW90.multinomial_six_lower` (six parts `(L,L,L,N−L,N−L,N−L)`), re-derived verbatim as
`multinomial_six_lower'`, and the five-part unequal case `multinomial_five_lower'`.  The polynomial factor is `(n+1)^{s−1}`, exactly the `(3N+1)^5` and
`(n+1)^4` of the special cases: `s − 1` peelings, not `s`.

`0 ^ 0 = 1` in `ℕ` is what makes vanishing parts come out right, and it is the same convention
as `Real.log 0 = 0` on the entropy side; the two match term by term.

## Main results

* `multinomial_mul_prod_pow_le` — the weighted largest-term inequality, any `Finset`.
* `multinomial_mul_prod_pow_self_le`, `pow_sum_le_multinomial` — the `ℕ` sandwich.
* `pow_card_le_multinomial_univ` — the `Fintype` form of the lower bound.
* `multinomial_five_lower'`, `multinomial_six_lower'` — the subsumption.
* `emp`, `exp_mul_H_emp` — the empirical distribution and `exp(N·H) = N^N / ∏ kᵢ^{kᵢ}`.
* `multinomial_le_exp_mul_H`, `exp_mul_H_le_multinomial` — the two counting inequalities.
* `abs_log_multinomial_sub_le` — the two-sided form, error `(s−1)·log(N+1)`; and
  `abs_log_multinomial_sub_le_of_card_le`, the uniform `80·log(N+1)` for `s ≤ 81`.
* `multinomial_le_two_pow`, `two_pow_le_multinomial` — the same in the base-`2` shape
  `2^{N(H₂(α) ± errRate)}`; `…_of_dist` for a prescribed distribution `α` with `αᵢN ∈ ℕ`.
* `tendsto_errRate` — the error term is `o(1)`.
-/

open Finset

namespace OmegaBound

namespace Entropy

variable {ι : Type*}

/-! ## The natural-number sandwich -/

section Nat

/-- **The weighted largest-term inequality**, for an arbitrary `Finset`: for any weights `a` and
any `k` with `∑_{i ∈ s} kᵢ = n`,

  `multinomial(n; k) · ∏_{i ∈ s} aᵢ^{kᵢ} ≤ (∑_{i ∈ s} aᵢ)^n`.

This is one term of the multinomial theorem.  It is proved by truncating
`k` to `s` before feeding it to `Finset.piAntidiag`; no side condition on `k` outside `s` is
needed, since neither side of the inequality mentions those values. -/
theorem multinomial_mul_prod_pow_le (s : Finset ι) (a k : ι → ℕ) (n : ℕ)
    (hk : ∑ i ∈ s, k i = n) :
    Nat.multinomial s k * ∏ i ∈ s, a i ^ k i ≤ (∑ i ∈ s, a i) ^ n := by
  classical
  have hmem : (fun i => if i ∈ s then k i else 0) ∈ Finset.piAntidiag s n := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · rw [← hk]
      exact Finset.sum_congr rfl fun i hi => if_pos hi
    · intro i hi
      by_contra h
      rw [if_neg h] at hi
      exact hi rfl
  have hmul : Nat.multinomial s (fun i => if i ∈ s then k i else 0) = Nat.multinomial s k :=
    Nat.multinomial_congr fun i hi => if_pos hi
  have hprod : (∏ i ∈ s, a i ^ (if i ∈ s then k i else 0)) = ∏ i ∈ s, a i ^ k i :=
    Finset.prod_congr rfl fun i hi => by rw [if_pos hi]
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  calc Nat.multinomial s k * ∏ i ∈ s, a i ^ k i
      = Nat.multinomial s (fun i => if i ∈ s then k i else 0) *
          ∏ i ∈ s, a i ^ (if i ∈ s then k i else 0) := by rw [hmul, hprod]
    _ ≤ ∑ m ∈ Finset.piAntidiag s n, Nat.multinomial s m * ∏ i ∈ s, a i ^ m i :=
        Finset.single_le_sum
          (f := fun m : ι → ℕ => Nat.multinomial s m * ∏ i ∈ s, a i ^ m i)
          (fun _ _ => Nat.zero_le _) hmem

/-- **The upper half of the sandwich**: `multinomial(n; k) · ∏ kᵢ^{kᵢ} ≤ n^n`, `n = ∑ k`. -/
theorem multinomial_mul_prod_pow_self_le (s : Finset ι) (k : ι → ℕ) :
    Nat.multinomial s k * ∏ i ∈ s, k i ^ k i ≤ (∑ i ∈ s, k i) ^ (∑ i ∈ s, k i) :=
  multinomial_mul_prod_pow_le s k k _ rfl

/-- **The lower half of the sandwich, and the general-alphabet largest-term bound**: for an
arbitrary `Finset ι` and arbitrary counts `k`, with `n = ∑_{i ∈ s} kᵢ` and `s` of cardinality
`|s|`,

  `n^n ≤ (n+1)^{|s|−1} · multinomial(n; k) · ∏_{i ∈ s} kᵢ^{kᵢ}`.

This is the theorem ADVXXZ needs, and it subsumes `CW90.multinomial_six_lower` (six equal parts,
factor `(3N+1)^5`) and the five-part unequal case (factor `(n+1)^4`);
see `multinomial_six_lower'` and `multinomial_five_lower'` below.

The proof is the peeling of `CW90.pow_add_self_le_choose_mul` performed `|s|−1` times, by
induction over nonempty `Finset`s; the empty case is `1 ≤ 1` and needs `0 ^ 0 = 1`. -/
theorem pow_sum_le_multinomial (s : Finset ι) (k : ι → ℕ) :
    (∑ i ∈ s, k i) ^ (∑ i ∈ s, k i) ≤
      ((∑ i ∈ s, k i) + 1) ^ (s.card - 1) * Nat.multinomial s k * ∏ i ∈ s, k i ^ k i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a t ha ht ih =>
      have hcard : t.card - 1 + 1 = t.card := Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ht)
      have ih' : (∑ i ∈ t, k i) ^ (∑ i ∈ t, k i) ≤
          (k a + (∑ i ∈ t, k i) + 1) ^ (t.card - 1) * Nat.multinomial t k *
            ∏ i ∈ t, k i ^ k i := by
        refine ih.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
        exact Nat.pow_le_pow_left (by omega) _
      rw [Finset.sum_cons, Nat.multinomial_cons, Finset.prod_cons, Finset.card_cons,
        Nat.add_sub_cancel, ← hcard]
      calc (k a + ∑ i ∈ t, k i) ^ (k a + ∑ i ∈ t, k i)
          ≤ (k a + (∑ i ∈ t, k i) + 1) *
              ((k a + ∑ i ∈ t, k i).choose (k a) *
                (k a ^ k a * (∑ i ∈ t, k i) ^ (∑ i ∈ t, k i))) :=
            CW90.pow_add_self_le_choose_mul _ _
        _ ≤ (k a + (∑ i ∈ t, k i) + 1) *
              ((k a + ∑ i ∈ t, k i).choose (k a) *
                (k a ^ k a *
                  ((k a + (∑ i ∈ t, k i) + 1) ^ (t.card - 1) * Nat.multinomial t k *
                    ∏ i ∈ t, k i ^ k i))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih'))
        _ = (k a + (∑ i ∈ t, k i) + 1) ^ (t.card - 1 + 1) *
              ((k a + ∑ i ∈ t, k i).choose (k a) * Nat.multinomial t k) *
              (k a ^ k a * ∏ i ∈ t, k i ^ k i) := by
            rw [pow_succ]; ring

variable [Fintype ι]

/-- The `Fintype` form of the sandwich, upper half. -/
theorem multinomial_mul_prod_pow_self_le_univ (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) :
    Nat.multinomial Finset.univ k * ∏ i, k i ^ k i ≤ n ^ n := by
  have h := multinomial_mul_prod_pow_self_le (Finset.univ : Finset ι) k
  rwa [hk] at h

/-- The `Fintype` form of the sandwich, lower half: with `s = |ι|` the alphabet size,

  `n^n ≤ (n+1)^{s−1} · multinomial(n; k) · ∏ᵢ kᵢ^{kᵢ}`. -/
theorem pow_card_le_multinomial_univ (k : ι → ℕ) (n : ℕ) (hk : ∑ i, k i = n) :
    n ^ n ≤ (n + 1) ^ (Fintype.card ι - 1) * Nat.multinomial Finset.univ k * ∏ i, k i ^ k i := by
  have h := pow_sum_le_multinomial (Finset.univ : Finset ι) k
  rwa [hk, Finset.card_univ] at h

end Nat

/-! ## Two special cases

A five-part unequal instance and the statement of `CW90.multinomial_six_lower`, verbatim, derived
from the general theorem. -/

/-- The five-part unequal instance, from the general bound.  `Fintype.card (Fin 5) − 1 = 4`
is where the `(n+1)^4` comes from. -/
theorem multinomial_five_lower' (A : Fin 5 → ℕ) (n : ℕ) (hn : ∑ v, A v = n) :
    n ^ n ≤ (n + 1) ^ 4 * Nat.multinomial Finset.univ A * ∏ v, A v ^ A v := by
  have h := pow_card_le_multinomial_univ A n hn
  simpa using h

/-- `CW90.multinomial_six_lower`, from the general bound.  `Fintype.card (Fin 6) − 1 = 5` is
where the `(3N+1)^5` comes from. -/
theorem multinomial_six_lower' (N L : ℕ) (hL : L ≤ N) :
    (3 * N) ^ (3 * N) ≤
      (3 * N + 1) ^ 5 * Nat.multinomial Finset.univ ![L, L, L, N - L, N - L, N - L] *
        (N - L) ^ (3 * (N - L)) * L ^ (3 * L) := by
  have hsum : ∑ v, ![L, L, L, N - L, N - L, N - L] v = 3 * N := by
    rw [Fin.sum_univ_six]
    change L + L + L + (N - L) + (N - L) + (N - L) = 3 * N
    omega
  have h := pow_card_le_multinomial_univ ![L, L, L, N - L, N - L, N - L] (3 * N) hsum
  have hprod : ∏ v, (![L, L, L, N - L, N - L, N - L] v) ^ (![L, L, L, N - L, N - L, N - L] v)
      = (N - L) ^ (3 * (N - L)) * L ^ (3 * L) := by
    rw [Fin.prod_univ_six]
    change L ^ L * L ^ L * L ^ L * (N - L) ^ (N - L) * (N - L) ^ (N - L) * (N - L) ^ (N - L) = _
    rw [show 3 * (N - L) = (N - L) + (N - L) + (N - L) by ring,
      show 3 * L = L + L + L by ring, pow_add, pow_add, pow_add, pow_add]
    ring
  have hcard : Fintype.card (Fin 6) - 1 = 5 := by simp
  rw [hcard, hprod] at h
  calc (3 * N) ^ (3 * N)
      ≤ (3 * N + 1) ^ 5 * Nat.multinomial Finset.univ ![L, L, L, N - L, N - L, N - L] *
          ((N - L) ^ (3 * (N - L)) * L ^ (3 * L)) := h
    _ = (3 * N + 1) ^ 5 * Nat.multinomial Finset.univ ![L, L, L, N - L, N - L, N - L] *
          (N - L) ^ (3 * (N - L)) * L ^ (3 * L) := by ring

/-! ## The entropy form -/

section Real

/-- The **empirical distribution** (the "type") of a count vector `k` over `N` positions. -/
noncomputable def emp (k : ι → ℕ) (N : ℕ) : ι → ℝ := fun i => (k i : ℝ) / N

theorem emp_apply (k : ι → ℕ) (N : ℕ) (i : ι) : emp k N i = (k i : ℝ) / N := rfl

theorem emp_nonneg (k : ι → ℕ) (N : ℕ) (i : ι) : 0 ≤ emp k N i := by
  rw [emp_apply]; positivity

variable [Fintype ι]

theorem sum_emp (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    ∑ i, emp k N i = 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [emp_apply, ← Finset.sum_div]
  rw [show ∑ i, ((k i : ℕ) : ℝ) = (N : ℝ) by rw [← Nat.cast_sum, hk]]
  field_simp

private theorem prod_pow_pos (k : ι → ℕ) : (0 : ℝ) < ∏ i, ((k i : ℝ)) ^ (k i) := by
  refine Finset.prod_pos fun i _ => ?_
  rcases Nat.eq_zero_or_pos (k i) with h0 | h0
  · rw [h0]; norm_num
  · exact pow_pos (by exact_mod_cast h0) _

/-- `N · H(emp k N) = N log N − ∑ᵢ kᵢ log kᵢ`.  The `kᵢ = 0` coordinates contribute `0` to both
sides — on the left because `negMulLog 0 = 0`, on the right because `0 · log 0 = 0`. -/
theorem mul_H_emp_eq (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    (N : ℝ) * H Finset.univ (emp k N)
      = (N : ℝ) * Real.log N - ∑ i, (k i : ℝ) * Real.log (k i) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i : ι, (N : ℝ) * Real.negMulLog (emp k N i)
      = (k i : ℝ) * Real.log N - (k i : ℝ) * Real.log (k i) := by
    intro i
    rcases Nat.eq_zero_or_pos (k i) with h0 | h0
    · rw [emp_apply, h0]
      norm_num
    · have hki : (0 : ℝ) < (k i : ℝ) := by exact_mod_cast h0
      rw [emp_apply, negMulLog_eq, Real.log_div (ne_of_gt hki) (ne_of_gt hNR)]
      field_simp
      ring
  rw [H, Finset.mul_sum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
    ← Finset.sum_mul, show ∑ i, ((k i : ℕ) : ℝ) = (N : ℝ) by rw [← Nat.cast_sum, hk]]

/-- **The entropy of a type, exponentiated**: `exp(N · H(emp k N)) = N^N / ∏ᵢ kᵢ^{kᵢ}`.

This is the bridge between the `ℕ` sandwich and the entropy statement: the sandwich bounds the
multinomial coefficient against `N^N / ∏ kᵢ^{kᵢ}`, and this identity says that quantity *is*
`exp(N·H)`. -/
theorem exp_mul_H_emp (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    Real.exp ((N : ℝ) * H Finset.univ (emp k N)) = (N : ℝ) ^ N / ∏ i, ((k i : ℝ)) ^ (k i) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod := prod_pow_pos k
  have hpos : (0 : ℝ) < (N : ℝ) ^ N / ∏ i, ((k i : ℝ)) ^ (k i) :=
    div_pos (pow_pos hNR N) hprod
  have hlog : Real.log ((N : ℝ) ^ N / ∏ i, ((k i : ℝ)) ^ (k i))
      = (N : ℝ) * Real.log N - ∑ i, (k i : ℝ) * Real.log (k i) := by
    rw [Real.log_div (ne_of_gt (pow_pos hNR N)) (ne_of_gt hprod), Real.log_pow,
      Real.log_prod (fun i _ => ?_)]
    · refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      rw [Real.log_pow]
    · rcases Nat.eq_zero_or_pos (k i) with h0 | h0
      · rw [h0]; norm_num
      · exact ne_of_gt (pow_pos (by exact_mod_cast h0) _)
  rw [mul_H_emp_eq k N hk hN, ← hlog, Real.exp_log hpos]

/-- **Type counting, upper direction.**  `binom(N; k) ≤ exp(N · H(α))` with `α` the type of `k`.
No polynomial factor: this direction is exact. -/
theorem multinomial_le_exp_mul_H (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    ((Nat.multinomial Finset.univ k : ℕ) : ℝ)
      ≤ Real.exp ((N : ℝ) * H Finset.univ (emp k N)) := by
  have hprod := prod_pow_pos k
  have hnat := multinomial_mul_prod_pow_self_le_univ k N hk
  have hreal : ((Nat.multinomial Finset.univ k : ℕ) : ℝ) * ∏ i, ((k i : ℝ)) ^ (k i)
      ≤ (N : ℝ) ^ N := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  rw [exp_mul_H_emp k N hk hN, le_div_iff₀ hprod]
  exact hreal

/-- **Type counting, lower direction.**  `exp(N · H(α)) ≤ (N+1)^{s−1} · binom(N; k)`, with `s`
the alphabet size — the concrete polynomial factor that the `o(1)` of the asymptotic statement
hides. -/
theorem exp_mul_H_le_multinomial (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    Real.exp ((N : ℝ) * H Finset.univ (emp k N))
      ≤ ((N : ℝ) + 1) ^ (Fintype.card ι - 1) * ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
  have hprod := prod_pow_pos k
  have hnat := pow_card_le_multinomial_univ k N hk
  have hreal : (N : ℝ) ^ N
      ≤ ((N : ℝ) + 1) ^ (Fintype.card ι - 1) * ((Nat.multinomial Finset.univ k : ℕ) : ℝ) *
        ∏ i, ((k i : ℝ)) ^ (k i) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  rw [exp_mul_H_emp k N hk hN, div_le_iff₀ hprod]
  exact hreal

end Real

/-! ## The two-sided statement, and the explicit error term -/

section Error

variable [Fintype ι]

/-- The **concrete `o(1)`**: `errRate s N = (s−1)·log(N+1)/N`, in nats per position, for an
alphabet of size `s`.  `tendsto_errRate` proves it tends to `0`. -/
noncomputable def errRate (s N : ℕ) : ℝ := ((s - 1 : ℕ) : ℝ) * Real.log (N + 1) / N

/-- **The two-sided type-counting estimate.**  `|log binom(N; k) − N·H(α)| ≤ (s−1)·log(N+1)`,
i.e. `binom(N; α₁N, …, α_sN) = exp(N(H(α) ± errRate s N))`, with the error explicit. -/
theorem abs_log_multinomial_sub_le (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    |Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ) - (N : ℝ) * H Finset.univ (emp k N)|
      ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log (N + 1) := by
  have hmpos : (0 : ℝ) < ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.multinomial_pos Finset.univ k
  have hNR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hup := multinomial_le_exp_mul_H k N hk hN
  have hlo := exp_mul_H_le_multinomial k N hk hN
  have h1 : Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ)
      ≤ (N : ℝ) * H Finset.univ (emp k N) := by
    have := Real.log_le_log hmpos hup
    rwa [Real.log_exp] at this
  have h2 : (N : ℝ) * H Finset.univ (emp k N)
      ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log (N + 1) +
        Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < ((N : ℝ) + 1) ^ (Fintype.card ι - 1) := by positivity
    have := Real.log_le_log (Real.exp_pos _) hlo
    rwa [Real.log_exp, Real.log_mul (ne_of_gt hp) (ne_of_gt hmpos), Real.log_pow] at this
  have hnn : (0 : ℝ) ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The error is **uniform over the alphabets the laser method uses**.  ADVXXZ's joint types
live on alphabets of size at most `3^4 = 81`, where the error is at most `80·log(N+1)` whatever
the alphabet is; so a single `N` works for all of them at once. -/
theorem abs_log_multinomial_sub_le_of_card_le (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N)
    (hs : Fintype.card ι ≤ 81) :
    |Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ) - (N : ℝ) * H Finset.univ (emp k N)|
      ≤ 80 * Real.log ((N : ℝ) + 1) := by
  refine (abs_log_multinomial_sub_le k N hk hN).trans ?_
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hcard : ((Fintype.card ι - 1 : ℕ) : ℝ) ≤ 80 := by
    have h : Fintype.card ι - 1 ≤ 80 := by omega
    exact_mod_cast h
  exact mul_le_mul_of_nonneg_right hcard hlog

/-- The error term is `o(1)`: `(s−1)·log(N+1)/N → 0`. -/
theorem tendsto_errRate (s : ℕ) :
    Filter.Tendsto (fun N : ℕ => errRate s N) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h3 : Filter.Tendsto
      (fun N : ℕ => (2 * ((s - 1 : ℕ) : ℝ)) * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    simpa using (h1.comp h2).const_mul (2 * ((s - 1 : ℕ) : ℝ))
  refine squeeze_zero' ?_ ?_ h3
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [errRate]
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hc : (0 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrw : 2 * ((s - 1 : ℕ) : ℝ) * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1))
        = (2 * ((s - 1 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1)) / ((N : ℝ) + 1) := by
      field_simp
    rw [errRate, hrw, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hc hlog) (sub_nonneg.mpr hNR)]

end Error

/-! ## The base-`2` shape -/

section Base2

variable [Fintype ι]

private theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `2^x = exp (x · log 2)`, the only fact needed to move between the two bases. -/
private theorem two_rpow (x : ℝ) : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- **`binom(N; k) ≤ 2^{N·H₂(α)}`** — the base-`2` upper bound, no error term. -/
theorem multinomial_le_two_pow (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    ((Nat.multinomial Finset.univ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * H₂ Finset.univ (emp k N)) := by
  rw [two_rpow, mul_assoc, H_mul_log_two]
  exact multinomial_le_exp_mul_H k N hk hN

/-- **`2^{N(H₂(α) − errRate)} ≤ binom(N; k)`** — the base-`2` lower bound, with the error term
explicit and `o(1)` by `tendsto_errRate`.  Together with `multinomial_le_two_pow` this is
`binom(N; α₁N, …, α_sN) = 2^{N(H₂(α) ± o(1))}` in the form a limit argument can consume. -/
theorem two_pow_le_multinomial (k : ι → ℕ) (N : ℕ) (hk : ∑ i, k i = N) (hN : 0 < N) :
    (2 : ℝ) ^ ((N : ℝ) * (H₂ Finset.univ (emp k N) - errRate (Fintype.card ι) N / Real.log 2))
      ≤ ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.multinomial_pos Finset.univ k
  have habs := abs_log_multinomial_sub_le k N hk hN
  rw [abs_le] at habs
  rw [two_rpow]
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hexp : ((N : ℝ) * (H₂ Finset.univ (emp k N) - errRate (Fintype.card ι) N / Real.log 2))
      * Real.log 2
      = (N : ℝ) * H Finset.univ (emp k N)
        - ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1) := by
    have h1 : ((N : ℝ) * (H₂ Finset.univ (emp k N) - errRate (Fintype.card ι) N / Real.log 2))
        * Real.log 2
        = (N : ℝ) * (H₂ Finset.univ (emp k N) * Real.log 2)
          - (N : ℝ) * (errRate (Fintype.card ι) N / Real.log 2 * Real.log 2) := by ring
    rw [h1, H_mul_log_two, div_mul_cancel₀ _ (ne_of_gt log_two_pos), errRate]
    congr 1
    field_simp
  rw [hexp]
  have : (N : ℝ) * H Finset.univ (emp k N)
      - ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1)
      ≤ Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
    have h := habs.2
    push_cast at h ⊢
    linarith
  calc Real.exp ((N : ℝ) * H Finset.univ (emp k N)
        - ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.log ((N : ℝ) + 1))
      ≤ Real.exp (Real.log ((Nat.multinomial Finset.univ k : ℕ) : ℝ)) := Real.exp_le_exp.mpr this
    _ = ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := Real.exp_log hmpos

omit [Fintype ι] in
/-- If the counts are `kᵢ = αᵢ·N` for a real vector `α`, then `α` *is* the type of `k`. -/
theorem emp_eq_of_dist (a : ι → ℝ) (k : ι → ℕ) (N : ℕ) (hN : 0 < N)
    (h : ∀ i, (k i : ℝ) = a i * N) : emp k N = a := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  funext i
  rw [emp_apply, h i, mul_div_assoc, div_self (ne_of_gt hNR), mul_one]

/-- **`binom(N; α₁N, …, α_sN) ≤ 2^{N·H₂(α)}`** — the statement of the laser method, upper half,
for a prescribed distribution `α` with integral parts. -/
theorem multinomial_le_two_pow_of_dist (a : ι → ℝ) (k : ι → ℕ) (N : ℕ)
    (hk : ∑ i, k i = N) (hN : 0 < N) (h : ∀ i, (k i : ℝ) = a i * N) :
    ((Nat.multinomial Finset.univ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * H₂ Finset.univ a) := by
  rw [← emp_eq_of_dist a k N hN h]
  exact multinomial_le_two_pow k N hk hN

/-- **`2^{N(H₂(α) − o(1))} ≤ binom(N; α₁N, …, α_sN)`** — the statement of the laser method,
lower half, for a prescribed distribution `α` with integral parts.  The `o(1)` is
`errRate s N / log 2 = (s−1)·log₂(N+1)/N`, killed by `tendsto_errRate`. -/
theorem two_pow_le_multinomial_of_dist (a : ι → ℝ) (k : ι → ℕ) (N : ℕ)
    (hk : ∑ i, k i = N) (hN : 0 < N) (h : ∀ i, (k i : ℝ) = a i * N) :
    (2 : ℝ) ^ ((N : ℝ) * (H₂ Finset.univ a - errRate (Fintype.card ι) N / Real.log 2))
      ≤ ((Nat.multinomial Finset.univ k : ℕ) : ℝ) := by
  rw [← emp_eq_of_dist a k N hN h]
  exact two_pow_le_multinomial k N hk hN

end Base2

end Entropy

end OmegaBound

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Certified rational interval enclosures for `Real.exp`

This is the arithmetic core of the interval layer.  Everything else in the
`Interval*` files — `Real.log`, `x log x` — is derived from it by inversion, so
there is exactly one place where a transcendental function meets a rational
number.

## The core

`Real.exp_bound` in Mathlib gives, for `|t| ≤ 1` and `0 < n`,

  `|exp t - ∑_{m<n} tᵐ/m!| ≤ |t|ⁿ · (n+1)/(n!·n)`.

The constants are explicit, so the estimate is usable as stated; what is *not*
usable is the `Finset.range` sum, because a `norm_num` goal containing it costs
`n` rewrites of `Finset.sum_range_succ` before any arithmetic happens.  We
therefore fix `n = 20` once and for all and record the partial sum in **Horner
form** (`expPoly`), as a polynomial expression that `norm_num` evaluates
directly.  `expPoly_eq` is the (one-off) proof that the Horner form is the
Taylor sum.

At `n = 20` the remainder constant is `21/(20!·20) = 21/48658040163532800000`,
so for `|t| ≤ 1` the enclosure is good to `4.4·10⁻¹⁹`, and for `|t| ≤ log 2`
(the range of the reduced logarithm `log (x·2^m)`) to `2.9·10⁻²²`.

## Main results

* `abs_exp_sub_expPoly_le` — the enclosure theorem, remainder explicit
* `exp_le_of`, `le_exp_of` — the two one-sided consumer lemmas, `|t| ≤ 1`
* `exp_le_of_sq`, `le_exp_of_sq` — one squaring step, for range reduction
* `exp_enclosure` — the packaged two-sided form

Every side condition of the consumer lemmas is a rational inequality with no
transcendental subterm, dischargeable by `norm_num [expPoly]`.
-/

namespace OmegaBound.Interval

open Finset

/-- `∑_{m<20} tᵐ/m!`, in Horner form.  Written out rather than as a
`Finset.range` sum so that `norm_num` can evaluate it with `19` multiplications
and no rewriting. -/
noncomputable def expPoly (t : ℝ) : ℝ :=
  1 + t / 1 * (1 + t / 2 * (1 + t / 3 * (1 + t / 4 * (1 + t / 5 * (1 + t / 6 *
  (1 + t / 7 * (1 + t / 8 * (1 + t / 9 * (1 + t / 10 * (1 + t / 11 * (1 + t / 12 *
  (1 + t / 13 * (1 + t / 14 * (1 + t / 15 * (1 + t / 16 * (1 + t / 17 * (1 + t / 18 *
  (1 + t / 19))))))))))))))))))

/-- The Taylor remainder constant `(n+1)/(n!·n)` at `n = 20`. -/
noncomputable def expErr : ℝ := 21 / 48658040163532800000

theorem expErr_pos : (0:ℝ) < expErr := by norm_num [expErr]

theorem expPoly_eq (t : ℝ) :
    expPoly t = ∑ m ∈ Finset.range 20, t ^ m / (Nat.factorial m : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num [expPoly]
  ring

/-- **The enclosure theorem.**  For `|t| ≤ 1` the degree-`19` Taylor polynomial
of `exp` approximates `exp t` with error at most `t²⁰ · 21/(20!·20)`. -/
theorem abs_exp_sub_expPoly_le {t : ℝ} (ht : |t| ≤ 1) :
    |Real.exp t - expPoly t| ≤ t ^ 20 * expErr := by
  have h := Real.exp_bound (x := t) ht (n := 20) (by norm_num)
  rw [expPoly_eq]
  refine h.trans (le_of_eq ?_)
  have habs : |t| ^ 20 = t ^ 20 := (Nat.even_iff.mpr rfl).pow_abs t
  rw [habs, expErr]
  norm_num [Nat.factorial]

/-- **The flat form of the enclosure theorem**, with the `t²⁰` factor discarded.

This is what the consumer lemmas use, and it is the single most important
performance decision in this layer.  Evaluating `c²⁰` for an `18`-decimal `c`
means a `360`-digit numerator, and measurement says that one term costs **four
times** as much as the whole degree-`19` Horner evaluation of `expPoly c`
(`≈ 38 ms` against `≈ 10 ms`).  Dropping it costs three digits of precision —
the enclosure is good to `4.4·10⁻¹⁹` rather than to `3·10⁻²²` — and buys back a
factor of three in elaboration time and proof size at every call site.

The sharp form `abs_exp_sub_expPoly_le` remains available for one-off constants,
where cost does not matter; it is what pins `log 2` to `21` decimals. -/
theorem abs_exp_sub_expPoly_le' {t : ℝ} (ht : |t| ≤ 1) :
    |Real.exp t - expPoly t| ≤ expErr := by
  refine (abs_exp_sub_expPoly_le ht).trans ?_
  have h1 : t ^ 20 ≤ 1 := by
    have : |t| ^ 20 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
    rwa [(Nat.even_iff.mpr rfl).pow_abs t] at this
  nlinarith [expErr_pos]

/-- One-sided consumer lemma: an upper bound on `exp t`.  The hypothesis is a
rational inequality with no transcendental subterm. -/
theorem exp_le_of {t hi : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1)
    (h : expPoly t + expErr ≤ hi) : Real.exp t ≤ hi := by
  have habs : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly_le' habs)
  linarith [hb.2]

/-- One-sided consumer lemma: a lower bound on `exp t`. -/
theorem le_exp_of {t lo : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1)
    (h : lo ≤ expPoly t - expErr) : lo ≤ Real.exp t := by
  have habs : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly_le' habs)
  linarith [hb.1]

/-- The sharp one-sided upper bound, for one-off constants. -/
theorem exp_le_of_sharp {t hi : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1)
    (h : expPoly t + t ^ 20 * expErr ≤ hi) : Real.exp t ≤ hi := by
  have habs : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly_le habs)
  linarith [hb.2]

/-- The sharp one-sided lower bound, for one-off constants. -/
theorem le_exp_of_sharp {t lo : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1)
    (h : lo ≤ expPoly t - t ^ 20 * expErr) : lo ≤ Real.exp t := by
  have habs : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly_le habs)
  linarith [hb.1]

/-- **The packaged two-sided `exp` enclosure, `|t| ≤ 1`.**  A call site is

  `exp_enclosure (by norm_num [expPoly, expErr]) : lo ≤ Real.exp t ∧ Real.exp t ≤ hi`. -/
theorem exp_enclosure {t lo hi : ℝ}
    (h : -1 ≤ t ∧ t ≤ 1 ∧ lo ≤ expPoly t - expErr ∧ expPoly t + expErr ≤ hi) :
    lo ≤ Real.exp t ∧ Real.exp t ≤ hi :=
  ⟨le_exp_of h.1 h.2.1 h.2.2.1, exp_le_of h.1 h.2.1 h.2.2.2⟩

/-! ### The low-degree core

The proof term produced by `norm_num` for an exact rational Horner evaluation of
degree `d` at a `D`-decimal argument has size `Θ(d²·D)`: the `k`-th accumulator
is a reduced rational with about `k·D` digits in numerator and denominator, and
`norm_num` records every one of them.  Halving the degree therefore quarters the
proof.

`expPoly8` is the degree-`7` truncation.  On its own it is useless — at `|t| ≤ 1`
the remainder is `2.8·10⁻⁵` — but on `|t| ≤ 1/128` the remainder is
`(1/128)⁸·9/(8!·8) = 3.9·10⁻²²`, *better* than the degree-`19` polynomial on
`|t| ≤ 1`, for a third of the cost.  The `Real.log` layer reaches `|t| ≤ 1/128`
by reducing along powers of `65/64` (see `OmegaBound.IntervalLog`). -/

/-- `∑_{m<8} tᵐ/m!`, in Horner form. -/
noncomputable def expPoly8 (t : ℝ) : ℝ :=
  1 + t / 1 * (1 + t / 2 * (1 + t / 3 * (1 + t / 4 * (1 + t / 5 * (1 + t / 6 *
  (1 + t / 7))))))

/-- `(1/128)⁸ · 9/(8!·8)`, the degree-`7` remainder constant on `|t| ≤ 1/128`. -/
noncomputable def expErr8 : ℝ := 9 / 23242897532874035036160

theorem expErr8_pos : (0:ℝ) < expErr8 := by norm_num [expErr8]

theorem expPoly8_eq (t : ℝ) :
    expPoly8 t = ∑ m ∈ Finset.range 8, t ^ m / (Nat.factorial m : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num [expPoly8]
  ring

/-- **The low-degree enclosure theorem.**  On `|t| ≤ 1/128` the degree-`7` Taylor
polynomial of `exp` approximates `exp t` to `3.9·10⁻²²`. -/
theorem abs_exp_sub_expPoly8_le {t : ℝ} (ht : |t| ≤ 1 / 128) :
    |Real.exp t - expPoly8 t| ≤ expErr8 := by
  have ht1 : |t| ≤ 1 := ht.trans (by norm_num)
  have h := Real.exp_bound (x := t) ht1 (n := 8) (by norm_num)
  rw [expPoly8_eq]
  refine h.trans ?_
  have hp : |t| ^ 8 ≤ (1 / 128 : ℝ) ^ 8 := pow_le_pow_left₀ (abs_nonneg t) ht 8
  have hc : (0:ℝ) ≤ ((8:ℕ).succ / ((Nat.factorial 8 : ℝ) * 8)) := by
    norm_num [Nat.factorial]
  calc |t| ^ 8 * ((8:ℕ).succ / ((Nat.factorial 8 : ℝ) * 8))
      ≤ (1 / 128 : ℝ) ^ 8 * ((8:ℕ).succ / ((Nat.factorial 8 : ℝ) * 8)) := by
        exact mul_le_mul_of_nonneg_right hp hc
    _ = expErr8 := by norm_num [Nat.factorial, expErr8]

/-- Low-degree one-sided consumer lemma: an upper bound on `exp t`. -/
theorem exp_le_of8 {t hi : ℝ} (h1 : -(1 / 128) ≤ t) (h2 : t ≤ 1 / 128)
    (h : expPoly8 t + expErr8 ≤ hi) : Real.exp t ≤ hi := by
  have habs : |t| ≤ 1 / 128 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly8_le habs)
  linarith [hb.2]

/-- Low-degree one-sided consumer lemma: a lower bound on `exp t`. -/
theorem le_exp_of8 {t lo : ℝ} (h1 : -(1 / 128) ≤ t) (h2 : t ≤ 1 / 128)
    (h : lo ≤ expPoly8 t - expErr8) : lo ≤ Real.exp t := by
  have habs : |t| ≤ 1 / 128 := abs_le.mpr ⟨h1, h2⟩
  have hb := abs_le.mp (abs_exp_sub_expPoly8_le habs)
  linarith [hb.1]

/-! ### Range reduction by squaring

`exp (2t) = (exp t)²`, so an enclosure at `t` squares to an enclosure at `2t`.
The extra rational argument (`h`, resp. `l`) is the *rounded* square: a
generator supplies a short rational and the side condition keeps the
intermediate numerators from doubling in length at every step. -/

theorem exp_le_of_sq {t hi h : ℝ} (h0 : 0 ≤ hi) (hle : Real.exp t ≤ hi)
    (hsq : hi ^ 2 ≤ h) : Real.exp (2 * t) ≤ h := by
  have : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [two_mul, Real.exp_add]; ring
  rw [this]
  exact le_trans (by nlinarith [Real.exp_pos t]) hsq

theorem le_exp_of_sq {t lo l : ℝ} (h0 : 0 ≤ lo) (hle : lo ≤ Real.exp t)
    (hsq : l ≤ lo ^ 2) : l ≤ Real.exp (2 * t) := by
  have : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [two_mul, Real.exp_add]; ring
  rw [this]
  exact hsq.trans (by nlinarith)

end OmegaBound.Interval

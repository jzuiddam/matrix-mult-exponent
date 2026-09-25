import OmegaBound.IntervalCert
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Certified enclosures for `x · log x`

The entropy inequalities of the laser method are stated in `x·log x`, or in
Mathlib's `Real.negMulLog x = -x · log x`, so this is the form the consumer
actually needs.

## The value at `x = 0`

`Real.log 0 = 0` by Mathlib's junk-value convention, so `0 · Real.log 0 = 0`,
which is the correct entropy value — but for the *wrong reason*, and the
convention is not what makes it right.  It is right because
`x log x → 0` as `x ↓ 0`, and the `x = 0` term of an entropy sum contributes
nothing.  The point that matters here is that no lemma below needs `0 < x`:
`mul_log_le_of` and `le_mul_log_of` take `0 ≤ x`, and at `x = 0` both sides are
`0`.  `mul_log_zero` records the value explicitly so that a generator can emit a
uniform call for a coordinate it does not know to be nonzero.

Note that the *log* layer does require `0 < x` — `log_cert` cannot certify
`log 0`.  A generator must therefore split on `x = 0`, which is a rational test,
and emit `mul_log_zero` there.

## Main results

* `mul_log_zero` — `x = 0 → x·log x = 0`
* `mul_log_le_of`, `le_mul_log_of` — monotone transfer from a `log` enclosure
* `mul_log_cert`, `le_mul_log_cert` — the packaged division-free forms
* `negMulLog_le_cert`, `le_negMulLog_cert` — the same in Mathlib's `negMulLog`

## A generated call site

```lean
theorem inst7 :
    ((242061413842535959 : ℝ) / 1000000000000000000) *
        Real.log ((242061413842535959 : ℝ) / 1000000000000000000)
      ≤ (-343383887837... : ℝ) / 10 ^ 21 :=
  mul_log_cert 3 43 242061413842535959 1000000000000000000
    (-5802288179029568438) (10 ^ 21) (-1418563808812359568199) (10 ^ 21)
    (-343383887837...) (10 ^ 21) (by norm_num [expNum8])
```
-/

namespace OmegaBound.Interval

/-- At `x = 0` the entropy term vanishes. -/
theorem mul_log_zero {x : ℝ} (hx : x = 0) : x * Real.log x = 0 := by
  rw [hx, zero_mul]

/-- Monotone transfer: an upper bound on `log x` gives one on `x·log x`, for
`x ≥ 0`.  No positivity of `x` is needed — at `x = 0` both sides are `0`. -/
theorem mul_log_le_of {x b u : ℝ} (hx : 0 ≤ x) (hb : Real.log x ≤ b)
    (h : x * b ≤ u) : x * Real.log x ≤ u :=
  le_trans (mul_le_mul_of_nonneg_left hb hx) h

/-- Monotone transfer: a lower bound on `log x` gives one on `x·log x`. -/
theorem le_mul_log_of {x a l : ℝ} (hx : 0 ≤ x) (ha : a ≤ Real.log x)
    (h : l ≤ x * a) : l ≤ x * Real.log x :=
  le_trans h (mul_le_mul_of_nonneg_left ha hx)

/-- **Upper bound on `(P/Q)·log (P/Q)`, division-free certificate.**

The first eight conjuncts are exactly those of `log_le_cert`; the ninth clears
the denominators of the final multiplication, `(P/Q)·(B/T) ≤ U/V`.  Note the
direction: because `B/T` is an *upper* bound on `log x` and `x ≥ 0`, the product
`x·(B/T)` is an upper bound on `x log x` whatever the sign of `B`. -/
theorem mul_log_cert (m j : ℕ) (P Q C S B T U V : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ≤
        Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 - 45360 * S ^ 7) ∧
      C * 10 ^ 26 * T + j * 1550418653596525415085406 * S * T ≤
        B * S * 10 ^ 26 + m * 693147180559945309416 * 10 ^ 5 * S * T ∧
      0 < V ∧ P * B * V ≤ U * (Q * T)) :
    P / Q * Real.log (P / Q) ≤ U / V := by
  obtain ⟨hP, hQ, hS, hT, hc1, hc2, hcert, hb, hV, hmul⟩ := h
  refine mul_log_le_of (le_of_lt (div_pos hP hQ))
    (log_le_cert m j P Q C S B T ⟨hP, hQ, hS, hT, hc1, hc2, hcert, hb⟩) ?_
  rw [← sub_nonneg]
  have key : U / V - P / Q * (B / T) = (U * (Q * T) - P * B * V) / (Q * T * V) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)

/-- **Lower bound on `(P/Q)·log (P/Q)`, division-free certificate.** -/
theorem le_mul_log_cert (m j : ℕ) (P Q C S A T L V : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 + 45360 * S ^ 7) ≤
        P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ∧
      A * S * 10 ^ 26 + m * 693147180559945309418 * 10 ^ 5 * S * T ≤
        C * 10 ^ 26 * T + j * 1550418653596525415085403 * S * T ∧
      0 < V ∧ L * (Q * T) ≤ P * A * V) :
    L / V ≤ P / Q * Real.log (P / Q) := by
  obtain ⟨hP, hQ, hS, hT, hc1, hc2, hcert, ha, hV, hmul⟩ := h
  refine le_mul_log_of (le_of_lt (div_pos hP hQ))
    (le_log_cert m j P Q C S A T ⟨hP, hQ, hS, hT, hc1, hc2, hcert, ha⟩) ?_
  rw [← sub_nonneg]
  have key : P / Q * (A / T) - L / V = (P * A * V - L * (Q * T)) / (Q * T * V) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)

/-! ### In Mathlib's `negMulLog`

`Real.negMulLog x = -x · log x`, which is the *positive* entropy contribution.
An upper bound on `x log x` is a lower bound on `negMulLog x` and conversely, so
the two certificate lemmas swap roles. -/

theorem negMulLog_eq_neg (x : ℝ) : Real.negMulLog x = -(x * Real.log x) := by
  rw [Real.negMulLog]; ring

/-- A lower bound on `negMulLog (P/Q)` from the `x·log x` upper certificate. -/
theorem le_negMulLog_cert (m j : ℕ) (P Q C S B T U V : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ≤
        Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 - 45360 * S ^ 7) ∧
      C * 10 ^ 26 * T + j * 1550418653596525415085406 * S * T ≤
        B * S * 10 ^ 26 + m * 693147180559945309416 * 10 ^ 5 * S * T ∧
      0 < V ∧ P * B * V ≤ U * (Q * T)) :
    -(U / V) ≤ Real.negMulLog (P / Q) := by
  rw [negMulLog_eq_neg, neg_le_neg_iff]
  exact mul_log_cert m j P Q C S B T U V h

/-- An upper bound on `negMulLog (P/Q)` from the `x·log x` lower certificate. -/
theorem negMulLog_le_cert (m j : ℕ) (P Q C S A T L V : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 + 45360 * S ^ 7) ≤
        P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ∧
      A * S * 10 ^ 26 + m * 693147180559945309418 * 10 ^ 5 * S * T ≤
        C * 10 ^ 26 * T + j * 1550418653596525415085403 * S * T ∧
      0 < V ∧ L * (Q * T) ≤ P * A * V) :
    Real.negMulLog (P / Q) ≤ -(L / V) := by
  rw [negMulLog_eq_neg, neg_le_neg_iff]
  exact le_mul_log_cert m j P Q C S A T L V h

end OmegaBound.Interval

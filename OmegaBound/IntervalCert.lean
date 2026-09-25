import OmegaBound.IntervalLog

/-!
# The generated-call-site interface: division-free `Real.log` certificates

`OmegaBound.IntervalLog` states its consumer lemmas with rational side
conditions.  That is the mathematically natural form, and it works, but it is
**four times more expensive than it needs to be**, for a reason worth recording.

## Measurement

Per call site, at `21` decimals, with the degree-`7` core:

| side condition                                        | elaborate | kernel | total |
|-------------------------------------------------------|-----------|--------|-------|
| rational, `expPoly8 c - expErr8` with `c = C/S`        | `0.7 ms`  | `31 ms`| `40 ms` |
| the same inequality with denominators cleared          | `0.9 ms`  | `1.6 ms`| `4.5 ms` |

The cost is not `Real`, and it is not the size of the integers — the cleared
inequality compares two `270`-digit numbers.  It is **division**: `norm_num`
certifies a quotient through `IsRat`, whose invariant carries an invertible
denominator, and the kernel pays for every one of the `~30` intermediate
denominators that an exact rational Horner evaluation produces.  Replacing
`(0:ℝ) ≤ e/d` by `0 ≤ e` costs the kernel nothing.

This is the same lesson as the rest of this repository — collapse to one integer
inequality — and it is what makes `10⁴` call sites comfortable rather than
merely possible.

## The cleared form

With `x = P/Q`, `c = C/S`, `b = B/T` and `E = 23242897532874035036160`
(so that `expErr8 = 9/E`), the two nontrivial conditions of `log_le_fast` become

  `P·2^m·64^j·5040·S⁷·E ≤ Q·65^j·(expNum8 C S·E − 45360·S⁷)`
  `C·10²⁶·T + j·RH·S·T ≤ B·S·10²⁶ + m·L2·10⁵·S·T`

where `expNum8 C S = 5040·S⁷·expPoly8 (C/S)` is the integer-coefficient Horner
polynomial and `RH`, `L2` are the numerators of `lgRhoHi`, `log2Lo`.  Every
subterm is a product of integers.

## Main results

* `log_le_cert`, `le_log_cert` — one-sided, division-free
* `log_cert` — the two-sided form

## A generated call site

```lean
theorem inst7 :
    Real.log ((242061413842535959 : ℝ) / 1000000000000000000)
      ≤ (-1418563808812359568199 : ℝ) / 10 ^ 21 :=
  log_le_cert 3 43 242061413842535959 1000000000000000000
    (-5802288179029568438) (10 ^ 21) (-1418563808812359568199) (10 ^ 21)
    (by norm_num [expNum8])
```

`3` and `43` are the two range-reduction exponents `m` and `j`; the six reals are
`P Q C S B T`; the single `by norm_num [expNum8]` discharges an eight-fold
conjunction of integer inequalities.  Nothing searches.
-/

namespace OmegaBound.Interval

/-- `5040·S⁷·expPoly8 (C/S)`, the degree-`7` Taylor polynomial with its
denominators cleared: a homogeneous integer-coefficient polynomial in `C, S`,
in Horner form. -/
noncomputable def expNum8 (C S : ℝ) : ℝ :=
  5040 * S ^ 7 + C * (5040 * S ^ 6 + C * (2520 * S ^ 5 + C * (840 * S ^ 4 +
    C * (210 * S ^ 3 + C * (42 * S ^ 2 + C * (7 * S + C))))))

theorem expPoly8_div (C S : ℝ) (hS : S ≠ 0) :
    expPoly8 (C / S) = expNum8 C S / (5040 * S ^ 7) := by
  rw [expPoly8, expNum8]
  field_simp
  ring

theorem expErr8_eq : expErr8 = 9 / 23242897532874035036160 := rfl

/-- **Upper bound on `log (P/Q)`, division-free certificate.**  All eight
conditions are integer inequalities. -/
theorem log_le_cert (m j : ℕ) (P Q C S B T : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ≤
        Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 - 45360 * S ^ 7) ∧
      C * 10 ^ 26 * T + j * 1550418653596525415085406 * S * T ≤
        B * S * 10 ^ 26 + m * 693147180559945309416 * 10 ^ 5 * S * T) :
    Real.log (P / Q) ≤ B / T := by
  obtain ⟨hP, hQ, hS, hT, hc1, hc2, hcert, hb⟩ := h
  refine log_le_fast m j (C / S) ⟨div_pos hP hQ, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hS]; linarith
  · rw [div_le_iff₀ hS]; linarith
  · rw [← sub_nonneg]
    have key : 65 ^ j * (expPoly8 (C / S) - expErr8) - P / Q * 2 ^ m * 64 ^ j =
        (Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 - 45360 * S ^ 7) -
            P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160) /
          (Q * 5040 * S ^ 7 * 23242897532874035036160) := by
      rw [expPoly8_div C S (ne_of_gt hS), expErr8_eq]
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)
  · rw [← sub_nonneg]
    have key : B / T - (C / S + j * lgRhoHi - m * log2Lo) =
        (B * S * 10 ^ 26 + m * 693147180559945309416 * 10 ^ 5 * S * T -
            (C * 10 ^ 26 * T + j * 1550418653596525415085406 * S * T)) /
          (S * T * 10 ^ 26) := by
      rw [lgRhoHi, log2Lo]
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)

/-- **Lower bound on `log (P/Q)`, division-free certificate.** -/
theorem le_log_cert (m j : ℕ) (P Q C S A T : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧ -S ≤ 128 * C ∧ 128 * C ≤ S ∧
      Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 + 45360 * S ^ 7) ≤
        P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ∧
      A * S * 10 ^ 26 + m * 693147180559945309418 * 10 ^ 5 * S * T ≤
        C * 10 ^ 26 * T + j * 1550418653596525415085403 * S * T) :
    A / T ≤ Real.log (P / Q) := by
  obtain ⟨hP, hQ, hS, hT, hc1, hc2, hcert, ha⟩ := h
  refine le_log_fast m j (C / S) ⟨div_pos hP hQ, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hS]; linarith
  · rw [div_le_iff₀ hS]; linarith
  · rw [← sub_nonneg]
    have key : P / Q * 2 ^ m * 64 ^ j - 65 ^ j * (expPoly8 (C / S) + expErr8) =
        (P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 -
            Q * 65 ^ j * (expNum8 C S * 23242897532874035036160 + 45360 * S ^ 7)) /
          (Q * 5040 * S ^ 7 * 23242897532874035036160) := by
      rw [expPoly8_div C S (ne_of_gt hS), expErr8_eq]
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)
  · rw [← sub_nonneg]
    have key : C / S + j * lgRhoLo - m * log2Hi - A / T =
        (C * 10 ^ 26 * T + j * 1550418653596525415085403 * S * T -
            (A * S * 10 ^ 26 + m * 693147180559945309418 * 10 ^ 5 * S * T)) /
          (S * T * 10 ^ 26) := by
      rw [lgRhoLo, log2Hi]
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)

/-- **The two-sided division-free certificate.**

`m`, `j` are the range-reduction exponents; `x = P/Q` is the argument;
`C₋/S`, `C₊/S` are the two witnesses for the twice-reduced logarithm; and the
conclusion is `A/T ≤ log x ≤ B/T`.  The single hypothesis is a conjunction of
integer inequalities, dischargeable by `norm_num [expNum8]`. -/
theorem log_cert (m j : ℕ) (P Q Cm Cp S A B T : ℝ)
    (h : 0 < P ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧
      (-S ≤ 128 * Cm ∧ 128 * Cm ≤ S) ∧ (-S ≤ 128 * Cp ∧ 128 * Cp ≤ S) ∧
      Q * 65 ^ j * (expNum8 Cm S * 23242897532874035036160 + 45360 * S ^ 7) ≤
        P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ∧
      P * 2 ^ m * 64 ^ j * 5040 * S ^ 7 * 23242897532874035036160 ≤
        Q * 65 ^ j * (expNum8 Cp S * 23242897532874035036160 - 45360 * S ^ 7) ∧
      A * S * 10 ^ 26 + m * 693147180559945309418 * 10 ^ 5 * S * T ≤
        Cm * 10 ^ 26 * T + j * 1550418653596525415085403 * S * T ∧
      Cp * 10 ^ 26 * T + j * 1550418653596525415085406 * S * T ≤
        B * S * 10 ^ 26 + m * 693147180559945309416 * 10 ^ 5 * S * T) :
    A / T ≤ Real.log (P / Q) ∧ Real.log (P / Q) ≤ B / T := by
  obtain ⟨hP, hQ, hS, hT, ⟨hm1, hm2⟩, ⟨hp1, hp2⟩, h1, h2, h3, h4⟩ := h
  exact ⟨le_log_cert m j P Q Cm S A T ⟨hP, hQ, hS, hT, hm1, hm2, h1, h3⟩,
    log_le_cert m j P Q Cp S B T ⟨hP, hQ, hS, hT, hp1, hp2, h2, h4⟩⟩

end OmegaBound.Interval

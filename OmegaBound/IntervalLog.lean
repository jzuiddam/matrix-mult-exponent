import OmegaBound.IntervalExp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Certified rational interval enclosures for `Real.log`

`Real.log` is enclosed by **inverting** the `exp` core of `OmegaBound.IntervalExp`:
`log x ≤ b` is exactly `x ≤ exp b`, and `a ≤ log x` is exactly `exp a ≤ x`, so a
one-sided rational bound on `exp` at a *generator-chosen* rational argument is a
one-sided rational bound on `log` at an arbitrary rational argument.

This is strictly better than running the artanh series in `log` directly.  The
artanh series `log ((1+z)/(1-z)) = 2∑ z^{2j+1}/(2j+1)` converges geometrically
with ratio `z²`; after the range reduction `x = 2^{-m}·y`, `y ∈ [1,2]`, one has
`|z| ≤ 1/3` and `19` significant digits costs `20` terms, i.e. `z³⁹`.  The
exponential series has the extra `1/n!` damping: the same `19` digits cost the
degree-`19` polynomial `expPoly` at an argument of size `≤ log 2`.  Half the
degree means half the digits in every intermediate numerator.

The artanh remainder is nevertheless proved here as
`abs_log_div_sub_sum_le`, and is used to **independently re-derive** the `log 2`
constant (`log_two_artanh`, from `z = 1/3`, exact small rationals) as
a cross-check on the exp-route value.

## Range reduction

`log x = log (x·2^m) − m·log 2` with `m : ℕ` chosen so that `x·2^m ∈ [1,2]`, i.e.
`log (x·2^m) ∈ [0, log 2] ⊂ [-1,1]`, which is the range where the `exp` core is
valid.  For `x > 1` the mirrored form `log x = m·log 2 + log (x/2^m)` is
`log_le_of_div_pow` / `le_log_of_div_pow`.

## Main results

* `log_two_lo`, `log_two_hi` — `log 2` to `21` decimals
* `abs_log_div_sub_sum_le` — the artanh remainder bound, explicit
* `log_le_of_mul_pow`, `le_log_of_mul_pow` — the consumer lemmas for `x ≤ 1`
* `log_le_of_div_pow`, `le_log_of_div_pow` — the consumer lemmas for `x ≥ 1`
* `log_enclosure` — the packaged two-sided form

Each consumer lemma takes the reduction exponent `m`, one rational witness `c`,
and a **single** conjunctive side condition that is a pure rational inequality.
-/

namespace OmegaBound.Interval

open Finset

/-! ### The constant `log 2` -/

/-- A rational lower bound for `log 2`, `21` decimals. -/
noncomputable def log2Lo : ℝ := 693147180559945309416 / 10 ^ 21

/-- A rational upper bound for `log 2`, `21` decimals. -/
noncomputable def log2Hi : ℝ := 693147180559945309418 / 10 ^ 21

theorem log_two_lo : log2Lo ≤ Real.log 2 := by
  have h : Real.exp log2Lo ≤ 2 := by
    refine exp_le_of_sharp (by norm_num [log2Lo]) (by norm_num [log2Lo]) ?_
    norm_num [expPoly, expErr, log2Lo]
  have := (Real.log_le_log_iff (Real.exp_pos _) (by norm_num : (0:ℝ) < 2)).mpr h
  rwa [Real.log_exp] at this

theorem log_two_hi : Real.log 2 ≤ log2Hi := by
  have h : (2:ℝ) ≤ Real.exp log2Hi := by
    refine le_exp_of_sharp (by norm_num [log2Hi]) (by norm_num [log2Hi]) ?_
    norm_num [expPoly, expErr, log2Hi]
  have := (Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) (Real.exp_pos _)).mpr h
  rwa [Real.log_exp] at this

theorem log2Lo_pos : (0:ℝ) < log2Lo := by norm_num [log2Lo]

/-! ### The artanh remainder bound

Two applications of Mathlib's `Real.abs_log_sub_add_sum_range_le`, at `z` and at
`-z`, combine into the odd-part (artanh) series for `log ((1+z)/(1-z))`.  Stated
here as a theorem with an explicit remainder so that it can be evaluated, not
merely used for a limit. -/

/-- **The artanh remainder bound.**  For `|z| < 1`,
`log ((1+z)/(1-z))` differs from the `n`-term series
`∑_{i<n} (z^{i+1} − (−z)^{i+1})/(i+1)` (whose even terms vanish, so it is
`2∑_{2j+1<n} z^{2j+1}/(2j+1)`) by at most `2|z|^{n+1}/(1−|z|)`. -/
theorem abs_log_div_sub_sum_le {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    |Real.log ((1 + z) / (1 - z)) -
        ∑ i ∈ Finset.range n, (z ^ (i + 1) - (-z) ^ (i + 1)) / (i + 1)| ≤
      2 * |z| ^ (n + 1) / (1 - |z|) := by
  have hz' : |(-z)| < 1 := by rwa [abs_neg]
  have h1 := Real.abs_log_sub_add_sum_range_le hz n
  have h2 := Real.abs_log_sub_add_sum_range_le hz' n
  rw [abs_neg] at h2
  have hzlt : z < 1 := (abs_lt.mp hz).2
  have hzgt : -1 < z := (abs_lt.mp hz).1
  have h1ne : (1 : ℝ) - z ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + z ≠ 0 := by linarith
  have hsub : (1 : ℝ) - -z = 1 + z := by ring
  rw [hsub] at h2
  have hlog : Real.log ((1 + z) / (1 - z)) = Real.log (1 + z) - Real.log (1 - z) :=
    Real.log_div h2ne h1ne
  have hsplit :
      ∑ i ∈ Finset.range n, (z ^ (i + 1) - (-z) ^ (i + 1)) / (i + 1) =
        (∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1)) -
          ∑ i ∈ Finset.range n, (-z) ^ (i + 1) / (i + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlog, hsplit]
  have key :
      Real.log (1 + z) - Real.log (1 - z) -
          ((∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1)) -
            ∑ i ∈ Finset.range n, (-z) ^ (i + 1) / (i + 1)) =
        ((∑ i ∈ Finset.range n, (-z) ^ (i + 1) / (i + 1)) + Real.log (1 + z)) -
          ((∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1)) + Real.log (1 - z)) := by
    ring
  rw [key]
  refine (abs_sub _ _).trans ?_
  have hd : (0:ℝ) < 1 - |z| := by linarith
  have : |z| ^ (n + 1) / (1 - |z|) + |z| ^ (n + 1) / (1 - |z|) =
      2 * |z| ^ (n + 1) / (1 - |z|) := by ring
  calc |(∑ i ∈ Finset.range n, (-z) ^ (i + 1) / (i + 1)) + Real.log (1 + z)| +
        |(∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1)) + Real.log (1 - z)|
      ≤ |z| ^ (n + 1) / (1 - |z|) + |z| ^ (n + 1) / (1 - |z|) := add_le_add h2 h1
    _ = 2 * |z| ^ (n + 1) / (1 - |z|) := this

/-- An independent re-derivation of the `log 2` interval from the artanh series
at `z = 1/3` — where `(1+z)/(1-z) = 2` and every term of the series is an exact
small rational.  Cross-checks `log_two_lo` / `log_two_hi`, which come from the
exponential series instead. -/
theorem log_two_artanh :
    |Real.log 2 - ∑ i ∈ Finset.range 44,
        (((1:ℝ)/3) ^ (i + 1) - (-((1:ℝ)/3)) ^ (i + 1)) / (i + 1)| ≤ 3 / 3 ^ 45 := by
  have hz : |(1:ℝ)/3| < 1 := by rw [abs_of_pos] <;> norm_num
  have h := abs_log_div_sub_sum_le hz 44
  have h2 : ((1:ℝ) + 1/3) / (1 - 1/3) = 2 := by norm_num
  rw [h2] at h
  refine h.trans (le_of_eq ?_)
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1/3)]
  norm_num

/-! ### The consumer lemmas

`m` is the range-reduction exponent and `c` the rational witness for the reduced
logarithm.  The single hypothesis is a conjunction of rational inequalities, so a
generated call site is `lemma m c (by norm_num [expPoly, expErr, log2Lo])`. -/

/-- **Upper bound on `log x`, `x` small.**  `m : ℕ` and `c` are witnesses:
`x·2^m ≤ exp c` is certified by the `exp` core, and `log x = log (x·2^m) − m·log 2`. -/
theorem log_le_of_mul_pow (m : ℕ) (c : ℝ) {x b : ℝ}
    (h : 0 < x ∧ -1 ≤ c ∧ c ≤ 1 ∧
      x * 2 ^ m ≤ expPoly c - expErr ∧ c - m * log2Lo ≤ b) :
    Real.log x ≤ b := by
  obtain ⟨hx, hc1, hc2, hxc, hb⟩ := h
  have hpos : (0:ℝ) < x * 2 ^ m := by positivity
  have hexp : x * 2 ^ m ≤ Real.exp c := hxc.trans (le_exp_of hc1 hc2 le_rfl)
  have hlog : Real.log (x * 2 ^ m) ≤ c := by
    have := (Real.log_le_log_iff hpos (Real.exp_pos c)).mpr hexp
    rwa [Real.log_exp] at this
  have hsplit : Real.log (x * 2 ^ m) = Real.log x + m * Real.log 2 := by
    rw [Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow]
  rw [hsplit] at hlog
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [log_two_lo, hlog, hb]

/-- **Lower bound on `log x`, `x` small.** -/
theorem le_log_of_mul_pow (m : ℕ) (c : ℝ) {x a : ℝ}
    (h : 0 < x ∧ -1 ≤ c ∧ c ≤ 1 ∧
      expPoly c + expErr ≤ x * 2 ^ m ∧ a ≤ c - m * log2Hi) :
    a ≤ Real.log x := by
  obtain ⟨hx, hc1, hc2, hxc, ha⟩ := h
  have hpos : (0:ℝ) < x * 2 ^ m := by positivity
  have hexp : Real.exp c ≤ x * 2 ^ m := (exp_le_of hc1 hc2 le_rfl).trans hxc
  have hlog : c ≤ Real.log (x * 2 ^ m) := by
    have := (Real.log_le_log_iff (Real.exp_pos c) hpos).mpr hexp
    rwa [Real.log_exp] at this
  have hsplit : Real.log (x * 2 ^ m) = Real.log x + m * Real.log 2 := by
    rw [Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow]
  rw [hsplit] at hlog
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [log_two_hi, hlog, ha]

/-- **Upper bound on `log x`, `x` large.**  Here `x ≤ 2^m · exp c`. -/
theorem log_le_of_div_pow (m : ℕ) (c : ℝ) {x b : ℝ}
    (h : 0 < x ∧ -1 ≤ c ∧ c ≤ 1 ∧
      x ≤ 2 ^ m * (expPoly c - expErr) ∧ m * log2Hi + c ≤ b) :
    Real.log x ≤ b := by
  obtain ⟨hx, hc1, hc2, hxc, hb⟩ := h
  have hexp : x ≤ 2 ^ m * Real.exp c := by
    refine hxc.trans ?_
    have := le_exp_of (lo := expPoly c - expErr) hc1 hc2 le_rfl
    have h2 : (0:ℝ) < 2 ^ m := by positivity
    nlinarith
  have hlog : Real.log x ≤ m * Real.log 2 + c := by
    have hp : (0:ℝ) < 2 ^ m * Real.exp c := by positivity
    have := (Real.log_le_log_iff hx hp).mpr hexp
    rwa [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos c)), Real.log_pow,
      Real.log_exp] at this
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [log_two_hi, hlog, hb]

/-- **Lower bound on `log x`, `x` large.** -/
theorem le_log_of_div_pow (m : ℕ) (c : ℝ) {x a : ℝ}
    (h : 0 < x ∧ -1 ≤ c ∧ c ≤ 1 ∧
      2 ^ m * (expPoly c + expErr) ≤ x ∧ a ≤ m * log2Lo + c) :
    a ≤ Real.log x := by
  obtain ⟨hx, hc1, hc2, hxc, ha⟩ := h
  have hexp : 2 ^ m * Real.exp c ≤ x := by
    refine le_trans ?_ hxc
    have := exp_le_of (hi := expPoly c + expErr) hc1 hc2 le_rfl
    have h2 : (0:ℝ) < 2 ^ m := by positivity
    nlinarith
  have hlog : m * Real.log 2 + c ≤ Real.log x := by
    have hp : (0:ℝ) < 2 ^ m * Real.exp c := by positivity
    have := (Real.log_le_log_iff hp hx).mpr hexp
    rwa [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos c)), Real.log_pow,
      Real.log_exp] at this
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [log_two_lo, hlog, ha]

/-! ### The fast route: geometric range reduction along `65/64`

Reducing only by powers of `2` leaves `log (x·2^m) ∈ [0, log 2]`, which needs the
degree-`19` polynomial.  Reducing further along powers of `ρ = 65/64` — one extra
certified constant, `log ρ`, and one extra generator-chosen exponent `j` — leaves

  `c = log (x · 2^m · ρ^{-j}) ∈ [−(log ρ)/2, (log ρ)/2] ⊆ [−1/128, 1/128]`,

which the degree-`7` polynomial handles to `3.9·10⁻²²`.  Since
`x·2^m·ρ^{-j} = x·2^m·64^j/65^j`, the certified inequality is

  `x · 2^m · 64^j ≤ 65^j · (expPoly8 c − expErr8)`,

with `j ≤ 45`, because `log 2 / log ρ = 44.7`.

**Why `2^m · 64^j` and not `2^{m+6j}`.**  They are equal, but `norm_num` cannot
evaluate a power whose exponent exceeds `256` — Lean's `Nat.reducePow` refuses,
and the tactic silently leaves the goal open.  `m + 6j` reaches `280` on ordinary
inputs; `m` and `j` separately stay far below the limit.  This is a hard
constraint on any interval layer built on `norm_num`, and it is the reason the
statement carries two powers.  (It also caps the layer at `x ≥ 2^{-256}`; beyond
that the generator must split the power of two, which no certificate needs.)

This is the interface a generator should emit: fewer digits, better precision,
and a third of the proof size of the degree-`19` route. -/

/-- A rational lower bound for `log (65/64)`, `26` decimals. -/
noncomputable def lgRhoLo : ℝ := 1550418653596525415085403 / 10 ^ 26

/-- A rational upper bound for `log (65/64)`, `26` decimals. -/
noncomputable def lgRhoHi : ℝ := 1550418653596525415085406 / 10 ^ 26

theorem lgRho_lo : lgRhoLo ≤ Real.log (65 / 64) := by
  have h : Real.exp lgRhoLo ≤ 65 / 64 := by
    refine exp_le_of_sharp (by norm_num [lgRhoLo]) (by norm_num [lgRhoLo]) ?_
    norm_num [expPoly, expErr, lgRhoLo]
  have := (Real.log_le_log_iff (Real.exp_pos _) (by norm_num : (0:ℝ) < 65 / 64)).mpr h
  rwa [Real.log_exp] at this

theorem lgRho_hi : Real.log (65 / 64) ≤ lgRhoHi := by
  have h : (65 / 64 : ℝ) ≤ Real.exp lgRhoHi := by
    refine le_exp_of_sharp (by norm_num [lgRhoHi]) (by norm_num [lgRhoHi]) ?_
    norm_num [expPoly, expErr, lgRhoHi]
  have := (Real.log_le_log_iff (by norm_num : (0:ℝ) < 65 / 64) (Real.exp_pos _)).mpr h
  rwa [Real.log_exp] at this

/-- `log (65/64) = log 65 − log 64`. -/
theorem log_rho_eq : Real.log (65 / 64) = Real.log 65 - Real.log 64 :=
  Real.log_div (by norm_num) (by norm_num)

/-- `log (x·2^m·64^j) = log x + m·log 2 + j·log 64`. -/
theorem logSplit {x : ℝ} (hx : 0 < x) (m j : ℕ) :
    Real.log (x * 2 ^ m * 64 ^ j) = Real.log x + m * Real.log 2 + j * Real.log 64 := by
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow, Real.log_pow]

/-- `log (65^j · exp c) = j·log 65 + c`. -/
theorem logExpSplit (j : ℕ) (c : ℝ) :
    Real.log ((65:ℝ) ^ j * Real.exp c) = j * Real.log 65 + c := by
  rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos c)), Real.log_pow, Real.log_exp]

/-- **Upper bound on `log x`, fast route.**  `m` and `j` are the two reduction
exponents and `c` the rational witness for the twice-reduced logarithm. -/
theorem log_le_fast (m j : ℕ) (c : ℝ) {x b : ℝ}
    (h : 0 < x ∧ -(1 / 128) ≤ c ∧ c ≤ 1 / 128 ∧
      x * 2 ^ m * 64 ^ j ≤ 65 ^ j * (expPoly8 c - expErr8) ∧
      c + j * lgRhoHi - m * log2Lo ≤ b) :
    Real.log x ≤ b := by
  obtain ⟨hx, hc1, hc2, hxc, hb⟩ := h
  have hpos : (0:ℝ) < x * 2 ^ m * 64 ^ j := by positivity
  have h65 : (0:ℝ) < (65:ℝ) ^ j := by positivity
  have hexp : x * 2 ^ m * 64 ^ j ≤ 65 ^ j * Real.exp c := by
    refine hxc.trans ?_
    have := le_exp_of8 (lo := expPoly8 c - expErr8) hc1 hc2 le_rfl
    nlinarith
  have hq : (0:ℝ) < (65:ℝ) ^ j * Real.exp c := by positivity
  have hlog := (Real.log_le_log_iff hpos hq).mpr hexp
  rw [logSplit hx, logExpSplit] at hlog
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrho : Real.log 65 - Real.log 64 ≤ lgRhoHi := log_rho_eq ▸ lgRho_hi
  nlinarith [log_two_lo, hlog, hb, hrho]

/-- **Lower bound on `log x`, fast route.** -/
theorem le_log_fast (m j : ℕ) (c : ℝ) {x a : ℝ}
    (h : 0 < x ∧ -(1 / 128) ≤ c ∧ c ≤ 1 / 128 ∧
      65 ^ j * (expPoly8 c + expErr8) ≤ x * 2 ^ m * 64 ^ j ∧
      a ≤ c + j * lgRhoLo - m * log2Hi) :
    a ≤ Real.log x := by
  obtain ⟨hx, hc1, hc2, hxc, ha⟩ := h
  have hpos : (0:ℝ) < x * 2 ^ m * 64 ^ j := by positivity
  have h65 : (0:ℝ) < (65:ℝ) ^ j := by positivity
  have hexp : (65:ℝ) ^ j * Real.exp c ≤ x * 2 ^ m * 64 ^ j := by
    refine le_trans ?_ hxc
    have := exp_le_of8 (hi := expPoly8 c + expErr8) hc1 hc2 le_rfl
    nlinarith
  have hq : (0:ℝ) < (65:ℝ) ^ j * Real.exp c := by positivity
  have hlog := (Real.log_le_log_iff hq hpos).mpr hexp
  rw [logSplit hx, logExpSplit] at hlog
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrho : lgRhoLo ≤ Real.log 65 - Real.log 64 := log_rho_eq ▸ lgRho_lo
  nlinarith [log_two_hi, hlog, ha, hrho]

/-- **The packaged two-sided enclosure, fast route.**  One call, two rational
witnesses, one `norm_num` side condition. -/
theorem log_enclosure_fast (m j : ℕ) (cLo cHi : ℝ) {x a b : ℝ}
    (h : 0 < x ∧ (-(1 / 128) ≤ cLo ∧ cLo ≤ 1 / 128) ∧
      (-(1 / 128) ≤ cHi ∧ cHi ≤ 1 / 128) ∧
      65 ^ j * (expPoly8 cLo + expErr8) ≤ x * 2 ^ m * 64 ^ j ∧
      x * 2 ^ m * 64 ^ j ≤ 65 ^ j * (expPoly8 cHi - expErr8) ∧
      a ≤ cLo + j * lgRhoLo - m * log2Hi ∧ cHi + j * lgRhoHi - m * log2Lo ≤ b) :
    a ≤ Real.log x ∧ Real.log x ≤ b := by
  obtain ⟨hx, ⟨h1, h1'⟩, ⟨h2, h2'⟩, h3, h4, h5, h6⟩ := h
  exact ⟨le_log_fast m j cLo ⟨hx, h1, h1', h3, h5⟩,
    log_le_fast m j cHi ⟨hx, h2, h2', h4, h6⟩⟩

/-- The packaged two-sided enclosure for `x ≤ 1`: one call, two rational
witnesses `cLo ≤ cHi`, one `norm_num` side condition. -/
theorem log_enclosure (m : ℕ) (cLo cHi : ℝ) {x a b : ℝ}
    (h : 0 < x ∧ (-1 ≤ cLo ∧ cLo ≤ 1) ∧ (-1 ≤ cHi ∧ cHi ≤ 1) ∧
      expPoly cLo + expErr ≤ x * 2 ^ m ∧
      x * 2 ^ m ≤ expPoly cHi - expErr ∧
      a ≤ cLo - m * log2Hi ∧ cHi - m * log2Lo ≤ b) :
    a ≤ Real.log x ∧ Real.log x ≤ b := by
  obtain ⟨hx, ⟨h1, h1'⟩, ⟨h2, h2'⟩, h3, h4, h5, h6⟩ := h
  exact ⟨le_log_of_mul_pow m cLo ⟨hx, h1, h1', h3, h5⟩,
    log_le_of_mul_pow m cHi ⟨hx, h2, h2', h4, h6⟩⟩

end OmegaBound.Interval

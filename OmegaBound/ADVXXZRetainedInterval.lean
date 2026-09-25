import OmegaBound.IntervalXLogX
import OmegaBound.IntervalExp

/-!
# Tight one-sided intervals for the retained-capacity certificate

The released `R1`--`R13` endpoints have only a few `10^-21` of provenance
slack.  The general interval API deliberately uses a cheaper degree-seven
logarithm core and a 21-decimal `log 2`; that is ideal for most call sites but
loses just enough to miss three retained rows.  This local layer uses
a degree-eleven reduced exponential and pins `log 2` to 25 decimals.  It does
not change any shared interval module.
-/

namespace OmegaBound.ADVXXZRetainedInterval

open Finset
open OmegaBound.Interval

/-- `sum (t^m/m!)` for `m < 12`, in Horner form. -/
noncomputable def expPoly12 (t : ℝ) : ℝ :=
  1 + t / 1 * (1 + t / 2 * (1 + t / 3 * (1 + t / 4 * (1 + t / 5 *
  (1 + t / 6 * (1 + t / 7 * (1 + t / 8 * (1 + t / 9 * (1 + t / 10 *
  (1 + t / 11))))))))))

noncomputable def expErr12Coeff : ℝ := 13 / ((Nat.factorial 12 : ℝ) * 12)

theorem expPoly12_eq (t : ℝ) :
    expPoly12 t = ∑ m ∈ Finset.range 12, t ^ m / (Nat.factorial m : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num [expPoly12]
  ring

/-- Sharp degree-eleven exponential enclosure.  The generator keeps the
argument inside `[-1/128,1/128]`, where this error is below `10^-33`. -/
theorem abs_exp_sub_expPoly12_le {t : ℝ} (ht : |t| ≤ 1) :
    |Real.exp t - expPoly12 t| ≤ t ^ 12 * expErr12Coeff := by
  have h := Real.exp_bound (x := t) ht (n := 12) (by norm_num)
  rw [expPoly12_eq]
  refine h.trans (le_of_eq ?_)
  rw [(Nat.even_iff.mpr rfl).pow_abs t]
  rfl

theorem expPoly12_sub_le_exp {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    expPoly12 t - t ^ 12 * expErr12Coeff ≤ Real.exp t := by
  have h := abs_le.mp (abs_exp_sub_expPoly12_le (abs_le.mpr ⟨h1, h2⟩))
  linarith [h.1]

theorem exp_le_expPoly12_add {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.exp t ≤ expPoly12 t + t ^ 12 * expErr12Coeff := by
  have h := abs_le.mp (abs_exp_sub_expPoly12_le (abs_le.mpr ⟨h1, h2⟩))
  linarith [h.2]

noncomputable def log2TightLo : ℝ := 6931471805599453094172321 / 10 ^ 25
noncomputable def log2TightHi : ℝ := 6931471805599453094172322 / 10 ^ 25

/-- A 25-decimal pin for `log 2`, proved independently by the exact artanh
remainder rather than a floating-point stationarity equation. -/
theorem log_two_tight : log2TightLo ≤ Real.log 2 ∧ Real.log 2 ≤ log2TightHi := by
  have hz : |(1 : ℝ) / 3| < 1 := by rw [abs_of_pos] <;> norm_num
  have h := OmegaBound.Interval.abs_log_div_sub_sum_le hz 64
  have harg : ((1 : ℝ) + 1 / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [harg] at h
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, log2TightLo, log2TightHi] at h ⊢
  constructor <;> linarith

/-- Tight upper logarithm reduction.  `log(65/64)` retains the shared
26-decimal proof; only the loss-amplified `m * log 2` term needs strengthening. -/
theorem log_le_fast (m j : ℕ) (c : ℝ) {x b : ℝ}
    (h : 0 < x ∧ -(1 / 128) ≤ c ∧ c ≤ 1 / 128 ∧
      x * 2 ^ m * 64 ^ j ≤ 65 ^ j * (expPoly12 c - c ^ 12 * expErr12Coeff) ∧
      c + j * lgRhoHi - m * log2TightLo ≤ b) :
    Real.log x ≤ b := by
  obtain ⟨hx, hc1, hc2, hxc, hb⟩ := h
  have hc1' : -1 ≤ c := by linarith
  have hc2' : c ≤ 1 := by linarith
  have hpos : (0 : ℝ) < x * 2 ^ m * 64 ^ j := by positivity
  have hq : (0 : ℝ) < (65 : ℝ) ^ j * Real.exp c := by positivity
  have hexp : x * 2 ^ m * 64 ^ j ≤ 65 ^ j * Real.exp c :=
    hxc.trans (mul_le_mul_of_nonneg_left (expPoly12_sub_le_exp hc1' hc2') (by positivity))
  have hlog := (Real.log_le_log_iff hpos hq).mpr hexp
  rw [OmegaBound.Interval.logSplit hx, OmegaBound.Interval.logExpSplit] at hlog
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrho : Real.log 65 - Real.log 64 ≤ lgRhoHi :=
    OmegaBound.Interval.log_rho_eq ▸ OmegaBound.Interval.lgRho_hi
  nlinarith [log_two_tight.1, hlog, hb, hrho]

/-- Tight lower logarithm reduction. -/
theorem le_log_fast (m j : ℕ) (c : ℝ) {x a : ℝ}
    (h : 0 < x ∧ -(1 / 128) ≤ c ∧ c ≤ 1 / 128 ∧
      65 ^ j * (expPoly12 c + c ^ 12 * expErr12Coeff) ≤ x * 2 ^ m * 64 ^ j ∧
      a ≤ c + j * lgRhoLo - m * log2TightHi) :
    a ≤ Real.log x := by
  obtain ⟨hx, hc1, hc2, hxc, ha⟩ := h
  have hc1' : -1 ≤ c := by linarith
  have hc2' : c ≤ 1 := by linarith
  have hpos : (0 : ℝ) < x * 2 ^ m * 64 ^ j := by positivity
  have hq : (0 : ℝ) < (65 : ℝ) ^ j * Real.exp c := by positivity
  have hexp : (65 : ℝ) ^ j * Real.exp c ≤ x * 2 ^ m * 64 ^ j :=
    (mul_le_mul_of_nonneg_left (exp_le_expPoly12_add hc1' hc2') (by positivity)).trans hxc
  have hlog := (Real.log_le_log_iff hq hpos).mpr hexp
  rw [OmegaBound.Interval.logSplit hx, OmegaBound.Interval.logExpSplit] at hlog
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrho : lgRhoLo ≤ Real.log 65 - Real.log 64 :=
    OmegaBound.Interval.log_rho_eq ▸ OmegaBound.Interval.lgRho_lo
  nlinarith [log_two_tight.2, hlog, ha, hrho]

end OmegaBound.ADVXXZRetainedInterval

#print axioms OmegaBound.ADVXXZRetainedInterval.log_two_tight

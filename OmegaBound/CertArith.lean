import OmegaBound.ADVXXZBlockTens
import OmegaBound.ADVXXZHashPat
import OmegaBound.ADVXXZSplitIface
import OmegaBound.CW90Hash
import Mathlib.Data.List.GetD
import OmegaBound.IntervalLog

/-!
# The certificate arithmetic at `q = 5`, `w = 4`

The rational constants `tauCert`, `Ecert`, `Mcert` read off the released ADVXXZ certificate, and
the scalar feasibility row `feasibility` at those constants.

## The numbers

The figures below record a floating-point evaluation of the released certificate
`W1.00_2.371339.mat`; this module proves only the displayed rational inequalities.  That
evaluation gave, in nats,

  `E_total = 2.813020984570471`,  `M_total = 2.0961236751731973`,
  `Ω_cap  = (4·log 7 − E_total)/M_total = 2.371338900716377`,

where `E_total` is the sum of the region **capacities** and `M_total` the matrix capacity.
Capacities rather than the certificate's declared `retain` values: the declared values exceed
their capacities by `3.63·10⁻¹⁰` in total, so the released point is infeasible as evaluated in
floats, by `6.2·10⁻¹⁵`.  Since the constraint is `retain ≤ capacity`, replacing each `retain`
by its capacity is both valid and optimal.

The rationals used here truncate those figures **downwards**, so they are candidate lower
bounds:

  `Ecert = 2813020984/10⁹`,  `Mcert = 20961236751/10¹⁰`,  `τcert = 2371338950/10⁹`.

## The choice of `τ`, which is delicate

`τcert` is not the obvious truncation.  Taking `τ = 23713389/10⁷` — eight digits of `Ω_cap` —
gives feasibility slack `−1.50·10⁻⁹`: **infeasible**.  `τ = 2371338901/10⁹` gives `+5.95·10⁻¹⁰`,
too tight to certify.  `τcert = 2371338950/10⁹` gives `+1.03·10⁻⁷` and is still strictly below
the target `2371339/10⁶`.

## What is proved, and what is not

Proved here: `4·log 7 ≤ Ecert + Mcert·τcert` (`feasibility`).  The comparison
`τcert < 2371339/10⁶` is `ADVXXZT9TargetArithmetic.tauCert_lt_target_kernel`.

This module does not relate `Ecert`, `Mcert` to the certificate; that comparison is made in the
`ADVXXZGeneralReleasedRetained*` modules (see `ADVXXZGeneral.feasibility_sharp`, which keeps a
`10⁻⁷`-nat reserve).  **This module by itself is not a bound on `ω`.**
-/

open Real

namespace OmegaBound

namespace CertArith

/-- The certified rational exponent, chosen strictly between `Ω_cap` and the target. -/
noncomputable def tauCert : ℝ := 2371338950 / 10 ^ 9

/-- Downward truncation of the certificate's capacity sum, in nats. -/
noncomputable def Ecert : ℝ := 2813020984 / 10 ^ 9

/-- Downward truncation of the certificate's matrix capacity, in nats. -/
noncomputable def Mcert : ℝ := 20961236751 / 10 ^ 10

set_option maxRecDepth 100000 in
/-- `log 7 ≤ 1.94591015`, by the repository's `exp`-inversion machinery at `m = 2`,
`c = 0.5596157888` (so `2² · exp c ≥ 7`). -/
theorem log_seven_le : Real.log 7 ≤ 194591015 / 10 ^ 8 := by
  refine Interval.log_le_of_div_pow 2 (5596157888 / 10 ^ 10)
    ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [Interval.expPoly, Interval.expErr]
  · norm_num [Interval.log2Hi]

/-- **Feasibility at the certificate**: the scalar feasibility row with `w = 4`, `q = 5`. -/
theorem feasibility : (4 : ℝ) * Real.log ((5 : ℝ) + 2) ≤ Ecert + Mcert * tauCert := by
  have h7 : ((5 : ℝ) + 2) = 7 := by norm_num
  rw [h7]
  have hlog := log_seven_le
  rw [Ecert, Mcert, tauCert]
  nlinarith [hlog]


theorem tauCert_nonneg : (0 : ℝ) ≤ tauCert := by rw [tauCert]; norm_num

open ADVXXZBlock ADVXXZHash CW90Eight

end CertArith

end OmegaBound

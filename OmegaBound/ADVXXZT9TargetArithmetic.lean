import OmegaBound.CertArith

/-!
# Kernel-checked comparison of `tauCert` with the target `2371339 / 10^6`

The decimal certificate is not rounded.  The only computational certificate below is the
denominator-cleared integer inequality; the real comparison is a transport of that fact.
-/

namespace OmegaBound.ADVXXZT9TargetArithmetic

/-- The exact cross-multiplied comparison
`2371338950 / 10^9 < 2371339 / 10^6`, over cleared integers. -/
theorem tauCert_lt_target_ZZ :
    (2371338950 : Int) * 10 ^ 6 < (2371339 : Int) * 10 ^ 9 := by
  decide +kernel

/-- The real comparison, recovered from the cleared-integer kernel certificate. -/
theorem tauCert_lt_target_kernel :
    CertArith.tauCert < (2371339 : Real) / 10 ^ 6 := by
  have hcross :
      (2371338950 : Real) * (10 ^ 6 : Nat) <
        (2371339 : Real) * (10 ^ 9 : Nat) := by
    exact_mod_cast tauCert_lt_target_ZZ
  rw [CertArith.tauCert]
  apply (div_lt_div_iff₀ (by positivity : (0 : Real) < 10 ^ 9)
    (by positivity : (0 : Real) < 10 ^ 6)).2
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcross

end OmegaBound.ADVXXZT9TargetArithmetic

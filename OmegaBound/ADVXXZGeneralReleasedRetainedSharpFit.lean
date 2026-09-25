import OmegaBound.AuditIrowsFrozen8

/-!
# Sharpened scalar fit for the released ordinary certificate

The certified feasibility row has more than `10⁻⁷` nats of unused slack.  Keeping that slack
explicit lets the retained-rate proof undershoot `CertArith.Ecert` by `10⁻⁷`, while reusing the
physical matrix lower bound `audit_matrix_lower` unchanged.
-/

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 4000

/-- The released scalar feasibility row with an explicit `10⁻⁷`-nat reserve.

`CertArith.log_seven_le` is too coarse by about `1.218e-9` for this strengthened row, so the
proof uses the 21-digit upper endpoint `ADVXXZCert.log_seven_le` generated from
the same interval machinery.
-/
theorem feasibility_sharp :
    (4 : ℝ) * Real.log ((5 : ℝ) + 2) + (1 : ℝ) / 10 ^ 7 ≤
      CertArith.Ecert + CertArith.Mcert * CertArith.tauCert := by
  have h7 : ((5 : ℝ) + 2) = 7 := by norm_num
  rw [h7]
  have hlog : Real.log 7 ≤ (1945910149055313305108 : ℝ) / 10 ^ 21 := by
    simpa using OmegaBound.ADVXXZCert.log_seven_le
  rw [CertArith.Ecert, CertArith.Mcert, CertArith.tauCert]
  nlinarith [hlog]

private theorem scalar_fit_sharp (E z : ℝ)
    (hE : CertArith.Ecert - (1 : ℝ) / 10 ^ 7 ≤ E)
    (hM : CertArith.Mcert ≤ z) :
    0 ≤ CertArith.tauCert ∧ 0 < z ∧
      (4 : ℝ) * Real.log ((5 : ℝ) + 2) ≤ E + CertArith.tauCert * z := by
  have hpos : 0 < CertArith.Mcert := by norm_num [CertArith.Mcert]
  refine ⟨CertArith.tauCert_nonneg, lt_of_lt_of_le hpos hM, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hM CertArith.tauCert_nonneg
  have hm' : CertArith.Mcert * CertArith.tauCert ≤ CertArith.tauCert * z := by
    simpa only [mul_comm] using hm
  have hf := feasibility_sharp
  calc
    _ ≤ (CertArith.Ecert - (1 : ℝ) / 10 ^ 7) +
        CertArith.Mcert * CertArith.tauCert := by linarith
    _ ≤ E + CertArith.tauCert * z := add_le_add hE hm'

/-- The frozen numerical fit follows from a retained-rate lower bound weakened by `10⁻⁷`. -/
theorem apply1_of_retained_lower_sharp
    (hE : CertArith.Ecert - (1 : ℝ) / 10 ^ 7 ≤
      derivedRetainedRate releasedOrdinaryCertificatePhysical) :
    S_V17_I_Apply_1 := by
  change 0 ≤ CertArith.tauCert ∧
    0 < min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .X)
      (min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Y / 1)
        (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Z)) ∧
    (4 : ℝ) * Real.log ((5 : ℝ) + 2) ≤
      derivedRetainedRate releasedOrdinaryCertificatePhysical + CertArith.tauCert *
        min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .X)
          (min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Y / 1)
            (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Z))
  simp only [div_one]
  apply scalar_fit_sharp _ _ hE
  exact le_min (audit_matrix_lower .X)
    (le_min (audit_matrix_lower .Y) (audit_matrix_lower .Z))

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.feasibility_sharp
#print axioms OmegaBound.ADVXXZGeneral.apply1_of_retained_lower_sharp

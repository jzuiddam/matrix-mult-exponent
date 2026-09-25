import OmegaBound.ADVXXZCertificateConstituentData
import OmegaBound.ADVXXZConstituentPairing

/-!
# Closing the two constituent certificate fields as far as the released data permits

All semantic certificate distributions use the same natural denominator `certificateDen`.
Hence the corrected weight

`A t r * (alpha t r u + alpha t r (complement p t u))`

has `correctedWeightDen = certificateDen ^ 2` as a common denominator, and `certificateOutBase`
is the resulting natural `outBase` table.  `certificateParentDist` is the canonical rational
mixture of the six canonical regional laws, and `certificateParentDist_probR` identifies its
probability coordinates with the `A`-weighted mixture of those laws.
-/

open Finset

namespace OmegaBound.ADVXXZCertificateConstituentClosure

open ADVXXZ (Chunk RatDist SplitDist)
open ADVXXZPaper
open ADVXXZCertSemantic
open ADVXXZCertificateConstituentData

section CertificateClosure

variable {w s : ℕ} (p : ConstituentInput w s)
variable (idx : ConstituentCertificateIndexing p)

/-- The common natural denominator of every semantic certificate simplex. -/
def certificateDen : ℕ := 116056878683004400771792896

theorem certificateDen_pos : 0 < certificateDen := by native_decide

@[simp] theorem certificateRegionDist_den (t : Fin s) :
    (certificateRegionDist p idx t).den = certificateDen := by
  rfl

@[simp] theorem certificateChildDist_den (t : Fin s) (r : Fin 6) :
    (certificateChildDist p idx t r).den = certificateDen := by
  rfl

/-- A single denominator for `A * symWeight`.  The factor two in the total symmetric mass is
kept in the numerator; it is not silently normalized away. -/
def correctedWeightDen : ℕ := certificateDen * certificateDen


/-- The integral numerator of the corrected symmetric weight, including the parent region
weight but not `p.baseN`. -/
def correctedWeightNum (x : ConstituentTerm p) : ℕ :=
  (certificateRegionDist p idx x.1).num x.2.1 *
    ((certificateChildDist p idx x.1 x.2.1).num x.2.2 +
      (certificateChildDist p idx x.1 x.2.1).num (complement p x.1 x.2.2))


/-- The natural `outBase` table obtained by clearing the common corrected-weight denominator. -/
def certificateOutBase (x : ConstituentTerm p) : ℕ :=
  correctedWeightNum p idx x * (p.baseN x.1 / correctedWeightDen)


/-- All canonical regional laws have the semantic certificate denominator. -/
@[simp] theorem certificateBetaRegion_den (W : Side) (t : Fin s) (r : Fin 6) :
    (certificateBetaRegion p idx W t r).den = certificateDen := by
  simp [certificateBetaRegion]

/-- The canonical parent law obtained by rationally mixing the six canonical regional laws. -/
noncomputable def certificateParentDist (W : Side) (t : Fin s) : SplitDist (w + w) :=
  RatDist.mix (certificateRegionDist p idx t) (certificateBetaRegion p idx W t)
    certificateDen (certificateBetaRegion_den p idx W t)

/-- The probability coordinates of the canonical parent law are exactly the `A`-weighted
mixture of the canonical regional laws. -/
theorem certificateParentDist_probR (W : Side) (t : Fin s) (σ : Chunk (w + w)) :
    (certificateParentDist p idx W t).probR σ =
      ∑ r, (certificateConstituentData p idx (certificateOutBase p idx)).A t r *
        ((certificateConstituentData p idx
          (certificateOutBase p idx)).betaRegion W t r).probR σ := by
  classical
  simp only [certificateParentDist, RatDist.probR, RatDist.mix_num, RatDist.mix_den,
    certificateConstituentData, certificateRegionDist_den, certificateBetaRegion_den,
    Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  field_simp [Nat.ne_of_gt certificateDen_pos]

end CertificateClosure

end OmegaBound.ADVXXZCertificateConstituentClosure

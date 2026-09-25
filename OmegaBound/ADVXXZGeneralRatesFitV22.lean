import OmegaBound.ADVXXZGeneralScaleAuxV22

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def CertificateNumericalFitAt (C : Certificate) (τ : ℝ) : Prop :=
  let z := min (derivedMatrixRateAt C .X)
    (min (derivedMatrixRateAt C .Y/C.kappa) (derivedMatrixRateAt C .Z))
  0 ≤ τ ∧ 0 < z ∧
    C.width*Real.log (C.q+2:ℝ) ≤ derivedRetainedRate C + τ*z

end OmegaBound.ADVXXZGeneral
end

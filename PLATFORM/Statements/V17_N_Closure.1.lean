/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_N_Closure.1
paper_clause: numerical feasible-parameter limit interpretation (P/numerical.tex:25–28,36–53).
sha256: 7d431e2ba16f9d0d374e860efc9c284b80f678729605a5e48abae333fb59d8a3
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralEndpointDefs
import OmegaBound.ADVXXZGeneralCertScaleV22
import OmegaBound.ADVXXZGeneralRatesFitV22

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_N_Closure_1 : Prop :=
  ∀ (F : Type u) [Field F] (C : Certificate),
    AdmissibleAt C → ∀ (τ : ℝ), CertificateNumericalFitAt C τ →
      omegaRect F C.kappa ≤ τ

end OmegaBound.ADVXXZGeneral
end

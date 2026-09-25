/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Apply.1
paper_clause: substitute the checked released rates into the numerical principle (P/numerical.tex:36–40,57–60).
sha256: 7b87bfb76d785fa94df2cf025d8e94a6d035edfde9ba5f57e5ee30153d09cbf3
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralRatesFitV22
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysical
import OmegaBound.CertArith

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_I_Apply_1 : Prop :=
  CertificateNumericalFitAt releasedOrdinaryCertificatePhysical CertArith.tauCert

end OmegaBound.ADVXXZGeneral
end

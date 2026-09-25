/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Apply.2
paper_clause: substitute the checked released rates into the numerical principle (P/numerical.tex:36–40,57–60).
sha256: cf55e16c95635c41fc87343f1f73cdf1896f732d4ee857ca44afc0e10337149c
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralEndpointDefs
import OmegaBound.CertArith

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_I_Apply_2 : Prop :=
  ∀ (F : Type u) [Field F], omegaMM F ≤ CertArith.tauCert

end OmegaBound.ADVXXZGeneral
end

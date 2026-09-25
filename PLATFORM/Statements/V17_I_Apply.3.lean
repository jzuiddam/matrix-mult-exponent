/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Apply.3
paper_clause: substitute the checked released rates into the numerical principle (P/numerical.tex:36–40,57–60).
sha256: 4952e50bd00127999e13a645c02fda623fdd67d7b2c4474c50ab2b86b90c3e8e
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

namespace OmegaBound.ADVXXZFinal
def S_V17_I_Apply_3 : Prop :=
  omegaMM ℚ ≤ CertArith.tauCert
end OmegaBound.ADVXXZFinal

end

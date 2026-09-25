/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Apply.4
paper_clause: the retained residual of the released numerical fit: Ecert ≤ the derived retained rate of the released ordinary certificate (add the logarithmic retained contributions of the global stage and the ordinary recursion, then substitute the lower bound into the final inequality; P/numerical.tex:8–28,36–40).
sha256: c1d97c2f54a79383534fe542813da3b44b689850e83c5f1fb0692b9690d68acf
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows
import OmegaBound.ADVXXZGeneralRowsSource30Assembly
import OmegaBound.ADVXXZCertClose
import OmegaBound.CertArith

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open OmegaBound.ADVXXZGeneral
open scoped BigOperators
namespace P2M.V17_I_Apply
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
def S_V17_I_Apply_4 : Prop :=
  OmegaBound.CertArith.Ecert ≤
    derivedRetainedRate releasedOrdinaryCertificatePhysical
end P2M.V17_I_Apply
end

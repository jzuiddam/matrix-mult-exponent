/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Rows.10
paper_clause: the released level-three retained leg: R2+…+R7 ≤ the paper constituent rate at the released level-three data at stage scale (sum every parent per direction before the regional minimum, then the six regions; P/constituent.tex:128–134), feeding P/numerical.tex:24–28,36–40.
sha256: 1c23401d8ecd8179ba6995fcaac70f65f4a9317f1e8f52a5f8f4ad17f052c04a
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
namespace P2M.V17_I_Rows
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
def S_V17_I_Rows_10 : Prop :=
  (OmegaBound.ADVXXZCert.R2 + OmegaBound.ADVXXZCert.R3 + OmegaBound.ADVXXZCert.R4 +
      OmegaBound.ADVXXZCert.R5 + OmegaBound.ADVXXZCert.R6 + OmegaBound.ADVXXZCert.R7) ≤
    cRate releasedConstituentSpec * (constituentBaseTotal releasedParent : ℝ) /
      (releasedCertificate.D : ℝ) ^ 2
end P2M.V17_I_Rows
end

/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_I_Rows.8
paper_clause: interpret numerical entropy rows and specialize the printed directional minima (P/constituent.tex:128–134; P/global.tex:88–90; P/numerical.tex:36–40).
sha256: bd2ed168a92db28b6f433504f0daf0217b19f7ad8782102f440834af03efd1ec
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRows

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
def S_V17_I_Rows_8 : Prop :=
  derivedRetainedRate releasedOrdinaryCertificatePhysical = derivedRetainedRate physicalLegacyCertificate +
    OmegaBound.ADVXXZLevel2Closure.symmetricRate OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms ∧
  ∀ W, derivedMatrixRateAt releasedOrdinaryCertificatePhysical W =
    OmegaBound.ADVXXZReleasedTree.releasedLevel2Matrix (OmegaBound.ADVXXZT6Round82.sideIndex W) +
    OmegaBound.ADVXXZReleasedTree.releasedLevel3Matrix (OmegaBound.ADVXXZT6Round82.sideIndex W)
end P2M.V17_I_Rows
end

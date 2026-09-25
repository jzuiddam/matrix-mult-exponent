import OmegaBound.ADVXXZGeneralReleasedOrdinaryCertificate

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

def physicalSideIndex : Side → Fin 3
  | .X => 0
  | .Y => 1
  | .Z => 2

def physicalGlobalBeta (W : Side) (r : Fin 6) (u : Shape 4) : SplitDist 4 :=
  OmegaBound.ADVXXZG1.betaIdx r
    (OmegaBound.ADVXXZG1.roleAt r (physicalSideIndex W))
    (OmegaBound.ADVXXZT2.logRow r (OmegaBound.ADVXXZCertRegionalSemantic.shapeIndex u))

noncomputable def physicalGlobalSpec : GlobalSpec 4 where
  A := OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist
  alpha := OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist
  beta := physicalGlobalBeta
  perm := releasedPerm
  joint := OmegaBound.ADVXXZCertificateGlobalData.certificateJoint

noncomputable def physicalLegacyCertificate : Certificate :=
  { releasedCertificate with global := physicalGlobalSpec }

noncomputable def releasedOrdinaryCertificatePhysical : Certificate where
  q := 5
  width := 4
  top := 3
  kappa := 1
  global := physicalGlobalSpec
  stage := releasedOrdinaryStage
  D := ordinaryD^2
  modulus := releasedCertificate.modulus

end OmegaBound.ADVXXZGeneral
end

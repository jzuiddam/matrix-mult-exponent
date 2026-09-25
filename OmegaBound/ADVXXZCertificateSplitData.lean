import OmegaBound.ADVXXZCertificateSplitDataResX00
import OmegaBound.ADVXXZCertificateSplitDataResX01
import OmegaBound.ADVXXZCertificateSplitDataResX02
import OmegaBound.ADVXXZCertificateSplitDataResX03
import OmegaBound.ADVXXZCertificateSplitDataResX04
import OmegaBound.ADVXXZCertificateSplitDataResX05
import OmegaBound.ADVXXZCertificateSplitDataResY00
import OmegaBound.ADVXXZCertificateSplitDataResY01
import OmegaBound.ADVXXZCertificateSplitDataResY02
import OmegaBound.ADVXXZCertificateSplitDataResY03
import OmegaBound.ADVXXZCertificateSplitDataResY04
import OmegaBound.ADVXXZCertificateSplitDataResY05
import OmegaBound.ADVXXZCertificateSplitDataResZ00
import OmegaBound.ADVXXZCertificateSplitDataResZ01
import OmegaBound.ADVXXZCertificateSplitDataResZ02
import OmegaBound.ADVXXZCertificateSplitDataResZ03
import OmegaBound.ADVXXZCertificateSplitDataResZ04
import OmegaBound.ADVXXZCertificateSplitDataResZ05
import OmegaBound.ADVXXZCertificateGlobalData
import OmegaBound.ADVXXZEpsCnt
import OmegaBound.ADVXXZShufCW

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OmegaBound.ADVXXZCertificateSplitData

open ADVXXZ (SplitDist)
open ADVXXZHash (Pat)
open ADVXXZPaper (GlobalData Shape Side)

/-- The integral certificate complete-split distribution at a typed shape index. -/
def certificateSplitByIndex :
    Side → ADVXXZCertSemantic.GlobalShapeId → SplitDist 4
  | .X, shape => match shape.1 with
    | 0 => resXRow00Dist
    | 1 => resXRow01Dist
    | 2 => resXRow02Dist
    | 3 => resXRow03Dist
    | 4 => resXRow04Dist
    | 5 => resXRow05Dist
    | 6 => resXRow06Dist
    | 7 => resXRow07Dist
    | 8 => resXRow08Dist
    | 9 => resXRow09Dist
    | 10 => resXRow10Dist
    | 11 => resXRow11Dist
    | 12 => resXRow12Dist
    | 13 => resXRow13Dist
    | 14 => resXRow14Dist
    | 15 => resXRow15Dist
    | 16 => resXRow16Dist
    | 17 => resXRow17Dist
    | 18 => resXRow18Dist
    | 19 => resXRow19Dist
    | 20 => resXRow20Dist
    | 21 => resXRow21Dist
    | 22 => resXRow22Dist
    | 23 => resXRow23Dist
    | 24 => resXRow24Dist
    | 25 => resXRow25Dist
    | 26 => resXRow26Dist
    | 27 => resXRow27Dist
    | 28 => resXRow28Dist
    | 29 => resXRow29Dist
    | 30 => resXRow30Dist
    | 31 => resXRow31Dist
    | 32 => resXRow32Dist
    | 33 => resXRow33Dist
    | 34 => resXRow34Dist
    | 35 => resXRow35Dist
    | 36 => resXRow36Dist
    | 37 => resXRow37Dist
    | 38 => resXRow38Dist
    | 39 => resXRow39Dist
    | 40 => resXRow40Dist
    | 41 => resXRow41Dist
    | 42 => resXRow42Dist
    | 43 => resXRow43Dist
    | 44 => resXRow44Dist
    | _ => resXRow44Dist
  | .Y, shape => match shape.1 with
    | 0 => resYRow00Dist
    | 1 => resYRow01Dist
    | 2 => resYRow02Dist
    | 3 => resYRow03Dist
    | 4 => resYRow04Dist
    | 5 => resYRow05Dist
    | 6 => resYRow06Dist
    | 7 => resYRow07Dist
    | 8 => resYRow08Dist
    | 9 => resYRow09Dist
    | 10 => resYRow10Dist
    | 11 => resYRow11Dist
    | 12 => resYRow12Dist
    | 13 => resYRow13Dist
    | 14 => resYRow14Dist
    | 15 => resYRow15Dist
    | 16 => resYRow16Dist
    | 17 => resYRow17Dist
    | 18 => resYRow18Dist
    | 19 => resYRow19Dist
    | 20 => resYRow20Dist
    | 21 => resYRow21Dist
    | 22 => resYRow22Dist
    | 23 => resYRow23Dist
    | 24 => resYRow24Dist
    | 25 => resYRow25Dist
    | 26 => resYRow26Dist
    | 27 => resYRow27Dist
    | 28 => resYRow28Dist
    | 29 => resYRow29Dist
    | 30 => resYRow30Dist
    | 31 => resYRow31Dist
    | 32 => resYRow32Dist
    | 33 => resYRow33Dist
    | 34 => resYRow34Dist
    | 35 => resYRow35Dist
    | 36 => resYRow36Dist
    | 37 => resYRow37Dist
    | 38 => resYRow38Dist
    | 39 => resYRow39Dist
    | 40 => resYRow40Dist
    | 41 => resYRow41Dist
    | 42 => resYRow42Dist
    | 43 => resYRow43Dist
    | 44 => resYRow44Dist
    | _ => resYRow44Dist
  | .Z, shape => match shape.1 with
    | 0 => resZRow00Dist
    | 1 => resZRow01Dist
    | 2 => resZRow02Dist
    | 3 => resZRow03Dist
    | 4 => resZRow04Dist
    | 5 => resZRow05Dist
    | 6 => resZRow06Dist
    | 7 => resZRow07Dist
    | 8 => resZRow08Dist
    | 9 => resZRow09Dist
    | 10 => resZRow10Dist
    | 11 => resZRow11Dist
    | 12 => resZRow12Dist
    | 13 => resZRow13Dist
    | 14 => resZRow14Dist
    | 15 => resZRow15Dist
    | 16 => resZRow16Dist
    | 17 => resZRow17Dist
    | 18 => resZRow18Dist
    | 19 => resZRow19Dist
    | 20 => resZRow20Dist
    | 21 => resZRow21Dist
    | 22 => resZRow22Dist
    | 23 => resZRow23Dist
    | 24 => resZRow24Dist
    | 25 => resZRow25Dist
    | 26 => resZRow26Dist
    | 27 => resZRow27Dist
    | 28 => resZRow28Dist
    | 29 => resZRow29Dist
    | 30 => resZRow30Dist
    | 31 => resZRow31Dist
    | 32 => resZRow32Dist
    | 33 => resZRow33Dist
    | 34 => resZRow34Dist
    | 35 => resZRow35Dist
    | 36 => resZRow36Dist
    | 37 => resZRow37Dist
    | 38 => resZRow38Dist
    | 39 => resZRow39Dist
    | 40 => resZRow40Dist
    | 41 => resZRow41Dist
    | 42 => resZRow42Dist
    | 43 => resZRow43Dist
    | 44 => resZRow44Dist
    | _ => resZRow44Dist

/-- The named certificate `SplitDist` family, indexed by level triple. -/
def certificateSplit (S : Side) (u : Pat (2 * 4)) : SplitDist 4 :=
  certificateSplitByIndex S (ADVXXZCertSemantic.shapeIndex u)

/-- The certificate family, repeated across the six global regions. -/
def certificateBeta : Side → Fin 6 → Shape 4 → SplitDist 4 :=
  fun S _ u => certificateSplit S u

/-- Global certificate data callable without a caller-supplied `beta`. -/
noncomputable def certificateGlobalData : GlobalData 4 :=
  ADVXXZCertificateGlobalData.certificateGlobalData certificateBeta

end OmegaBound.ADVXXZCertificateSplitData

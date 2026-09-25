import OmegaBound.ADVXXZT6WordLaw

/-!
# Corrected downward multiplicities versus released `term_frac`

`ADVXXZT2Mult` gives the corrected symmetric natural multiplicities `mlt`.  This file checks that,
after multiplying by the actual global parent cell mass, those multiplicities are exactly the
`frac` fields of the 5,508 released level-2 records.
Zero regional slots are recorded explicitly and are not turned into zero-length interface
factors.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT6

open ADVXXZCertSemantic (Level3Incidence level3Incidence)
open ADVXXZReleasedTree (releasedLevel2TermDataTable)
open ADVXXZT2 (certDen logRow mlt parRegion parRow)

def incidenceArray : Array Level3Incidence := level3Incidence.toArray

/-- Physical global-cell numerator of the parent owning occurrence `e`. -/
def parentCellNum (e : Level3Incidence) : ℕ :=
  let r := parRegion e.parent.val
  let row := parRow e.parent.val
  ADVXXZCertificateGlobalData.Certificate.regionDist.num r *
    ADVXXZG1.aw r (logRow r row)

/-- The corrected propagated fraction reconstructed solely from the parent cell and the
occurrence multiplicity `mlt`. -/
def reconstructedFrac (e : Level3Incidence) : ℚ :=
  (parentCellNum e : ℚ) * ((mlt e.parent.val e.region.val).getD e.coordinate.val 0 : ℚ) /
    ((certDen : ℚ) ^ 4)

def active (e : Level3Incidence) : Bool :=
  0 < (mlt e.parent.val e.region.val).getD e.coordinate.val 0

/-- One released occurrence has the correct fraction at both committed downward endpoints.
The incidence-list position is deliberately not used as a registry node ID. -/
def fracRowOK (i : ℕ) : Bool :=
  match incidenceArray[i]? with
  | some e =>
      match termDataArray[e.left.val]?, termDataArray[e.right.val]? with
      | some dl, some dr =>
          (dl.node.val == e.left.val) && (dr.node.val == e.right.val) &&
          (dl.frac == reconstructedFrac e) && (dr.frac == reconstructedFrac e) &&
          ((dl.frac == 0) == !active e) && ((dr.frac == 0) == !active e)
      | _, _ => false
  | none => false

/-- Exact provenance plus the committed-downward-endpoint census. -/
def fracOK : Bool :=
  (List.range 5508).all fracRowOK &&
    (level3Incidence.countP (fun e => active e) == 3708) &&
    (level3Incidence.countP (fun e => !active e) == 1800)

/-- Proposition-facing form of the released-fraction audit. -/
def FracLaw : Prop := fracOK = true

instance : Decidable FracLaw := by unfold FracLaw; infer_instance

set_option maxHeartbeats 8000000 in
-- This is a streaming 5,508-row exact rational comparison against the released registry.
/-- **THE RELEASED FRACTIONS ARE THE CORRECTED MULTIPLICITIES.**  Every incidence is
checked at both explicit downward endpoints.  The census exposes exactly `3,708` positive and
`1,800` zero-weight occurrences, so a downstream producer can retain only committed positive
endpoints instead of manufacturing zero-length interface factors. -/
theorem frac_law : FracLaw := by native_decide

end ADVXXZT6
end OmegaBound

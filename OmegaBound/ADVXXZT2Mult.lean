import OmegaBound.ADVXXZT2Base

/-!
# The multiplicity closure over the released general parents

`MultOK` states, at every one of the `126` general parents and each of its six constituent
regions: the region simplex partitions the parent; every regional child simplex has one entry per
admissible child shape, totals the common denominator `certDen` and has every weight positive;
the corrected symmetric weight `symW` and the natural multiplicity `mlt` are reflection
invariant; the symmetric weights reassemble the parent's leg budget; and over the whole parent
the symmetric mass is exactly `2 * certDen²` and the one-sided mass exactly `certDen²`.
`mult_ok` checks `MultOK` by `native_decide`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT2

open ADVXXZCertSemantic (level3Specs Level3TermId GeneralTermId Level2TermId)
open ADVXXZG2 (isGeneralL3 genList dummySpec)

/-! ## §1  Addressing the released tables -/

/-- The offset of a level-3 node's own block of stored tables: a boundary leaf occupies one, a
general parent occupies seven. -/
def specBase (i : ℕ) : ℕ := ((List.range i).map (fun j => if isGeneralL3 j then 7 else 1)).sum

/-- The `Level3TermId` of the `p`-th general parent. -/
def genId (p : ℕ) : ℕ := genList.getD p 0

/-- The `p`-th general parent's released shape. -/
def parShapeOf (p : ℕ) : Sh := nodeShape (genId p)

/-- The `p`-th general parent's complete admissible child support. -/
def parKids (p : ℕ) : List Sh := admiss (parShapeOf p)

/-- The `p`-th general parent's released six-entry region simplex. -/
def regNums (p : ℕ) : List ℕ := (level3Specs.getD (specBase (genId p)) dummySpec).nums

/-- The `p`-th general parent's released child-split simplex in constituent region `r`. -/
def chNums (p r : ℕ) : List ℕ := (level3Specs.getD (specBase (genId p) + 1 + r) dummySpec).nums

/-- **THE CORRECTED SYMMETRIC OUTPUT WEIGHT** of a whole simplex: `alpha(u) + alpha(s - u)`, with
the complement realised by list reversal — which `ADVXXZT2Base.admiss_laws` proves *is* the
released complement `t ↦ s - t`. -/
def symW (al : List ℕ) : List ℕ := List.zipWith (· + ·) al al.reverse

/-- **THE EXACT NATURAL MULTIPLICITIES** of one `(parent, region)` block at `certDen²` parent
copies: region weight times corrected symmetric child weight. -/
def mlt (p r : ℕ) : List ℕ := (symW (chNums p r)).map (fun w => (regNums p).getD r 0 * w)

/-! ## §2  The closure, per parent

Every arithmetic law is stated against the admissible child support `admiss`, which needs no
`level2ShapeTable` lookup. -/

/-- **THE UNIVERSAL PER-PARENT LAWS.**  All `126` general parents, all `6` constituent regions. -/
def MultOK : Prop :=
  ∀ p ∈ List.range 126,
    -- the region simplex partitions the parent
    (regNums p).length = 6
    ∧ (regNums p).sum = certDen
    -- every regional child simplex partitions its region, at the released support
    ∧ (∀ r ∈ List.range 6,
        (chNums p r).length = (parKids p).length
        ∧ (chNums p r).sum = certDen
        ∧ (∀ a ∈ chNums p r, 0 < a)
        -- the corrected symmetric weight is reflection invariant
        ∧ symW (chNums p r) = (symW (chNums p r)).reverse
        -- so is the exact natural multiplicity
        ∧ mlt p r = (mlt p r).reverse
        -- regional reassembly, leg by leg
        ∧ (∀ l ∈ List.range 3,
            (List.zipWith (fun w x => w * (legs x).getD l 0) (symW (chNums p r)) (parKids p)).sum
              = (legs (parShapeOf p)).getD l 0 * certDen)
        -- and region by region: two halves per parent copy
        ∧ (mlt p r).sum = 2 * ((regNums p).getD r 0 * certDen))
    -- zero discarded, zero duplicated, over the whole parent
    ∧ ((List.range 6).map (fun r => (mlt p r).sum)).sum = 2 * (certDen * certDen)
    ∧ ((List.range 6).map (fun r => (regNums p).getD r 0 * (chNums p r).sum)).sum
        = certDen * certDen
    -- full reassembly of the parent's leg budget over all six regions
    ∧ (∀ l ∈ List.range 3,
        ((List.range 6).map (fun r =>
          (List.zipWith (fun w x => w * (legs x).getD l 0) (mlt p r) (parKids p)).sum)).sum
          = (legs (parShapeOf p)).getD l 0 * (certDen * certDen))

instance : Decidable MultOK := by unfold MultOK; infer_instance

/-- **THE PER-PARENT CLOSURE.** -/
theorem mult_ok : MultOK := by native_decide

/-! ### A measured structural fact that the checker must *not* assume

Every child weight is positive, and it is tempting to add the same clause for the six
**regional** weights.  It is false: `228` of the `756` released
`(parent, region)` slots carry regional weight exactly `0`, so `228` of the constituent-stage
regional inventories are genuinely empty.  Recording the number here keeps a later producer from
assuming a positive regional mass it does not have; the child weights *are* all positive, and
`MultOK` says so. -/

end ADVXXZT2
end OmegaBound

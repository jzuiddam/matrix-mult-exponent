import OmegaBound.ADVXXZCertSemantic
import OmegaBound.ADVXXZReleasedTree
import OmegaBound.ADVXXZCertificateConstituentClosure

/-!
# G2, part 1: the gate fixture — one released positive-coordinate parent

This module fixes the data of
**the first released positive-coordinate parent whose child support contains both a `112`
occurrence and a boundary occurrence**, at **the smallest positive multiplier of the relevant
common denominator**.

That parent is `ADVXXZCertSemantic.GeneralTermId 0`:

* it is `Level3TermId 10`, released shape `(1, 1, 6)`, global region `0`
  (`ADVXXZReleasedTree.releasedTree.level3Class` says `.general`, i.e. all three coordinates are
  positive);
* in each of the six constituent regions it has exactly `4` released child occurrences, of
  shapes `(0,0,4)`, `(0,1,3)`, `(1,0,3)`, `(1,1,2)` in released coordinate order;
* `(1,1,2)` is a `112` occurrence and `(0,0,4)`, `(0,1,3)`, `(1,0,3)` are boundary
  (zero-coordinate, matrix-producing) occurrences.  At level `2` the `112` class is *exactly* the
  all-positive class, so "112 or boundary" is a dichotomy, not a sample.

This module records that parent's released weights and cleared natural multiplicities.

## The common denominator, and the multiplier

Every semantic certificate simplex has denominator
`ADVXXZCertificateConstituentClosure.certificateDen = 3 * 2^85`.  The corrected symmetric output
weight `A_r * (alpha(u) + alpha(s - u))` therefore has common denominator
`correctedWeightDen = certificateDen ^ 2`.  The **smallest positive
multiplier** of that denominator is `1`, so the gate runs at

```text
baseN = 1 * correctedWeightDen = 9 * 2 ^ 170.
```

## The corrected weight, not the printed one-sided weight

The constituent stage pairs a child shape `u` with `s_T - u`, so the output weight is the
symmetric `alpha(u) + alpha(s_T - u)` (`ADVXXZPaper.symWeight`).  In released coordinate order the
complement is `Fin.rev` on the child index.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.style.longLine false

open Finset

namespace OmegaBound
namespace ADVXXZG2

open ADVXXZCertSemantic

/-! ## §1  The gate parent -/

/-- The gate parent's released level-3 shape. -/
def parShape : ℕ × ℕ × ℕ := (1, 1, 6)

/-! ## §2  Projecting a released level-3 incidence row

`l3sig` projects a released `Level3Incidence` onto naturals. -/

/-- `(parent, region, coordinate, parentSize, left, right)`. -/
def l3sig (e : Level3Incidence) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (e.parent.val, e.region.val, e.coordinate.val, e.parentSize, e.left.val, e.right.val)

/-! ## §3  The released rational weights, and the cleared natural multiplicities -/

/-- The one denominator of every semantic certificate simplex, `3 * 2 ^ 85`. -/
def den : ℕ := ADVXXZCertificateConstituentClosure.certificateDen

/-- The corrected-weight denominator `den ^ 2`. -/
def wden : ℕ := ADVXXZCertificateConstituentClosure.correctedWeightDen

/-- **THE SMALLEST POSITIVE MULTIPLIER** of the corrected-weight denominator. -/
def baseN : ℕ := 1 * wden

/-- The released six-entry region simplex of the gate parent
(`level3Specs` index `10`, source slots `3061-3066`). -/
def regA : Fin 6 → ℕ :=
  ![19333767933003093094957056, 19344943440278824301887488, 19334183436308156617064448,
    19344861560501052905619456, 19349461890922498907701248, 19349660421990774944563200]

/-- The released regional child-split simplexes of the gate parent
(`level3Specs` indices `11-16`, source slots `3067-3090`), in released coordinate order. -/
def chAlpha : Fin 6 → Fin 4 → ℕ :=
  ![![13306251741070042966523904, 44722099133833505478279168, 44722190100656657465868288,
     13306337707444194861121536],
    ![13261598789703106522251264, 44766807397079884197003264, 44766834672827424181321728,
     13261637823393985871216640],
    ![13306013593052607575752704, 44722440615168515323723776, 44722362628986517655126016,
     13306061845796760217190400],
    ![13261675952903509638119424, 44766766097472989259890688, 44766741568786327249354752,
     13261695063841574624428032],
    ![13254255241647174073712640, 44774169089022887649607680, 44774179519373174724624384,
     13254274832961164323848192],
    ![13254162436110839162339328, 44774301363742598875840512, 44774247549444459809734656,
     13254167333706502923878400]]

/-- **THE CORRECTED SYMMETRIC OUTPUT WEIGHT**, numerator form:
`alpha(u) + alpha(parentShape - u)`, with the complement taken as `Fin.rev` on the child index. -/
def symW (r : Fin 6) (d : Fin 4) : ℕ := chAlpha r d + chAlpha r (Fin.rev d)

/-- **THE EXACT NATURAL MULTIPLICITY** of the child occurrence `(r, d)` at `baseN` parent
copies.  This is `ADVXXZCertificateConstituentClosure.certificateOutBase` at
`baseN / correctedWeightDen = 1`. -/
def mlt (r : Fin 6) (d : Fin 4) : ℕ := regA r * symW r d


/-! ## §4  A default `DistSpec` -/

/-- A default `DistSpec`; `List.getD` needs one and `DistSpec` is not `Inhabited`. -/
def dummySpec : DistSpec where
  sourceStart := 0
  sourceSize := 1
  nums := [116056878683004400771792896]
  nonempty := by decide
  sum_num := by simp

/-! ## §5  The admissible child support and the level-3 inventories -/

/-- All shapes of level `2` that fit inside the gate parent — the complete admissible child
support, enumerated independently of the released tables. -/
def admissibleSplits : List (ℕ × ℕ × ℕ) :=
  ((List.range 125).map (fun n => (n / 25, (n / 5) % 5, n % 5))).filter
    (fun s => decide (s.1 + s.2.1 + s.2.2 = 4 ∧ s.1 ≤ parShape.1 ∧ s.2.1 ≤ parShape.2.1
      ∧ s.2.2 ≤ parShape.2.2))

/-- The global-output occurrences that are general (positive-coordinate) level-3 nodes. -/
def isGeneralL3 (i : ℕ) : Bool :=
  let s := ADVXXZReleasedTree.globalShapeTable.getD (i % 45) (0, 0, 0)
  !(s.1 == 0) && !(s.2.1 == 0) && !(s.2.2 == 0)

/-- The constituent-input inventory, read off the global-output inventory. -/
def genList : List ℕ := (List.range 270).filter isGeneralL3

/-- The boundary-leaf inventory. -/
def leafList : List ℕ := (List.range 270).filter (fun i => !isGeneralL3 i)

end ADVXXZG2
end OmegaBound

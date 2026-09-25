import OmegaBound.ADVXXZCertSemantic
import OmegaBound.ADVXXZG2Fix
import OmegaBound.ADVXXZT1IncRange

/-!
# The shared vocabulary of the whole released level-3 graph

This module fixes the vocabulary in which the released level-3 graph (all `270` level-3 nodes) is
described, and kernel-decides its census:

* `nodeShapes` — the `270` released level-3 node shapes, in `Level3TermId` order;
* `admiss s` — *all* level-2 shapes that fit inside a level-3 shape `s`, enumerated
  independently of the released tables (this is `ADVXXZG2.admissibleSplits` universalised);
* the released `level3Specs` layout: a boundary leaf carries **one** complete-split table, a
  general parent carries **one** region simplex followed by **six** child-split simplexes, so the
  `1026` stored level-3 tables are `144 * 1 + 126 * 7`.

## Why `admiss` and not the released shapes

`admiss s` is the *complete* admissible child support of `s`, computed from `s` alone.  The
arithmetic laws of `ADVXXZT2Mult` are stated against `admiss`, which costs no
`level2ShapeTable` lookup.

`admiss_laws` proves, at all `45` released shapes, that the enumeration is a complete,
duplicate-free, level-`4` support closed under the complement `t ↦ s - t`, and that the
complement is exactly list reversal, i.e. the released complement edge `Fin.rev`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT2

open ADVXXZCertSemantic (level3Specs level2Specs globalSpecs Level3TermId GeneralTermId Level2TermId)
open ADVXXZReleasedTree (globalShapeTable level2ShapeTable)
open ADVXXZG2 (isGeneralL3 genList leafList)

/-! ## §1  Shapes -/

/-- A released shape triple. -/
abbrev Sh := ℕ × ℕ × ℕ

/-- The one common denominator of every released semantic simplex. -/
def certDen : ℕ := 116056878683004400771792896

/-- The released **physical** shape of a level-3 node: `Level3TermId` is `45 * region + row`. -/
def nodeShape (i : ℕ) : Sh := globalShapeTable.getD (i % 45) (0, 0, 0)

/-- The `270` released level-3 node shapes, in `Level3TermId` order. -/
def nodeShapes : List Sh := (List.range 270).map nodeShape

/-- A general (positive-coordinate) parent, as a predicate on shapes. -/
def isGenShape (s : Sh) : Bool := !(s.1 == 0) && !(s.2.1 == 0) && !(s.2.2 == 0)

/-- The three legs of a shape as a list: `0 = X`, `1 = Y`, `2 = Z`. -/
def legs (s : Sh) : List ℕ := [s.1, s.2.1, s.2.2]

/-- The released level-2 shape of a released `Level2TermId`. -/
def l2sh (n : ℕ) : Sh := level2ShapeTable.getD n (0, 0, 0)

/-- **THE COMPLETE ADMISSIBLE CHILD SUPPORT** of a level-3 shape: every level-2 shape that fits
inside it, enumerated from `s` alone.  `ADVXXZG2.admissibleSplits` is this list at the gate
parent's shape. -/
def admiss (s : Sh) : List Sh :=
  ((List.range 125).map (fun n => (n / 25, (n / 5) % 5, n % 5))).filter
    (fun t => t.1 + t.2.1 + t.2.2 == 4 && t.1 ≤ s.1 && t.2.1 ≤ s.2.1 && t.2.2 ≤ s.2.2)

/-! ## §2  The census, kernel-decided

Everything here is one pass over short lists. -/

/-- **THE RELEASED NODE CENSUS.**  `270 = 126 + 144`, `756 = 126 * 6` blocks, `5,508` level-2
shapes, and the `1026` stored level-3 tables are exactly `144 * 1 + 126 * 7`. -/
theorem census :
    nodeShapes.length = 270
    ∧ genList.length = 126
    ∧ leafList.length = 144
    ∧ level2ShapeTable.length = 5508
    ∧ globalSpecs.length = 7
    ∧ level3Specs.length = 1026
    ∧ level2Specs.length = 2700
    ∧ (nodeShapes.filter isGenShape).length = 126
    ∧ (nodeShapes.filter (fun s => !isGenShape s)).length = 144
    ∧ ((nodeShapes.map (fun s => if isGenShape s then 7 else 1)).sum = 1026)
    ∧ (∀ i ∈ List.range 270, isGenShape (nodeShape i) = isGeneralL3 i) := by
  decide +kernel

/-- **THE SHAPE-LEVEL SUPPORT LAWS.**  At every one of the `45` released shapes the admissible
enumeration is nonempty, duplicate-free, lives at level `4`, fits inside the parent, and is
closed under the complement `t ↦ s - t` — with the complement realised **exactly** by list
reversal, which is the released complement edge `Fin.rev`. -/
theorem admiss_laws : ∀ n ∈ List.range 45,
    let s := globalShapeTable.getD n (0, 0, 0)
    0 < (admiss s).length
    ∧ (admiss s).eraseDups.length = (admiss s).length
    ∧ ((admiss s).all (fun t => t.1 + t.2.1 + t.2.2 == 4 && t.1 ≤ s.1 && t.2.1 ≤ s.2.1 && t.2.2 ≤ s.2.2) = true)
    ∧ ((List.zip (admiss s) (admiss s).reverse).all
         (fun q => q.1.1 + q.2.1 == s.1 && q.1.2.1 + q.2.2.1 == s.2.1 && q.1.2.2 + q.2.2.2 == s.2.2) = true)
    ∧ ((admiss s).reverse = (admiss s).map (fun t => (s.1 - t.1, s.2.1 - t.2.1, s.2.2 - t.2.2))) := by
  decide +kernel

end ADVXXZT2
end OmegaBound

import OmegaBound.ADVXXZReleasedL2Family
import OmegaBound.ADVXXZT2Inv
import OmegaBound.ADVXXZG2Mix

/-!
# The typed special-stage inventory and its natural scale table

The released level-2 registry stores rational `term_frac` and (for `112`/`022`) rational
`split_0`.  A finite producer needs two natural numbers for every node: its number of positions
and, when applicable, the number of `0+2` positions.  The MATLAB release does not serialize that
natural table.  This module derives it, once and for all, at the common denominator
`3 * 2^253`; every later scale is a free multiplier `m` of this base.  Thus `m` is never confused
with the paper's recursion depth.

The carrier is not a freshly enumerated list: it is the occurrence equivalence
`ADVXXZT2.leftEquiv` over all `5,508` level-2 nodes.

SOURCE: VXXZ24 `analysis_constituent.tex:5-16` (heterogeneous term multiplicities and `n=sum n_t`).
SOURCE: VXXZ24 `analysis_constituent.tex:178-205` (one type class over all term parts).
SOURCE: `TermInfoLv2.m:103-154` (the per-node `term_frac`, `split_0`, and complete-split laws).
SOURCE: `Workspace.m:210-227` (all level-2 nodes are summed before one minimum).
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false

open Finset

namespace OmegaBound
namespace ADVXXZT7SpecialInventory

open ADVXXZCertSemantic (Level2TermId)
open ADVXXZReleasedTree (ReleasedLevel2TermData releasedLevel2TermDataTable)

/-- The exact common denominator of every released `frac` and every product `frac * mu`.
The free stage scale is always `m * naturalDen`, with symbolic `m : Nat`.

This is a denominator, not a frozen tensor-power choice.
-/
def naturalDen : Nat := 3 * 2 ^ 253

/-- Natural numerator of a nonnegative rational known to divide `naturalDen`. -/
def naturalNumerator (x : Rat) : Nat := x.num.natAbs * (naturalDen / x.den)

/-- Base number of positions assigned to a released node. -/
def baseCopies (d : ReleasedLevel2TermData) : Nat := naturalNumerator d.frac

/-- Base number of `0+2` positions.  Direct classes have `mu = none`, hence zero here. -/
def baseCorners (d : ReleasedLevel2TermData) : Nat :=
  naturalNumerator (d.frac * d.mu.getD 0)

/-- The complete exact audit of the derived natural table.  The last three clauses measure the
positive-`mu` `112` scope exactly: `292` live nodes in each rotation, `876` total.

This proposition deliberately says *derived*: no claim is made that the release contains a
serialized natural table.
-/
def NaturalTableLaw : Prop :=
  releasedLevel2TermDataTable.length = 5508 ∧
  (∀ d ∈ releasedLevel2TermDataTable,
    0 ≤ d.frac ∧
    d.frac = (baseCopies d : Rat) / naturalDen ∧
    d.frac * d.mu.getD 0 = (baseCorners d : Rat) / naturalDen ∧
    2 * baseCorners d ≤ baseCopies d) ∧
  releasedLevel2TermDataTable.countP (fun d => 0 < d.frac) = 3708 ∧
  releasedLevel2TermDataTable.countP (fun d => d.frac = 0) = 1800 ∧
  (∀ r : Fin 3,
    releasedLevel2TermDataTable.countP (fun d =>
      d.kind = .k112 ∧ d.rot = r ∧ 0 < d.frac ∧ 0 < d.mu.getD 0) = 292)

instance : Decidable NaturalTableLaw := by unfold NaturalTableLaw; infer_instance

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
-- One streaming exact-rational check over all 5,508 rows is the sole heavy check in this module.
/-- **THE MISSING NATURAL TABLE IS DERIVED EXACTLY AT EVERY RELEASED NODE.** -/
theorem natural_table_law : NaturalTableLaw := by native_decide

/-- Lookup by the released typed node id. -/
def dataById (i : Level2TermId) : ReleasedLevel2TermData :=
  releasedLevel2TermDataTable.get
    ⟨i.val, by rw [natural_table_law.1]; exact i.isLt⟩

/-- The left occurrence equivalence `ADVXXZT2.leftEquiv` is the carrier of the special stage. -/
noncomputable def occurrenceData (i : ADVXXZT2.Occ) : ReleasedLevel2TermData :=
  dataById (ADVXXZT2.leftEquiv i)

/-- Symbolic-in-`m` natural position count of an occurrence. -/
noncomputable def copies (m : Nat) (i : ADVXXZT2.Occ) : Nat :=
  m * baseCopies (occurrenceData i)

end ADVXXZT7SpecialInventory
end OmegaBound

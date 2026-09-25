import OmegaBound.ADVXXZT1Inc

/-!
# Uniqueness and coverage of the released level-2 ids

The second half of the universal incidence checker (`ADVXXZT1Inc` carries the first); each half
is one `native_decide` evaluation.

The first clause of `inc_range_laws` says parent and region are constant on a block; `inc_left_ranges` says each
block's left child ids, sorted, are exactly that block's own contiguous range, and that the
running offset ends at `5508`.  Together: the `756` blocks tile the whole level-2 inventory with
no gap, no overlap and no repetition — the uniqueness statement, in `O(Σ len²)` form rather than
the `O(n²)` `Nodup` that cost `48 GB`.  The right-hand side needs no check of its own: it
is the reversed left side by the reflection clause of `ADVXXZT1.inc_laws`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT1

open ADVXXZCertSemantic (level3Incidence)

/-- **UNIQUENESS AND COVERAGE.**  Two universal laws, in one `native_decide`. -/
theorem inc_range_laws :
    (∀ B ∈ blocks level3Incidence, ∀ e ∈ B, ∀ e' ∈ B, e.parent = e'.parent ∧ e.region = e'.region)
    ∧ rangeWalk (fun e => e.left.val) (blocks level3Incidence) = (5508, true) := by
  native_decide


/-- **UNIQUENESS AND COVERAGE OF THE LEFT IDS.**  Each block's left `Level2TermId`s, sorted, are
exactly that block's own contiguous range, and the running offset ends at `5508`. -/
theorem inc_left_ranges :
    rangeWalk (fun e => e.left.val) (blocks level3Incidence) = (5508, true) :=
  inc_range_laws.2


end ADVXXZT1
end OmegaBound

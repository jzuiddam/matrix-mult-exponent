import OmegaBound.ADVXXZG1Mirror
import OmegaBound.ADVXXZG1Supp
import OmegaBound.ADVXXZG2Mix
import OmegaBound.ADVXXZT1Phys

/-!
# The universal incidence checker over all 5,508 released splits

Coverage, uniqueness and every incidence endpoint of the released level-3 incidence list.

## Why a block decomposition, and not a `Nodup`

The obvious statement — `(level3Incidence.map (·.left)).Nodup` — is `O(n²)` in the kernel at
`n = 5508` (measured at 48.4 GB RSS); `List.mergeSort` is well-founded, so `decide +kernel`
cannot reduce it at all.

The statement is therefore kept `O(n)` in shape.  The released incidence list is **block-structured** — a new `(parent, region)`
block opens at each released split coordinate `0` — and `blocks` recovers those blocks in one
left-to-right pass.  Every law below is then either one pass over the `5,508` rows or a pass over
the `756` blocks with `O(len²)` work inside a block of length at most about `20`.

## What the two modules prove

| clause | module | content |
|---|---|---|
| 1, 2 | here | `5,508` incidences in `756 = 126 × 6` blocks |
| 3 | here | the blocks reassemble the released list exactly (no row invented, none dropped) |
| 4 | here | a block's length is its parent's released `parentSize` |
| 5 | here | a block's released split coordinates enumerate `0 … len-1` — **every incidence endpoint** |
| 6 | here | **the universal reflection law**: a block's right ids are its left ids reversed |
| 7 | `ADVXXZT1IncRange` | parent and region are constant on a block |
| 8 | `ADVXXZT1IncRange` | a block's left ids, sorted, are exactly its own contiguous id range |

The eight clauses are split across the two modules, each module checking its clauses in one
`native_decide` evaluation.

Clause 8 is the uniqueness statement in `O(Σ len²)` form: within a block the left ids are
distinct *and* exhaust that block's range, and the ranges tile `[0, 5508)` because the running
offset ends at `5508`; the right ids follow by the reflection clause 6.  The typed bijection is
built in `ADVXXZT2Inv`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace OmegaBound
namespace ADVXXZT1

open ADVXXZCertSemantic (Level3Incidence level3Incidence)
open ADVXXZG2 (l3sig)

/-! ## §1  The block decomposition and a kernel-reducible sort -/

/-- Chunk the released incidence list into its `(parent, region)` blocks: a new block opens at
each released split coordinate `0`.  One left-to-right pass. -/
def blocks (l : List Level3Incidence) : List (List Level3Incidence) :=
  ((l.foldl (fun (acc : List (List Level3Incidence)) e =>
      if e.coordinate.val = 0 then [e] :: acc
      else match acc with | [] => [[e]] | b :: bs => (e :: b) :: bs) []).map List.reverse).reverse

/-- Insertion into a sorted list.  Structural, so the kernel reduces it; `List.mergeSort` is
well-founded and does not. -/
def ins (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

/-- Insertion sort.  Used only inside a block, where the length is at most about `20`. -/
def isort : List ℕ → List ℕ
  | [] => []
  | a :: l => ins a (isort l)

/-- Walk the blocks left to right, accumulating the running id offset, and check that each block's
`f`-ids, sorted, are exactly that block's own contiguous range. -/
def rangeWalk (f : Level3Incidence → ℕ) (BL : List (List Level3Incidence)) : ℕ × Bool :=
  BL.foldl (fun st B =>
    (st.1 + B.length, st.2 && (isort (B.map f) == List.range' st.1 B.length))) (0, true)

/-! ## §2  THE UNIVERSAL INCIDENCE CHECKER, part 1 — structure, addressing, reflection

One `native_decide` evaluation.  The uniqueness/coverage half is `ADVXXZT1IncRange`. -/

/-- **EVERY RELEASED INCIDENCE, CHECKED: STRUCTURE, ADDRESSING, REFLECTION.**  Six universal laws
over all `5,508` released splits and all `756` blocks, in one `native_decide`. -/
theorem inc_laws :
    level3Incidence.length = 5508
    ∧ (blocks level3Incidence).length = 756
    ∧ ((blocks level3Incidence).flatten.map l3sig = level3Incidence.map l3sig)
    ∧ (∀ B ∈ blocks level3Incidence, ∀ e ∈ B, e.parentSize = B.length)
    ∧ (∀ B ∈ blocks level3Incidence, B.map (fun e => e.coordinate.val) = List.range B.length)
    ∧ (∀ B ∈ blocks level3Incidence,
        B.map (fun e => e.right.val) = (B.map (fun e => e.left.val)).reverse) := by
  native_decide

/-! ## §3  The named laws -/

/-- The released inventory: `5,508` incidences. -/
theorem inc_length : level3Incidence.length = 5508 := inc_laws.1


/-- **THE BLOCKS REASSEMBLE THE RELEASED LIST.**  No row is invented and none is dropped, so every
law stated per block is a law about every released incidence. -/
theorem inc_blocks_flatten :
    (blocks level3Incidence).flatten.map l3sig = level3Incidence.map l3sig := inc_laws.2.2.1

end ADVXXZT1
end OmegaBound

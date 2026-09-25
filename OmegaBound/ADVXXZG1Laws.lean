import OmegaBound.ADVXXZReAnchor

/-!
# G1, part 1: the slot alphabet and the law bundle for the six regional beta authorities

This module fixes the typed indices and the two law bundles `SuppOK` and `MirrorOK` over every
`(region, side, shape, chunk)` slot of the released global data; `ADVXXZG1Supp` and
`ADVXXZG1Mirror` decide them.

The authorities are `ADVXXZRA.regionalSplit` — the six committed regional families, one per
region.

## The laws, and where they come from

ADVXXZ `global.tex`, `rmk:assumptions_on_complete_split_dist`, states exactly two families of
laws on the level-`ℓ` complete split distributions `splres^{(r)}_{W,i,j,k}`:

```text
  splres_X(i,0,k)(L) = splres_Z(i,0,k)(2⃗ - L)     -- typed index j = 0
  splres_Z(0,j,k)(L) = splres_Y(0,j,k)(2⃗ - L)     -- typed index i = 0
  splres_Y(i,j,0)(L) = splres_X(i,j,0)(2⃗ - L)     -- typed index k = 0

  splres_X(i,j,k)(L) = 0  if  Σ_t L_t ≠ i, and likewise Y ↔ j, Z ↔ k
```

`SuppOK` carries the support law — in the **stronger biconditional form**: an entry is nonzero
*exactly* when its word sits at the leg's own level; the source asks only for one direction —
together with the boundary point-mass reading of the two extreme levels.  `MirrorOK` carries the
three complement/reflection laws, each guarded by its own typed index and each cross-multiplied
over `ℕ`, since the two tables of a mirror pair carry different denominators and no rational is
formed anywhere.

Normalisation and nonnegativity are structural: `ADVXXZ.RatDist` carries `den_pos` and `sum_num`
as fields and `num` is `ℕ`-valued.
-/

set_option maxHeartbeats 1000000
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset

namespace OmegaBound
namespace ADVXXZG1

open ADVXXZ (Chunk chunkLvl)
open ADVXXZHash (Pat Ix Jy Kz)
open ADVXXZPaper (Side Shape)
open ADVXXZRA (regionalSplit c0 c2)

/-! ## §1  The typed indices -/

/-- The level at which leg `S`'s table of the level-3 node `u` must live: `i` for `X`, `j` for
`Y`, `k` for `Z`. -/
def lvlOf : Side → Pat (2 * 4) → ℕ
  | .X, u => (Ix u).val
  | .Y, u => (Jy u).val
  | .Z, u => (Kz u).val

/-- `lvlOf` is the paper's `coord`, at the unreduced width. -/
theorem lvlOf_eq_coord (S : Side) (u : Shape 4) : lvlOf S u = ADVXXZPaper.coord S u := by
  cases S <;> rfl


/-- The complement word `2⃗ - L` of `rmk:assumptions_on_complete_split_dist`. -/
def cbar (c : Chunk 4) : Chunk 4 := fun p => ⟨2 - (c p).val, by omega⟩

/-- The complement is an involution. -/
theorem cbar_cbar (c : Chunk 4) : cbar (cbar c) = c := by
  funext p
  have h := (c p).isLt
  ext
  show 2 - (2 - (c p).val) = (c p).val
  omega


/-! ## §2  The two law bundles -/

/-- **THE SUPPORT/BOUNDARY CLAUSE** at the slot `(r, S, u, c)`:

1. exact level support, in biconditional form;
2. the boundary point mass at level `0`;
3. the boundary point mass at level `2 * 4`. -/
def SuppOK (r : Fin 6) (S : Side) (u : Pat (2 * 4)) (c : Chunk 4) : Prop :=
  ((regionalSplit r S u).num c ≠ 0 ↔ chunkLvl c = lvlOf S u)
  ∧ (lvlOf S u = 0 →
      (regionalSplit r S u).num c = if c = c0 then (regionalSplit r S u).den else 0)
  ∧ (lvlOf S u = 2 * 4 →
      (regionalSplit r S u).num c = if c = c2 then (regionalSplit r S u).den else 0)

instance instDecSuppOK (r : Fin 6) (S : Side) (u : Pat (2 * 4)) (c : Chunk 4) :
    Decidable (SuppOK r S u c) := by
  unfold SuppOK; infer_instance

/-- **THE MIRROR/COMPLEMENT CLAUSE** at `(r, u, c)`: the three reflection laws of
`rmk:assumptions_on_complete_split_dist`, each guarded by its own typed index and cross-multiplied
over `ℕ`. -/
def MirrorOK (r : Fin 6) (u : Pat (2 * 4)) (c : Chunk 4) : Prop :=
  ((Jy u).val = 0 →
      (regionalSplit r .X u).num c * (regionalSplit r .Z u).den
        = (regionalSplit r .Z u).num (cbar c) * (regionalSplit r .X u).den)
  ∧ ((Ix u).val = 0 →
      (regionalSplit r .Z u).num c * (regionalSplit r .Y u).den
        = (regionalSplit r .Y u).num (cbar c) * (regionalSplit r .Z u).den)
  ∧ ((Kz u).val = 0 →
      (regionalSplit r .Y u).num c * (regionalSplit r .X u).den
        = (regionalSplit r .X u).num (cbar c) * (regionalSplit r .Y u).den)

instance instDecMirrorOK (r : Fin 6) (u : Pat (2 * 4)) (c : Chunk 4) :
    Decidable (MirrorOK r u c) := by
  unfold MirrorOK; infer_instance

end ADVXXZG1
end OmegaBound

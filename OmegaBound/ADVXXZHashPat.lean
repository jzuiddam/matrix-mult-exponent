import OmegaBound.CW90EightRandomCount

/-!
# ADVXXZ / DWZ hashing, level `ℓ`: the patterns

ADVXXZ (`global.tex:142-184`) and DWZ (`hashing.tex:15-51`) hash the level-`ℓ` partition of
`(CW_q^{⊗2^{ℓ-1}})^{⊗n}`, whose block triples are the level triples with `I + J + K = 2^ℓ`.
This file defines the level-`L` pattern type for an arbitrary natural number `L` (the intended
value is `L = 2^ℓ`): `Pat L` is the *subtype* of level triples summing to `L`, with the level
projections `Ix`, `Jy`, `Kz` and the side index `lev : Fin 3 → Pat L → Fin (L+1)`,
`![Ix, Jy, Kz]`.
-/

open Finset

namespace OmegaBound

namespace ADVXXZHash


/-! ## The level-`L` patterns -/

/-- **The level-`L` patterns**: triples of levels in `{0, …, L}` summing to `L`.  At
`L = 2^ℓ` these are ADVXXZ's level-`ℓ` block triples (`global.tex:150`). -/
abbrev Pat (L : ℕ) : Type :=
  {t : Fin (L + 1) × Fin (L + 1) × Fin (L + 1) //
    (t.1 : ℕ) + (t.2.1 : ℕ) + (t.2.2 : ℕ) = L}

variable {L : ℕ}

/-- The `x`-level of a pattern. -/
def Ix (t : Pat L) : Fin (L + 1) := t.1.1

/-- The `y`-level of a pattern. -/
def Jy (t : Pat L) : Fin (L + 1) := t.1.2.1

/-- The `z`-level of a pattern. -/
def Kz (t : Pat L) : Fin (L + 1) := t.1.2.2

/-- The pattern set is nonempty: `(0, 0, L)`. -/
instance : Inhabited (Pat L) :=
  ⟨⟨(⟨0, by omega⟩, ⟨0, by omega⟩, ⟨L, by omega⟩), by simp⟩⟩

/-! ## The side index

`lev` packages the three level maps as one function of a side `s : Fin 3`. -/


/-- The level map of a side: `0 ↦ x`, `1 ↦ y`, `2 ↦ z`. -/
def lev : Fin 3 → Pat L → Fin (L + 1) := ![Ix, Jy, Kz]

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

end ADVXXZHash

end OmegaBound

import OmegaBound.ADVXXZConGrid
import OmegaBound.ADVXXZBlkCount
import OmegaBound.ADVXXZHashRung
import OmegaBound.ADVXXZSplitIface
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-!
# The level triple splits into a grid of level-1 triples

`exists_grid_of_sum` splits a level triple `(I, J, K)` with `I + J + K = 2w` into `w` level-1
triples `pat : Fin w → Pat (2 * 1)`, each summing to `2`, whose `X`-, `Y`- and `Z`-levels add up
to `I`, `J` and `K`: pair up the `2w` coloured level units into `w` pairs.  The `w = 1` case of the
split is the identity.

## Main results

* `ADVXXZAbs.patOf3` — the level-1 triple with prescribed levels.
* `ADVXXZAbs.exists_grid_of_sum` — a level triple summing to `2w` splits into `w` level-1 triples.
-/

open Finset Tensor3

namespace OmegaBound

namespace ADVXXZAbs

open ADVXXZ (chunkLvl)
open ADVXXZHash (Pat Ix Jy Kz)
open ADVXXZCon (patX patY patZ)

/-! ## Level-1 triples -/

/-- **The level-1 pattern with prescribed levels.**  Any triple of naturals summing to `2` is a
`Pat 2`; the `Fin 3` bounds come from the sum. -/
def patOf3 (a b c : ℕ) (h : a + b + c = 2) : Pat (2 * 1) :=
  ⟨(⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩), by simpa using h⟩

@[simp] theorem Ix_patOf3 (a b c : ℕ) (h : a + b + c = 2) :
    (Ix (patOf3 a b c h)).val = a := rfl

@[simp] theorem Jy_patOf3 (a b c : ℕ) (h : a + b + c = 2) :
    (Jy (patOf3 a b c h)).val = b := rfl

@[simp] theorem Kz_patOf3 (a b c : ℕ) (h : a + b + c = 2) :
    (Kz (patOf3 a b c h)).val = c := rfl


/-! ## Cons on a coordinate pattern -/

theorem chunkLvl_patX_cons {w : ℕ} (v : Pat (2 * 1)) (pat : Fin w → Pat (2 * 1)) :
    chunkLvl (patX (Fin.cons v pat)) = (Ix v).val + chunkLvl (patX pat) := by
  simp only [chunkLvl, patX, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem chunkLvl_patY_cons {w : ℕ} (v : Pat (2 * 1)) (pat : Fin w → Pat (2 * 1)) :
    chunkLvl (patY (Fin.cons v pat)) = (Jy v).val + chunkLvl (patY pat) := by
  simp only [chunkLvl, patY, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem chunkLvl_patZ_cons {w : ℕ} (v : Pat (2 * 1)) (pat : Fin w → Pat (2 * 1)) :
    chunkLvl (patZ (Fin.cons v pat)) = (Kz v).val + chunkLvl (patZ pat) := by
  simp only [chunkLvl, patZ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-! ## The split -/

/-- **A level triple summing to `2w` splits into `w` level-1 triples.**  Pair up the `2w`
coloured units; the pairing is unconstrained, so the induction may take any admissible head. -/
theorem exists_grid_of_sum : ∀ (w I J K : ℕ), I + J + K = 2 * w →
    ∃ pat : Fin w → Pat (2 * 1), chunkLvl (patX pat) = I ∧ chunkLvl (patY pat) = J
      ∧ chunkLvl (patZ pat) = K := by
  intro w
  induction w with
  | zero =>
      intro I J K h
      exact ⟨Fin.elim0, by simp only [chunkLvl, Finset.univ_eq_empty, Finset.sum_empty]; omega,
        by simp only [chunkLvl, Finset.univ_eq_empty, Finset.sum_empty]; omega,
        by simp only [chunkLvl, Finset.univ_eq_empty, Finset.sum_empty]; omega⟩
  | succ w ih =>
      intro I J K h
      obtain ⟨a, b, c, hs, ha, hb, hc⟩ :
          ∃ a b c : ℕ, a + b + c = 2 ∧ a ≤ I ∧ b ≤ J ∧ c ≤ K := by
        rcases Nat.lt_or_ge I 1 with hI | hI
        · rcases Nat.lt_or_ge J 1 with hJ | hJ
          · exact ⟨0, 0, 2, by omega, by omega, by omega, by omega⟩
          · rcases Nat.lt_or_ge J 2 with hJ2 | hJ2
            · exact ⟨0, 1, 1, by omega, by omega, by omega, by omega⟩
            · exact ⟨0, 2, 0, by omega, by omega, by omega, by omega⟩
        · rcases Nat.lt_or_ge I 2 with hI2 | hI2
          · rcases Nat.lt_or_ge J 1 with hJ | hJ
            · exact ⟨1, 0, 1, by omega, by omega, by omega, by omega⟩
            · exact ⟨1, 1, 0, by omega, by omega, by omega, by omega⟩
          · exact ⟨2, 0, 0, by omega, by omega, by omega, by omega⟩
      obtain ⟨pat, h1, h2, h3⟩ := ih (I - a) (J - b) (K - c) (by omega)
      refine ⟨Fin.cons (patOf3 a b c hs) pat, ?_, ?_, ?_⟩
      · rw [chunkLvl_patX_cons, Ix_patOf3, h1]; omega
      · rw [chunkLvl_patY_cons, Jy_patOf3, h2]; omega
      · rw [chunkLvl_patZ_cons, Kz_patOf3, h3]; omega

end ADVXXZAbs

end OmegaBound

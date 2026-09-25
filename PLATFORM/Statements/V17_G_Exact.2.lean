/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_G_Exact.2
paper_clause: repair and exact global output (P/global.tex:79–93,460–462).
sha256: b7766a9fd572930a64523d264aade5fcf10568369cfa962b19bda4a1c179439e
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralAmend27GExactNear

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_G_Exact_2 : Prop :=
  ∀ (q w b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b),
  ∃ (V : ℕ → ℕ) (ell : ℕ → ℝ),
    (∀ m, 0 ≤ ell m) ∧ Sublinear (fun m => b*m) ell ∧
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      Real.exp (gRate g * (b*m:ℝ) - ell m) ≤ (V m:ℝ) ∧
      ∀ (F : Type u) [Field F],
        Degenerates F ((topZ q w (b*m)).over F)
          ((copiesZ (V m) (globalOutputZ q g (b*m) 0)).over F)

end OmegaBound.ADVXXZGeneral
end

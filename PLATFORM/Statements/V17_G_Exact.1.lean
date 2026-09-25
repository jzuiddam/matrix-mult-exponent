/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_G_Exact.1
paper_clause: repair and exact global output (P/global.tex:79–93,460–462).
sha256: 4f8bfd74f1bd4690eb07b165b6ac486dc6afddcffb6c6b80273f830fb2b5a971
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

def S_V17_G_Exact_1 : Prop :=
  ∀ {w b : ℕ} (q : ℕ) (hq : 0 < q) (hw : 0 < w)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b),
  ∃ ell : ℕ → ℝ, (∀ m, 0 ≤ ell m) ∧ Sublinear (fun m => b*m) ell ∧
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ ξ : ExactGrid g (b*m),
      ∃ V N : ℕ,
        Real.exp (gridRate g (b*m) ξ*(b*m:ℝ)-ell m) ≤ (V:ℝ) ∧
        PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
          (copiesZ V (exactGridTensor q g (b*m) ξ)).tensor

end OmegaBound.ADVXXZGeneral
end

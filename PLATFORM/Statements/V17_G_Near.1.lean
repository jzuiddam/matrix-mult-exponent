/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_G_Near.1
paper_clause: uniform nearby-output loss in the positive global theorem (P/global.tex:116–125).
sha256: 12cd5eaa3dafd2dd2f7a967aa52fc9186b2ee2c7824fdd567c72566910f5bde5
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralAmend27GExactNear
import OmegaBound.ADVXXZGeneralGridFull

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_G_Near_1 : Prop :=
  ∀ {w b : ℕ} (q : ℕ) (hq : 0 < q) (hw : 0 < w)
    (g : GlobalSpec w) (hg : GlobalAdmissible g) (hb : GlobalIntegral g b),
  ∃ (V : (ε : ℚ) → (m : ℕ) → FullGrid g (b*m) ε → ℕ)
    (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ Loss (fun m => b*m) ell ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m →
      ∀ ξ : FullGrid g (b*m) ε,
        Real.exp ((gRate g-delta ε)*(b*m:ℝ)-ell ε m) ≤ (V ε m ξ:ℝ) ∧
        ∃ N : ℕ, PolyDegeneratesAt ℤ N (topZ q w (b*m)).tensor
          (copiesZ (V ε m ξ) (exactGridTensor q g (b*m) ξ.val)).tensor

end OmegaBound.ADVXXZGeneral
end

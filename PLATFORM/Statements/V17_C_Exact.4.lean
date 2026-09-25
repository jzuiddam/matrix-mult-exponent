/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_C_Exact.4
paper_clause: positive-parent-to-positive-child 3eps-to-eps construction in the finite regional count convention (P/constituent.tex:138–149); the paper's 2^(sum_r E_r - o(n)) count claim (P/constituent.tex:117–119) is discharged in the recursion (statement V17_N_Iterate.1) by constituent_pooled_positive33.
sha256: 1954fdca8a6f004d5c8e6c21d4c92d847837853db607c027560d888c8044c81a
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralCExact33Defs

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_C_Exact_4 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (Q V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧ Loss (cLength p b) ell ∧
    RegionalCopyBound33 p d b delta ell V ∧
    (∀ ε, 0 < ε → Sublinear (cLength p b) (fun m => Real.log (Q ε m:ℝ))) ∧
    ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
      1 ≤ Q ε m ∧ Q ε m ≤ (cLength p b m+1)^ConstituentGridDimension p d ∧
      ∀ (F : Type u) [Field F],
        Degenerates F ((copiesZ (Q ε m) (constituentPlainInputZ q p (b*m) (3*ε))).over F)
          ((copiesZ (V ε m) (constituentOutputZ q d m ε)).over F)
end OmegaBound.ADVXXZGeneral
end

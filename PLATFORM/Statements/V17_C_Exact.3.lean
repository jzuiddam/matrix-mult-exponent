/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_C_Exact.3
paper_clause: positive-parent-to-exact-child construction in the finite regional count convention (P/constituent.tex:113–136); the paper's 2^(sum_r E_r - o(n)) count claim (P/constituent.tex:117–119) is discharged in the recursion (statement V17_N_Iterate.1) by constituent_pooled_positive33.
sha256: 3074a29abca3f39389737b615cf10b5f098b185e91311438388a9eabcbc1ff55
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

def S_V17_C_Exact_3 : Prop :=
  ∀ (q w s b : ℕ) (hq : 0 < q) (hw : 0 < w)
    (p : ConstituentInput w s) (d : ConstituentSpec p)
    (hd : ConstituentAdmissibleAt d b) (hb : StepIntegralAt p d b),
  ∃ (V : ℚ → ℕ → ℕ) (delta : ℚ → ℝ) (ell : ℚ → ℕ → ℝ),
    VanishesWithTolerance delta ∧
    Loss (fun m => constituentBaseTotal p * (b*m)) ell ∧
    RegionalCopyBound33 p d b delta ell V ∧
    ∀ ε : ℚ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ (F : Type u) [Field F],
        Degenerates F ((constituentInputZ q p (b*m) ε).over F)
          ((copiesZ (V ε m) (constituentOutputZ q d m 0)).over F)
end OmegaBound.ADVXXZGeneral
end

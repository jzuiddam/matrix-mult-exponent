/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_N_Iterate.1
paper_clause: compose the actual level-by-level producers and boundary matrices (P/numerical.tex:8,16–22; P/constituent.tex:28–36).
sha256: a084d1d5300bdd1e7142bb5245223c1eb878661a96eec88bd69cbc66ad52ba9f
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralAmend27N
import OmegaBound.ADVXXZGeneralCertScaleV22
import OmegaBound.ADVXXZGeneralStageNumerical

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_N_Iterate_1 : Prop :=
  ∀ (C : Certificate) (hC : AdmissibleAt C),
  ∃ f : NumericalFamily, IntegralNumericalProduction C f ∧
    (∀ ε, 0 < ε → (∀ m, 1 ≤ f.Q ε m) ∧
      Sublinear (outerN C) (fun m => Real.log (f.Q ε m:ℝ))) ∧
    LowerRate (outerN C) f.V (derivedRetainedRate C) ∧
    LowerRate (outerN C) f.a (derivedMatrixRateAt C .X) ∧
    LowerRate (outerN C) f.b (derivedMatrixRateAt C .Y) ∧
    LowerRate (outerN C) f.c (derivedMatrixRateAt C .Z)

end OmegaBound.ADVXXZGeneral
end

/-
Frozen statement: a copy of a statement frozen in the development repository.
id: V17_N_Closure.2
paper_clause: numerical feasible-parameter limit interpretation (P/numerical.tex:25–28,36–53).
sha256: 2b86a662246b1ec42a2f8d2cf646c19c1071320731cc6f3be65cff88ab751942
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.ADVXXZGeneralEndpointDefs
import OmegaBound.ADVXXZGeneralCertScaleV22
import OmegaBound.ADVXXZGeneralRatesFitV22

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def S_V17_N_Closure_2 : Prop :=
  ∀ (F : Type u) [Field F]
    (κ τ : ℝ), 0 < κ → ∀ (C : ℕ → Certificate) (t : ℕ → ℝ),
    (∀ n, AdmissibleAt (C n)) → (∀ n, (C n).kappa = κ) →
    (∀ n, CertificateNumericalFitAt (C n) (t n)) →
    Filter.Tendsto t Filter.atTop (nhds τ) → omegaRect F κ ≤ τ

end OmegaBound.ADVXXZGeneral
end

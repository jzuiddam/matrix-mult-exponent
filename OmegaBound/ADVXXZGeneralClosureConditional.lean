import OmegaBound.ADVXXZGeneralEndpointContinuation
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalAdmissible
import OmegaBound.ADVXXZT9TargetArithmetic
import PLATFORM.Statements.«V17_N_Iterate.1»
import PLATFORM.Statements.«V17_N_Closure.1»
import PLATFORM.Statements.«V17_N_Closure.2»
import PLATFORM.Statements.«V17_I_Apply.1»
import PLATFORM.Statements.«V17_I_Apply.2»
import PLATFORM.Statements.«V17_I_Apply.3»
import PLATFORM.Statements.«T8_F.1»
import PLATFORM.Statements.«T8.1»

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private theorem copies_matMul_over_eq_famDS_conditional (F : Type u) [Field F]
    (V a b c : ℕ) :
    (copiesZ V (matMulZ a b c)).over F =
      famDS Finset.univ (fun _ : Fin V => Tensor3.matMul (R := F) a b c) := by
  classical
  funext x y z
  obtain ⟨ix, x⟩ := x
  obtain ⟨iy, y⟩ := y
  obtain ⟨iz, z⟩ := z
  obtain ⟨i, j⟩ := x
  obtain ⟨j', k⟩ := y
  obtain ⟨k', i'⟩ := z
  simp [ITensor.over, copiesZ, mapTensor, famDS, matMulZ, Tensor3.matMul]

private theorem numerical_production_degenerates_conditional
    (F : Type u) [Field F] (C : Certificate) (f : NumericalFamily)
    (hprod : IntegralNumericalProduction C f) :
    ∀ ε, 0 < ε → ∃ M, ∀ m, M ≤ m →
      Degenerates F ((copiesZ (f.Q ε m) (topZ C.q C.width (outerN C m))).over F)
        (famDS Finset.univ (fun _ : Fin (f.V ε m) =>
          Tensor3.matMul (R := F) (f.a ε m) (f.b ε m) (f.c ε m))) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hprod ε hε
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨N, hN⟩ := hM m hm
  have hdeg := integral_degenerates F
    (copiesZ (f.Q ε m) (topZ C.q C.width (outerN C m)))
    (copiesZ (f.V ε m) (matMulZ (f.a ε m) (f.b ε m) (f.c ε m))) ⟨N, hN⟩
  rw [copies_matMul_over_eq_famDS_conditional] at hdeg
  exact hdeg

/-- The frozen statement `V17_N_Iterate.1` supplies exactly the numerical family consumed by
the frozen certificate bound `V17_N_Closure.1`. -/
theorem certificate_bound_of_iterate :
    S_V17_N_Iterate_1 → S_V17_N_Closure_1.{u} := by
  intro hiterate F _ C hC τ hfit
  rcases hiterate C hC with ⟨f, hprod, hQ, hV, ha, hb, hc⟩
  rcases hfit with ⟨hτ, hgrowth, hfit⟩
  exact numerical_limit F C hC f.Q f.V f.a f.b f.c
    (derivedRetainedRate C) (derivedMatrixRateAt C .X)
    (derivedMatrixRateAt C .Y) (derivedMatrixRateAt C .Z) τ hτ hQ
    (numerical_production_degenerates_conditional F C f hprod)
    hV ha hb hc hgrowth hfit

/-- Pointwise frozen certificate bounds are closed under the supplied convergent sequence. -/
theorem omegaRect_le_of_certificates_tendsto_of_bound :
    S_V17_N_Closure_1.{u} → S_V17_N_Closure_2.{u} := by
  intro hbound F _ κ τ _hκ C t hC hκC hfit ht
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [] with n
  rw [← hκC n]
  exact hbound F (C n) (hC n) (t n) (hfit n)

/-- The released fit and the frozen general certificate bound imply the all-fields
non-strict released endpoint. -/
theorem omegaMM_le_tauCert_allFields_of :
    S_V17_I_Apply_1 → S_V17_N_Closure_1.{u} → S_V17_I_Apply_2.{u} := by
  intro hfit hbound F _
  have hrect := hbound F releasedOrdinaryCertificatePhysical
    released_ordinary_physical_admissible CertArith.tauCert hfit
  have hkappa : releasedOrdinaryCertificatePhysical.kappa = 1 := rfl
  rw [hkappa, omegaRect_one] at hrect
  exact hrect

/-- The non-strict released endpoint and the cleared-integer comparison imply the
all-fields strict capstone proposition. -/
theorem omegaMM_lt_target_allFields_of :
    S_V17_I_Apply_2.{u} → S_T8_F_1.{u} := by
  intro h F _
  exact lt_of_le_of_lt (h F) ADVXXZT9TargetArithmetic.tauCert_lt_target_kernel

end OmegaBound.ADVXXZGeneral

namespace OmegaBound.ADVXXZFinal

/-- The all-fields non-strict endpoint implies the frozen rational endpoint `V17_I_Apply.3`. -/
theorem omegaMM_le_tauCert114_of :
    ADVXXZGeneral.S_V17_I_Apply_2.{0} → S_V17_I_Apply_3 := by
  intro h
  exact h ℚ

/-- The all-fields strict capstone proposition implies the frozen rational capstone. -/
theorem omegaMM_lt_target114_of :
    ADVXXZGeneral.S_T8_F_1.{0} → _root_.S_T8_1 := by
  intro h
  exact h ℚ

end OmegaBound.ADVXXZFinal
end

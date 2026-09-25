import OmegaBound.AuditIrowsMatrixX
import OmegaBound.AuditIrowsMatrixY
import OmegaBound.AuditIrowsMatrixZ
import PLATFORM.Statements.«V17_I_Rows.8»
import PLATFORM.Statements.«V17_I_Apply.1»
open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
private def auditStageEquiv : Fin 2 ≃ Stage 3 where
  toFun j := if j = 0 then ordinaryLevel2 else ordinaryLevel3
  invFun l := if l.val = 2 then 0 else 1
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by
    rintro ⟨l, hl⟩
    have : l = 2 ∨ l = 3 := by omega
    rcases this with rfl | rfl <;> rfl
private theorem audit_stage_sum {M : Type*} [AddCommMonoid M] (f : Stage 3 → M) :
    ∑ l : Stage 3, f l = f ordinaryLevel2 + f ordinaryLevel3 := by
  rw [← Equiv.sum_comp auditStageEquiv f, Fin.sum_univ_two]
  rfl

theorem audit_derived_matrix_split (W : Side) :
    derivedMatrixRateAt releasedOrdinaryCertificatePhysical W =
      ordinaryInventoryRate 5 W (G releasedOrdinaryCertificatePhysical) /
        (releasedOrdinaryCertificatePhysical.D : ℝ)^4 +
      (ordinaryInventoryRate 5 W (QAt releasedOrdinaryCertificatePhysical ordinaryLevel3) +
       ordinaryInventoryRate 5 W (QAt releasedOrdinaryCertificatePhysical ordinaryLevel2)) /
        (releasedOrdinaryCertificatePhysical.D : ℝ)^4 := by
  change (ordinaryInventoryRate 5 W (G releasedOrdinaryCertificatePhysical) +
    ∑ l : Stage 3, ordinaryInventoryRate 5 W (QAt releasedOrdinaryCertificatePhysical l)) /
      (releasedOrdinaryCertificatePhysical.D : ℝ)^4 = _
  rw [audit_stage_sum]
  ring

theorem audit_global_matrix (W : Side) :
    ordinaryInventoryRate 5 W (G releasedOrdinaryCertificatePhysical) /
      (releasedOrdinaryCertificatePhysical.D : ℝ)^4 =
      OmegaBound.ADVXXZReleasedTree.releasedLevel3Matrix
        (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
  cases W
  · exact audit_physical_global_matrix_x32
  · exact audit_physical_global_matrix_y32
  · exact audit_physical_global_matrix_z32

theorem audit_frozen_rows8 : P2M.V17_I_Rows.S_V17_I_Rows_8 := by
  refine ⟨released_ordinary_derived_retained_rate32, ?_⟩
  intro W
  rw [audit_derived_matrix_split, audit_global_matrix,
    released_ordinary_matrix_census32]
  have hm : OmegaBound.ADVXXZLevel2Closure.matrixRow 5
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms
      (OmegaBound.ADVXXZT6Round82.sideIndex W) =
      OmegaBound.ADVXXZReleasedTree.releasedLevel2Matrix
      (OmegaBound.ADVXXZT6Round82.sideIndex W) := by
    cases W
    · exact OmegaBound.ADVXXZReleasedTree.released_matrixRow_0
    · exact OmegaBound.ADVXXZReleasedTree.released_matrixRow_1
    · exact OmegaBound.ADVXXZReleasedTree.released_matrixRow_2
  rw [hm, add_comm]

example : P2M.V17_I_Rows.S_V17_I_Rows_8 := audit_frozen_rows8

theorem audit_matrix_lower (W : Side) :
    CertArith.Mcert ≤ derivedMatrixRateAt releasedOrdinaryCertificatePhysical W := by
  rw [audit_frozen_rows8.2 W]
  cases W
  · exact OmegaBound.ADVXXZReleasedTree.released_combined_matrix_0 ▸
      OmegaBound.ADVXXZCert.Mcert_le_Mtotal0
  · exact OmegaBound.ADVXXZReleasedTree.released_combined_matrix_1 ▸
      OmegaBound.ADVXXZCert.Mcert_le_Mtotal1
  · exact OmegaBound.ADVXXZReleasedTree.released_combined_matrix_2 ▸
      OmegaBound.ADVXXZCert.Mcert_le_Mtotal2

private theorem audit_scalar_fit (E z : ℝ)
    (hE : CertArith.Ecert ≤ E) (hM : CertArith.Mcert ≤ z) :
    0 ≤ CertArith.tauCert ∧ 0 < z ∧
      (4 : ℝ) * Real.log ((5 : ℝ) + 2) ≤ E + CertArith.tauCert * z := by
  have hpos : 0 < CertArith.Mcert := by norm_num [CertArith.Mcert]
  refine ⟨CertArith.tauCert_nonneg, lt_of_lt_of_le hpos hM, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hM CertArith.tauCert_nonneg
  calc
    _ ≤ CertArith.Ecert + CertArith.Mcert * CertArith.tauCert := CertArith.feasibility
    _ ≤ E + CertArith.tauCert * z := by
      simpa only [mul_comm] using add_le_add hE hm

theorem audit_fit_of_retained_lower
    (hE : CertArith.Ecert ≤ derivedRetainedRate releasedOrdinaryCertificatePhysical) :
    S_V17_I_Apply_1 := by
  change 0 ≤ CertArith.tauCert ∧
    0 < min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .X)
      (min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Y / 1)
        (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Z)) ∧
    (4 : ℝ) * Real.log ((5 : ℝ) + 2) ≤
      derivedRetainedRate releasedOrdinaryCertificatePhysical + CertArith.tauCert *
        min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .X)
          (min (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Y / 1)
            (derivedMatrixRateAt releasedOrdinaryCertificatePhysical .Z))
  simp only [div_one]
  apply audit_scalar_fit _ _ hE
  exact le_min (audit_matrix_lower .X)
    (le_min (audit_matrix_lower .Y) (audit_matrix_lower .Z))
end OmegaBound.ADVXXZGeneral
#print axioms OmegaBound.ADVXXZGeneral.audit_frozen_rows8
#print axioms OmegaBound.ADVXXZGeneral.audit_matrix_lower
#print axioms OmegaBound.ADVXXZGeneral.audit_fit_of_retained_lower

import OmegaBound.ADVXXZGeneralReleasedRetainedLegs
import OmegaBound.ADVXXZGeneralReleasedRetainedLevel2Leg

/-!
# Glue for the three released retained-rate legs

The only stage bookkeeping here is the two-element `Stage 3` expansion already used by
`released_ordinary_derived_retained_rate32`.  Once that exact identity is exposed, the thirteen
released rows and the three leg hypotheses close the residual by linear arithmetic.
-/

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

private def retainedGlueStageEquiv : Fin 2 ≃ Stage 3 where
  toFun j := if j = 0 then ordinaryLevel2 else ordinaryLevel3
  invFun l := if l.val = 2 then 0 else 1
  left_inv := by
    intro j
    fin_cases j <;> rfl
  right_inv := by
    intro l
    rcases l with ⟨l, hl⟩
    have : l = 2 ∨ l = 3 := by omega
    rcases this with rfl | rfl <;> rfl

private theorem retained_glue_stage_sum {M : Type*} [AddCommMonoid M]
    (f : Stage 3 → M) :
    ∑ l : Stage 3, f l = f ordinaryLevel2 + f ordinaryLevel3 := by
  rw [← Equiv.sum_comp retainedGlueStageEquiv f, Fin.sum_univ_two]
  rfl

/-- The legacy physical certificate has exactly its global term and the released level-3 term. -/
theorem physical_legacy_derived_retained_rate32 :
    derivedRetainedRate physicalLegacyCertificate =
      gRate physicalGlobalSpec +
        cRate releasedConstituentSpec * (constituentBaseTotal releasedParent : ℝ) /
          (releasedCertificate.D : ℝ) ^ 2 := by
  have hlegacy2 : releasedStage ordinaryLevel2 = none := by
    simp [releasedStage, ordinaryLevel2]
  have hlegacy3 : releasedStage ordinaryLevel3 = some releasedStep3 := by
    simp [releasedStage, ordinaryLevel3]
  unfold derivedRetainedRate
  simp only [physicalLegacyCertificate, releasedCertificate]
  rw [retained_glue_stage_sum, hlegacy2, hlegacy3]
  simp only [zero_add, releasedStep3]

/-- The level-2, level-3, and global rows imply the combined retained-rate residual. -/
theorem residual_of_legs :
    S_released_level2_retained_leg →
      S_released_level3_retained_leg →
        S_released_global_retained_leg →
          S_released_retained_residual := by
  intro h2 h3 hg
  have hrows : OmegaBound.CertArith.Ecert ≤
      (OmegaBound.ADVXXZCert.R1 + OmegaBound.ADVXXZCert.R2 +
        OmegaBound.ADVXXZCert.R3 + OmegaBound.ADVXXZCert.R4 +
        OmegaBound.ADVXXZCert.R5 + OmegaBound.ADVXXZCert.R6 +
        OmegaBound.ADVXXZCert.R7 + OmegaBound.ADVXXZCert.R8 +
        OmegaBound.ADVXXZCert.R9 + OmegaBound.ADVXXZCert.R10 +
        OmegaBound.ADVXXZCert.R11 + OmegaBound.ADVXXZCert.R12 +
        OmegaBound.ADVXXZCert.R13 : ℝ) := by
    norm_num [OmegaBound.CertArith.Ecert, OmegaBound.ADVXXZCert.R1,
      OmegaBound.ADVXXZCert.R2, OmegaBound.ADVXXZCert.R3,
      OmegaBound.ADVXXZCert.R4, OmegaBound.ADVXXZCert.R5,
      OmegaBound.ADVXXZCert.R6, OmegaBound.ADVXXZCert.R7,
      OmegaBound.ADVXXZCert.R8, OmegaBound.ADVXXZCert.R9,
      OmegaBound.ADVXXZCert.R10, OmegaBound.ADVXXZCert.R11,
      OmegaBound.ADVXXZCert.R12, OmegaBound.ADVXXZCert.R13]
  unfold S_released_level2_retained_leg at h2
  unfold S_released_level3_retained_leg at h3
  unfold S_released_global_retained_leg at hg
  unfold S_released_retained_residual
  rw [released_ordinary_derived_retained_rate32,
    physical_legacy_derived_retained_rate32]
  linarith

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.physical_legacy_derived_retained_rate32
#print axioms OmegaBound.ADVXXZGeneral.residual_of_legs

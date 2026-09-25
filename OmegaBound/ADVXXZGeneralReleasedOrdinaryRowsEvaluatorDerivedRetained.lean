import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorMatrixAssemble
import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsScale

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
set_option maxRecDepth 4000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

private def ordinaryStageEquiv32 : Fin 2 ≃ Stage 3 where
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

private theorem ordinary_stage_sum32 {M : Type*} [AddCommMonoid M]
    (f : Stage 3 → M) :
    ∑ l : Stage 3, f l = f ordinaryLevel2 + f ordinaryLevel3 := by
  rw [← Equiv.sum_comp ordinaryStageEquiv32 f, Fin.sum_univ_two]
  rfl

/-- The retained-rate stage list consists exactly of the unchanged/scaled level-three
term and the released ordinary level-two census. -/
theorem released_ordinary_derived_retained_rate32 :
    derivedRetainedRate releasedOrdinaryCertificatePhysical =
      derivedRetainedRate physicalLegacyCertificate +
        OmegaBound.ADVXXZLevel2Closure.symmetricRate
          OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms := by
  have hcov := released_ordinary_scale_covariance.2.2.1
  have hlevel2 := released_ordinary_symmetric_rate32
  have hcov' :
      cRate releasedOrdinaryStep3.data *
          (constituentBaseTotal releasedOrdinaryStep3.input : ℝ) /
          (((ordinaryD : ℝ) ^ 2) ^ 2) =
        cRate releasedConstituentSpec *
          (constituentBaseTotal releasedParent : ℝ) / (ordinaryD : ℝ) ^ 2 := by
    simpa only [releasedOrdinaryCertificatePhysical, Nat.cast_pow] using hcov
  have hlevel2' :
      cRate releasedOrdinaryData2 *
          (constituentBaseTotal releasedOrdinaryParent : ℝ) /
          (((ordinaryD : ℝ) ^ 2) ^ 2) =
        OmegaBound.ADVXXZLevel2Closure.symmetricRate
          OmegaBound.ADVXXZReleasedTree.releasedLevel2Terms := by
    simpa only [releasedOrdinaryCertificatePhysical, Nat.cast_pow] using hlevel2
  have hord2 : releasedOrdinaryStage ordinaryLevel2 = some releasedOrdinaryStep2 := by
    simpa only [releasedOrdinaryCertificatePhysical] using ordinary_stage2_eq32
  have hord3 : releasedOrdinaryStage ordinaryLevel3 = some releasedOrdinaryStep3 := by
    simpa only [releasedOrdinaryCertificatePhysical] using ordinary_stage3_eq32
  have hlegacy2 : releasedStage ordinaryLevel2 = none := by
    simp [releasedStage, ordinaryLevel2]
  have hlegacy3 : releasedStage ordinaryLevel3 = some releasedStep3 := by
    simp [releasedStage, ordinaryLevel3]
  unfold derivedRetainedRate
  simp only [releasedOrdinaryCertificatePhysical, physicalLegacyCertificate,
    releasedCertificate]
  rw [ordinary_stage_sum32, ordinary_stage_sum32]
  rw [hord2, hord3, hlegacy2, hlegacy3]
  simp only [zero_add]
  simp only [Nat.cast_pow, releasedOrdinaryStep2, releasedStep3]
  rw [hcov', hlevel2']
  ring

end OmegaBound.ADVXXZGeneral
end

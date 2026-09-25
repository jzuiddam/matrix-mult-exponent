import OmegaBound.ADVXXZGeneralReleasedOrdinaryRowsEvaluatorPhysicalGlobalCore

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 100000
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

private theorem chunk4_reindex_physical_cell_r4_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR4X0_32 : ℝ :=
  ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x0_32 :
    physicalGlobalCellMatrixRate32 4 .X 9 =
      releasedPhysicalGlobalCellR4X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 9 =
      1924421349657147211776 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow43Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X1_32 : ℝ :=
  ((325001638449796158612105925671695 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((186233649016345 : ℝ) / 1125899906842624)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((349921216342677 : ℝ) / 2251799813685248)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((993404071538603 : ℝ) / 144115188075855872)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((1489869192172789 : ℝ) / 9007199254740992)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((2799373244681477 : ℝ) / 18014398509481984)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((3973615809466295 : ℝ) / 576460752303423488)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((5959476768619639 : ℝ) / 36028797018963968)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((7947231614559709 : ℝ) / 1152921504606846976)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((7947231979750881 : ℝ) / 1152921504606846976)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((47675814151886775 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x1_32 :
    physicalGlobalCellMatrixRate32 4 .X 17 =
      releasedPhysicalGlobalCellR4X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 17 =
      58361940074053521899520 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow41Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X2_32 : ℝ :=
  ((180306893456290978825752435665167 : ℝ) / 83076749736557242056487941267521536) * Real.log (5 : ℝ)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((88696978015535 : ℝ) / 9007199254740992)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((88696979907049 : ℝ) / 9007199254740992)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((246753953622589 : ℝ) / 1125899906842624)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((709575840149861 : ℝ) / 72057594037927936)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((1605989005563609 : ℝ) / 144115188075855872)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303295660729 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303296486859 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303296487377 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303360571389 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((3211973874288313 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((3211978011353715 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((5676606719421519 : ℝ) / 576460752303423488)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((6423947746156861 : ℝ) / 576460752303423488)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((7896126335003501 : ℝ) / 36028797018963968)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((7896126352538313 : ℝ) / 36028797018963968)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((31584506065553763 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x2_32 :
    physicalGlobalCellMatrixRate32 4 .X 24 =
      releasedPhysicalGlobalCellR4X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 24 =
      548911910520479689998336 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow38Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X3_32 : ℝ :=
  ((13066131415180115649535184252274503 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396111154951 : ℝ) / 18014398509481984)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396111199365 : ℝ) / 18014398509481984)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396144612799 : ℝ) / 18014398509481984)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146792222062561 : ℝ) / 36028797018963968)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2090951984403807 : ℝ) / 1152921504606846976)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2100908043039967 : ℝ) / 1152921504606846976)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578629327 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578635707 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578689571 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4181903968753871 : ℝ) / 2305843009213693952)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4201855127055765 : ℝ) / 2305843009213693952)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4459569132590387 : ℝ) / 144115188075855872)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587168890273223 : ℝ) / 144115188075855872)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8363807937508277 : ℝ) / 4611686018427387904)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8363807942468157 : ℝ) / 4611686018427387904)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138252394519 : ℝ) / 288230376151711744)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138343133641 : ℝ) / 288230376151711744)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138348746987 : ℝ) / 288230376151711744)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((1408141661468647631 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x3_32 :
    physicalGlobalCellMatrixRate32 4 .X 30 =
      releasedPhysicalGlobalCellR4X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 30 =
      1426220798117545336897536 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow34Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X4_32 : ℝ :=
  ((356245157495573641651135321122009 : ℝ) / 166153499473114484112975882535043072) * Real.log (5 : ℝ)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((400571134969093 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((801142272836135 : ℝ) / 72057594037927936)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((1725541704399823 : ℝ) / 144115188075855872)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157672859 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157676557 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157722243 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138182726399 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138182826883 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138184671817 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902166816798567 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902182673718795 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902182675579055 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774670947470387 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774670950655141 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774671174448217 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((124394738793056533 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x4_32 :
    physicalGlobalCellMatrixRate32 4 .X 35 =
      releasedPhysicalGlobalCellR4X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 35 =
      547626157707060465106944 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow29Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X5_32 : ℝ :=
  ((106702892314306548380036199947121 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((282197496050883 : ℝ) / 36028797018963968)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((564394992134849 : ℝ) / 72057594037927936)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((689389422439901 : ℝ) / 4503599627370496)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((2757557633315345 : ℝ) / 18014398509481984)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((3209886395992819 : ℝ) / 18014398509481984)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((4515159812602407 : ℝ) / 576460752303423488)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((4515159887832687 : ℝ) / 576460752303423488)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((5515115380868365 : ℝ) / 36028797018963968)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((5515115386159221 : ℝ) / 36028797018963968)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((51358182723242761 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x5_32 :
    physicalGlobalCellMatrixRate32 4 .X 39 =
      releasedPhysicalGlobalCellR4X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 39 =
      57706282224384844234752 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow23Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4X6_32 : ℝ :=
  ((303633432809611 : ℝ) / 110680464442257309696) * Real.log (5 : ℝ)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_x6_32 :
    physicalGlobalCellMatrixRate32 4 .X 42 =
      releasedPhysicalGlobalCellR4X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 42 =
      1910296382650623983616 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow16Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion4MatrixX32 : ℝ :=
  ((22324529054970467418179654064482365 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((88696978015535 : ℝ) / 9007199254740992)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((88696979907049 : ℝ) / 9007199254740992)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((186233649016345 : ℝ) / 1125899906842624)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((246753953622589 : ℝ) / 1125899906842624)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((282197496050883 : ℝ) / 36028797018963968)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((349921216342677 : ℝ) / 2251799813685248)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((400571134969093 : ℝ) / 36028797018963968)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((564394992134849 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396111154951 : ℝ) / 18014398509481984)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396111199365 : ℝ) / 18014398509481984)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((573396144612799 : ℝ) / 18014398509481984)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((689389422439901 : ℝ) / 4503599627370496)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((709575840149861 : ℝ) / 72057594037927936)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((801142272836135 : ℝ) / 72057594037927936)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((993404071538603 : ℝ) / 144115188075855872)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146792222062561 : ℝ) / 36028797018963968)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((1489869192172789 : ℝ) / 9007199254740992)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((1605989005563609 : ℝ) / 144115188075855872)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((1725541704399823 : ℝ) / 144115188075855872)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2090951984403807 : ℝ) / 1152921504606846976)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2100908043039967 : ℝ) / 1152921504606846976)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4894056573631661 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578629327 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578635707 : ℝ) / 72057594037927936)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293584578689571 : ℝ) / 72057594037927936)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((2757557633315345 : ℝ) / 18014398509481984)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((2799373244681477 : ℝ) / 18014398509481984)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303295660729 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303296486859 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303296487377 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((2838303360571389 : ℝ) / 288230376151711744)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((3209886395992819 : ℝ) / 18014398509481984)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((3211973874288313 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((3211978011353715 : ℝ) / 288230376151711744)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((3973615809466295 : ℝ) / 576460752303423488)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4181903968753871 : ℝ) / 2305843009213693952)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4201855127055765 : ℝ) / 2305843009213693952)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4459569132590387 : ℝ) / 144115188075855872)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((303633432809611 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((4515159812602407 : ℝ) / 576460752303423488)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((4515159887832687 : ℝ) / 576460752303423488)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587168890273223 : ℝ) / 144115188075855872)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((5515115380868365 : ℝ) / 36028797018963968)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((5515115386159221 : ℝ) / 36028797018963968)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((5676606719421519 : ℝ) / 576460752303423488)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((5959476768619639 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157672859 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157676557 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138157722243 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138182726399 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138182826883 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6409138184671817 : ℝ) / 576460752303423488)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((6423947746156861 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902166816798567 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902182673718795 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((6902182675579055 : ℝ) / 576460752303423488)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774670947470387 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774670950655141 : ℝ) / 36028797018963968)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((7774671174448217 : ℝ) / 36028797018963968)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((7896126335003501 : ℝ) / 36028797018963968)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((7896126352538313 : ℝ) / 36028797018963968)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((7947231614559709 : ℝ) / 1152921504606846976)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((7947231979750881 : ℝ) / 1152921504606846976)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8363807937508277 : ℝ) / 4611686018427387904)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8363807942468157 : ℝ) / 4611686018427387904)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138252394519 : ℝ) / 288230376151711744)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138343133641 : ℝ) / 288230376151711744)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((8919138348746987 : ℝ) / 288230376151711744)
      + ((908824984432061 : ℝ) / 1152921504606846976) * Real.negMulLog ((31584506065553763 : ℝ) / 144115188075855872)
      + ((1159547568838865 : ℝ) / 13835058055282163712) * Real.negMulLog ((47675814151886775 : ℝ) / 288230376151711744)
      + ((382173605921433 : ℝ) / 4611686018427387904) * Real.negMulLog ((51358182723242761 : ℝ) / 288230376151711744)
      + ((1360044274993391 : ℝ) / 1729382256910270464) * Real.negMulLog ((124394738793056533 : ℝ) / 576460752303423488)
      + ((7084115336922533 : ℝ) / 3458764513820540928) * Real.negMulLog ((1408141661468647631 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region4_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 4 .X =
      releasedPhysicalGlobalRegion4MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r4_x0_32]
  rw [physical_global_cell_r4_x1_32]
  rw [physical_global_cell_r4_x2_32]
  rw [physical_global_cell_r4_x3_32]
  rw [physical_global_cell_r4_x4_32]
  rw [physical_global_cell_r4_x5_32]
  rw [physical_global_cell_r4_x6_32]
  unfold releasedPhysicalGlobalRegion4MatrixX32
  unfold releasedPhysicalGlobalCellR4X0_32
  unfold releasedPhysicalGlobalCellR4X1_32
  unfold releasedPhysicalGlobalCellR4X2_32
  unfold releasedPhysicalGlobalCellR4X3_32
  unfold releasedPhysicalGlobalCellR4X4_32
  unfold releasedPhysicalGlobalCellR4X5_32
  unfold releasedPhysicalGlobalCellR4X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

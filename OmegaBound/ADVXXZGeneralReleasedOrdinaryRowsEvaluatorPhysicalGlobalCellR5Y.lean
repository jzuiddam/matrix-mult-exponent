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

private theorem chunk4_reindex_physical_cell_r5_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR5Y0_32 : ℝ :=
  ((25649213250171 : ℝ) / 9223372036854775808) * Real.log (5 : ℝ)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y0_32 :
    physicalGlobalCellMatrixRate32 5 .Y 16 =
      releasedPhysicalGlobalCellR5Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 16 =
      1936450759176814067712 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow07Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y1_32 : ℝ :=
  ((1731516365672580678984348660597513 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((48562458147007 : ℝ) / 281474976710656)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((854226757153441 : ℝ) / 144115188075855872)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((1289234150339243 : ℝ) / 9007199254740992)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((1553998661791721 : ℝ) / 9007199254740992)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((2576702191119999 : ℝ) / 18014398509481984)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((3107997321204219 : ℝ) / 18014398509481984)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6833813978611213 : ℝ) / 1152921504606846976)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6837825129006943 : ℝ) / 1152921504606846976)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6837825401326773 : ℝ) / 1152921504606846976)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((198911828729020503 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y1_32 :
    physicalGlobalCellMatrixRate32 5 .Y 23 =
      releasedPhysicalGlobalCellR5Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 23 =
      58070201302109883727872 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow06Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y2_32 : ℝ :=
  ((4388964520357159133240737951504733 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((343810598583877 : ℝ) / 36028797018963968)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1001751017517611 : ℝ) / 4503599627370496)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1298749153665177 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1298749527726575 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1375281071561715 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2597499057393483 : ℝ) / 288230376151711744)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2750484828615337 : ℝ) / 288230376151711744)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2750562162108725 : ℝ) / 288230376151711744)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996614611699 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996614863435 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996615367109 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194998110924139 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194998116260701 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((8014008145310885 : ℝ) / 36028797018963968)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((8014010154584003 : ℝ) / 36028797018963968)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((128224162505432999 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y2_32 :
    physicalGlobalCellMatrixRate32 5 .Y 29 =
      releasedPhysicalGlobalCellR5Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 29 =
      551482668502317218660352 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow05Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y3_32 : ℝ :=
  ((13307993092891068002505262864629169 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((291438584888393 : ℝ) / 9007199254740992)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((573685597723267 : ℝ) / 18014398509481984)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((573685661997101 : ℝ) / 18014398509481984)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((878759087288323 : ℝ) / 576460752303423488)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1147371140610491 : ℝ) / 36028797018963968)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1147371324556991 : ℝ) / 36028797018963968)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2294742281229485 : ℝ) / 72057594037927936)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2331508666612115 : ℝ) / 72057594037927936)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2331508707354419 : ℝ) / 72057594037927936)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349258415 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349279685 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349285845 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3632819922043021 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3632866460779533 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589484562486415 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589485293118447 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589485297160005 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4663017353542943 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1398629991620342033 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y3_32 :
    physicalGlobalCellMatrixRate32 5 .Y 34 =
      releasedPhysicalGlobalCellR5Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 34 =
      1454871485050802650742784 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow04Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y4_32 : ℝ :=
  ((45035763893602291837424770890957 : ℝ) / 20769187434139310514121985316880384) * Real.log (5 : ℝ)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((121584058935173 : ℝ) / 562949953421312)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((806410744825843 : ℝ) / 72057594037927936)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225640967369091 : ℝ) / 288230376151711744)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355267114834255 : ℝ) / 288230376151711744)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355356661831173 : ℝ) / 288230376151711744)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281933168115 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281933773077 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281934757129 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285958359087 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285958824097 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285959382437 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6710534230082101 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6710713326001903 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781369774430919 : ℝ) / 36028797018963968)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781369798702163 : ℝ) / 36028797018963968)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781379756415831 : ℝ) / 36028797018963968)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y4_32 :
    physicalGlobalCellMatrixRate32 5 .Y 38 =
      releasedPhysicalGlobalCellR5Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 38 =
      553535760368032209174528 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow03Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y5_32 : ℝ :=
  ((423698795339089470270716268158583 : ℝ) / 2658455991569831745807614120560689152) * Real.log (5 : ℝ)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((578903281304981 : ℝ) / 72057594037927936)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2315613037197189 : ℝ) / 288230376151711744)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2315613128658047 : ℝ) / 288230376151711744)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2808904037095663 : ℝ) / 18014398509481984)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((3099815648620203 : ℝ) / 18014398509481984)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((4631226273446545 : ℝ) / 576460752303423488)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808040963193 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808063435875 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808065055419 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((99202030793647119 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y5_32 :
    physicalGlobalCellMatrixRate32 5 .Y 41 =
      releasedPhysicalGlobalCellR5Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 41 =
      57333093193188127014912 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow02Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Y6_32 : ℝ :=
  ((203810215274889 : ℝ) / 73786976294838206464) * Real.log (5 : ℝ)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_y6_32 :
    physicalGlobalCellMatrixRate32 5 .Y 43 =
      releasedPhysicalGlobalCellR5Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 43 =
      1923394502628738072576 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow01Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion5MatrixY32 : ℝ :=
  ((120927340274915680364731846609747077 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((48562458147007 : ℝ) / 281474976710656)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((121584058935173 : ℝ) / 562949953421312)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((291438584888393 : ℝ) / 9007199254740992)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((343810598583877 : ℝ) / 36028797018963968)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((573685597723267 : ℝ) / 18014398509481984)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((573685661997101 : ℝ) / 18014398509481984)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((578903281304981 : ℝ) / 72057594037927936)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((806410744825843 : ℝ) / 72057594037927936)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((854226757153441 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((878759087288323 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1001751017517611 : ℝ) / 4503599627370496)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1147371140610491 : ℝ) / 36028797018963968)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1147371324556991 : ℝ) / 36028797018963968)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((1289234150339243 : ℝ) / 9007199254740992)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1298749153665177 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1298749527726575 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((1375281071561715 : ℝ) / 144115188075855872)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((1553998661791721 : ℝ) / 9007199254740992)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((25649213250171 : ℝ) / 9223372036854775808) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2294742281229485 : ℝ) / 72057594037927936)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2315613037197189 : ℝ) / 288230376151711744)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2315613128658047 : ℝ) / 288230376151711744)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2331508666612115 : ℝ) / 72057594037927936)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((2331508707354419 : ℝ) / 72057594037927936)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((2576702191119999 : ℝ) / 18014398509481984)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2597499057393483 : ℝ) / 288230376151711744)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2750484828615337 : ℝ) / 288230376151711744)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((2750562162108725 : ℝ) / 288230376151711744)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((2808904037095663 : ℝ) / 18014398509481984)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((3099815648620203 : ℝ) / 18014398509481984)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((3107997321204219 : ℝ) / 18014398509481984)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225640967369091 : ℝ) / 288230376151711744)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355267114834255 : ℝ) / 288230376151711744)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355356661831173 : ℝ) / 288230376151711744)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349258415 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349279685 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3515036349285845 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3632819922043021 : ℝ) / 2305843009213693952)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((3632866460779533 : ℝ) / 2305843009213693952)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((203810215274889 : ℝ) / 73786976294838206464) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589484562486415 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589485293118447 : ℝ) / 144115188075855872)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4589485297160005 : ℝ) / 144115188075855872)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((4631226273446545 : ℝ) / 576460752303423488)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((4663017353542943 : ℝ) / 144115188075855872)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996614611699 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996614863435 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194996615367109 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194998110924139 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((5194998116260701 : ℝ) / 576460752303423488)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808040963193 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808063435875 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((5617808065055419 : ℝ) / 36028797018963968)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281933168115 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281933773077 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451281934757129 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285958359087 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285958824097 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451285959382437 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6710534230082101 : ℝ) / 576460752303423488)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((6710713326001903 : ℝ) / 576460752303423488)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6833813978611213 : ℝ) / 1152921504606846976)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6837825129006943 : ℝ) / 1152921504606846976)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((6837825401326773 : ℝ) / 1152921504606846976)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781369774430919 : ℝ) / 36028797018963968)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781369798702163 : ℝ) / 36028797018963968)
      + ((916480621311453 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781379756415831 : ℝ) / 36028797018963968)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((8014008145310885 : ℝ) / 36028797018963968)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((8014010154584003 : ℝ) / 36028797018963968)
      + ((759404145256521 : ℝ) / 9223372036854775808) * Real.negMulLog ((99202030793647119 : ℝ) / 576460752303423488)
      + ((5478488092644187 : ℝ) / 6917529027641081856) * Real.negMulLog ((128224162505432999 : ℝ) / 576460752303423488)
      + ((1538334986954527 : ℝ) / 18446744073709551616) * Real.negMulLog ((198911828729020503 : ℝ) / 1152921504606846976)
      + ((7226424838358177 : ℝ) / 3458764513820540928) * Real.negMulLog ((1398629991620342033 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region5_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 5 .Y =
      releasedPhysicalGlobalRegion5MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r5_y0_32]
  rw [physical_global_cell_r5_y1_32]
  rw [physical_global_cell_r5_y2_32]
  rw [physical_global_cell_r5_y3_32]
  rw [physical_global_cell_r5_y4_32]
  rw [physical_global_cell_r5_y5_32]
  rw [physical_global_cell_r5_y6_32]
  unfold releasedPhysicalGlobalRegion5MatrixY32
  unfold releasedPhysicalGlobalCellR5Y0_32
  unfold releasedPhysicalGlobalCellR5Y1_32
  unfold releasedPhysicalGlobalCellR5Y2_32
  unfold releasedPhysicalGlobalCellR5Y3_32
  unfold releasedPhysicalGlobalCellR5Y4_32
  unfold releasedPhysicalGlobalCellR5Y5_32
  unfold releasedPhysicalGlobalCellR5Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

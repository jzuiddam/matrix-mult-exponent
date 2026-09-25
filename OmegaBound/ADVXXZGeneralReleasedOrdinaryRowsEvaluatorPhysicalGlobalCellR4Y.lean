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

private theorem chunk4_reindex_physical_cell_r4_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR4Y0_32 : ℝ :=
  ((2448835704766715 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y0_32 :
    physicalGlobalCellMatrixRate32 4 .Y 16 =
      releasedPhysicalGlobalCellR4Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 16 =
      1925842760971097210880 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow01Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y1_32 : ℝ :=
  ((847148050895173901684399818393929 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315599043493281 : ℝ) / 288230376151711744)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809527410996917 : ℝ) / 18014398509481984)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631197710872561 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631197809486713 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631198043898841 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054783629739 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054787506331 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054803055213 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((6194091499024057 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((99210989528832027 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y1_32 :
    physicalGlobalCellMatrixRate32 4 .Y 23 =
      releasedPhysicalGlobalCellR4Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 23 =
      57316198240342983573504 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow02Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y2_32 : ℝ :=
  ((720499178982659617249718786727611 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((50400780664681 : ℝ) / 4503599627370496)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((403206233611151 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((486337885376099 : ℝ) / 2251799813685248)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((1677520493210843 : ℝ) / 144115188075855872)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225649961642583 : ℝ) / 288230376151711744)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741399133 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741568475 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741593639 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299925358711 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299925578515 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710081970948397 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710089926690081 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710089929609601 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((7781406177905921 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((7781406632994963 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((62251253105497663 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y2_32 :
    physicalGlobalCellMatrixRate32 4 .Y 29 =
      releasedPhysicalGlobalCellR4Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 29 =
      553478224322328570888192 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow03Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y3_32 : ℝ :=
  ((13307587161369814104080282251015253 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((1164773820657157 : ℝ) / 36028797018963968)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740942571103 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740947430835 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740947921265 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294741240711769 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294741241461151 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2329547566142385 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2329547672083955 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3519831876746911 : ℝ) / 2305843009213693952)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3519831879903887 : ℝ) / 2305843009213693952)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3634125602970483 : ℝ) / 2305843009213693952)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589481894863117 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589482481159751 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589482481430783 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4659095151571543 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7039663751063719 : ℝ) / 4611686018427387904)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7039663751064799 : ℝ) / 4611686018427387904)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7268332591820909 : ℝ) / 4611686018427387904)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2797719150548635979 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y3_32 :
    physicalGlobalCellMatrixRate32 4 .Y 34 =
      releasedPhysicalGlobalCellR4Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 34 =
      1454745033449318400393216 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow04Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y4_32 : ℝ :=
  ((2194911497875655685232605996696479 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((21491247095409 : ℝ) / 2251799813685248)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((81115220780569 : ℝ) / 9007199254740992)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((324460905953923 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((648921766404547 : ℝ) / 72057594037927936)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((648921811984759 : ℝ) / 72057594037927936)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1297843532870269 : ℝ) / 144115188075855872)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1297843623920623 : ℝ) / 144115188075855872)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1375423099917787 : ℝ) / 144115188075855872)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((2595687065714361 : ℝ) / 288230376151711744)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((4007209327092029 : ℝ) / 18014398509481984)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5191374495887519 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501692393844695 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501759257302341 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((8014418665840251 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((8014420542161901 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((128230728694387799 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y4_32 :
    physicalGlobalCellMatrixRate32 4 .Y 38 =
      releasedPhysicalGlobalCellR4Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 38 =
      551572451696062607917056 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow05Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y5_32 : ℝ :=
  ((649250621080761216174649298947535 : ℝ) / 3987683987354747618711421180841033728) * Real.log (5 : ℝ)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((644077002063521 : ℝ) / 4503599627370496)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((1709432956229347 : ℝ) / 288230376151711744)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((1709433005494005 : ℝ) / 288230376151711744)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((5152616049209645 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212110397841 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212111070495 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212112109043 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6837731826767123 : ℝ) / 1152921504606846976)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6837732102958935 : ℝ) / 1152921504606846976)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((99475394026390683 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y5_32 :
    physicalGlobalCellMatrixRate32 4 .Y 41 =
      releasedPhysicalGlobalCellR4Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 41 =
      58064513050872209473536 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow06Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Y6_32 : ℝ :=
  ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_y6_32 :
    physicalGlobalCellMatrixRate32 4 .Y 43 =
      releasedPhysicalGlobalCellR4Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 43 =
      1935651002092796903424 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 4 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow07Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResYRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion4MatrixY32 : ℝ :=
  ((60463380587361419372219582017813397 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((21491247095409 : ℝ) / 2251799813685248)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((50400780664681 : ℝ) / 4503599627370496)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((81115220780569 : ℝ) / 9007199254740992)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((324460905953923 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((403206233611151 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((486337885376099 : ℝ) / 2251799813685248)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((644077002063521 : ℝ) / 4503599627370496)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((648921766404547 : ℝ) / 72057594037927936)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((648921811984759 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((1164773820657157 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1297843532870269 : ℝ) / 144115188075855872)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1297843623920623 : ℝ) / 144115188075855872)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((1375423099917787 : ℝ) / 144115188075855872)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((1677520493210843 : ℝ) / 144115188075855872)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((1709432956229347 : ℝ) / 288230376151711744)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((1709433005494005 : ℝ) / 288230376151711744)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2448835704766715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740942571103 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740947430835 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294740947921265 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294741240711769 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294741241461151 : ℝ) / 72057594037927936)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315599043493281 : ℝ) / 288230376151711744)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2329547566142385 : ℝ) / 72057594037927936)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2329547672083955 : ℝ) / 72057594037927936)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((2595687065714361 : ℝ) / 288230376151711744)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809527410996917 : ℝ) / 18014398509481984)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225649961642583 : ℝ) / 288230376151711744)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3519831876746911 : ℝ) / 2305843009213693952)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3519831879903887 : ℝ) / 2305843009213693952)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((3634125602970483 : ℝ) / 2305843009213693952)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((4007209327092029 : ℝ) / 18014398509481984)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4922615056591789 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589481894863117 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589482481159751 : ℝ) / 144115188075855872)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589482481430783 : ℝ) / 144115188075855872)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631197710872561 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631197809486713 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631198043898841 : ℝ) / 576460752303423488)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((4659095151571543 : ℝ) / 144115188075855872)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((5152616049209645 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5191374495887519 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501692393844695 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501759257302341 : ℝ) / 576460752303423488)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054783629739 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054787506331 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619054803055213 : ℝ) / 36028797018963968)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((6194091499024057 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212110397841 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212111070495 : ℝ) / 36028797018963968)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6217212112109043 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741399133 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741568475 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299741593639 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299925358711 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451299925578515 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710081970948397 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710089926690081 : ℝ) / 576460752303423488)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710089929609601 : ℝ) / 576460752303423488)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6837731826767123 : ℝ) / 1152921504606846976)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((6837732102958935 : ℝ) / 1152921504606846976)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7039663751063719 : ℝ) / 4611686018427387904)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7039663751064799 : ℝ) / 4611686018427387904)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((7268332591820909 : ℝ) / 4611686018427387904)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((7781406177905921 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((7781406632994963 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((8014418665840251 : ℝ) / 36028797018963968)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((8014420542161901 : ℝ) / 36028797018963968)
      + ((1832770719535909 : ℝ) / 2305843009213693952) * Real.negMulLog ((62251253105497663 : ℝ) / 288230376151711744)
      + ((1518360727107339 : ℝ) / 18446744073709551616) * Real.negMulLog ((99210989528832027 : ℝ) / 576460752303423488)
      + ((1153638224817757 : ℝ) / 13835058055282163712) * Real.negMulLog ((99475394026390683 : ℝ) / 576460752303423488)
      + ((2739690004269593 : ℝ) / 3458764513820540928) * Real.negMulLog ((128230728694387799 : ℝ) / 576460752303423488)
      + ((3612898373229599 : ℝ) / 1729382256910270464) * Real.negMulLog ((2797719150548635979 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region4_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 4 .Y =
      releasedPhysicalGlobalRegion4MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r4_y0_32]
  rw [physical_global_cell_r4_y1_32]
  rw [physical_global_cell_r4_y2_32]
  rw [physical_global_cell_r4_y3_32]
  rw [physical_global_cell_r4_y4_32]
  rw [physical_global_cell_r4_y5_32]
  rw [physical_global_cell_r4_y6_32]
  unfold releasedPhysicalGlobalRegion4MatrixY32
  unfold releasedPhysicalGlobalCellR4Y0_32
  unfold releasedPhysicalGlobalCellR4Y1_32
  unfold releasedPhysicalGlobalCellR4Y2_32
  unfold releasedPhysicalGlobalCellR4Y3_32
  unfold releasedPhysicalGlobalCellR4Y4_32
  unfold releasedPhysicalGlobalCellR4Y5_32
  unfold releasedPhysicalGlobalCellR4Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

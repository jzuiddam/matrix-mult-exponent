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

private theorem chunk4_reindex_physical_cell_r3_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR3Z0_32 : ℝ :=
  ((1622939792801299 : ℝ) / 590295810358705651712) * Real.log (5 : ℝ)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z0_32 :
    physicalGlobalCellMatrixRate32 3 .Z 1 =
      releasedPhysicalGlobalCellR3Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 1 =
      1914497680698466762752 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow16Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z1_32 : ℝ :=
  ((2560933729641240882448506883062095 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((70586094053363 : ℝ) / 9007199254740992)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((1129377488744315 : ℝ) / 144115188075855872)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((1129444804640803 : ℝ) / 144115188075855872)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((4517779214719385 : ℝ) / 576460752303423488)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844091804293 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844095379737 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844100627745 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844105253179 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((6417675996752989 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((102693335658661311 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z1_32 :
    physicalGlobalCellMatrixRate32 3 .Z 2 =
      releasedPhysicalGlobalCellR3Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 2 =
      57708758614229762703360 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow23Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z2_32 : ℝ :=
  ((178155012305059936471347822604889 : ℝ) / 83076749736557242056487941267521536) * Real.log (5 : ℝ)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((400586942421687 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((400586942514225 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((431412929913887 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((801174026053797 : ℝ) / 72057594037927936)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((1602347770013519 : ℝ) / 144115188075855872)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((1943653417429433 : ℝ) / 9007199254740992)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((3204696104090599 : ℝ) / 288230376151711744)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((3887307792305721 : ℝ) / 18014398509481984)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409391078534321 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409392207925893 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409392208163713 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902533737781375 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902533813711089 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902606891809309 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((7774613665834341 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((62196925554309557 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z2_32 :
    physicalGlobalCellMatrixRate32 3 .Z 3 =
      releasedPhysicalGlobalCellR3Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 3 =
      547728388890908134735872 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow29Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z3_32 : ℝ :=
  ((816615342878469514229440480052639 : ℝ) / 124615124604835863084731911901282304) * Real.log (5 : ℝ)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((278772706508603 : ℝ) / 9007199254740992)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((1146914007009039 : ℝ) / 36028797018963968)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2090251735081825 : ℝ) / 1152921504606846976)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828013991279 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828015227801 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828016434745 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828094953425 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828214122723 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4180503470190611 : ℝ) / 2305843009213693952)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4587656184718849 : ℝ) / 144115188075855872)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4587656189264499 : ℝ) / 144115188075855872)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8361006940334559 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8361006940456641 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8403920653245797 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8403970387417341 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726585810355 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726585963219 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726612232719 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((704016906445344305 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z3_32 :
    physicalGlobalCellMatrixRate32 3 .Z 4 =
      releasedPhysicalGlobalCellR3Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 4 =
      1426229225672549899173888 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow34Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z4_32 : ℝ :=
  ((270405638823558383090363988364729 : ℝ) / 124615124604835863084731911901282304) * Real.log (5 : ℝ)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((709987506878011 : ℝ) / 72057594037927936)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((1605801160325929 : ℝ) / 144115188075855872)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355378171 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355449403 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355451833 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211577997103911 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211577997355371 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211602274045293 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3947881131204179 : ℝ) / 18014398509481984)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054292591 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054537559 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054737167 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900710985941 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((7895762279511955 : ℝ) / 36028797018963968)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((7895763605940099 : ℝ) / 36028797018963968)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((63166108848603935 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z4_32 :
    physicalGlobalCellMatrixRate32 3 .Z 5 =
      releasedPhysicalGlobalCellR3Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 5 =
      548816979832566787866624 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow38Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z5_32 : ℝ :=
  ((162481257730818207028573889112859 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((174979438874181 : ℝ) / 1125899906842624)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((1984847855416335 : ℝ) / 288230376151711744)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979711077541325 : ℝ) / 18014398509481984)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979711078018391 : ℝ) / 18014398509481984)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((3969695712926323 : ℝ) / 576460752303423488)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599342392696055 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959422155336671 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959422155594819 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((7939391773487575 : ℝ) / 1152921504606846976)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((7939392106776807 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z5_32 :
    physicalGlobalCellMatrixRate32 3 .Z 6 =
      releasedPhysicalGlobalCellR3Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 6 =
      58353282294650064863232 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow41Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Z6_32 : ℝ :=
  ((1630661950012839 : ℝ) / 590295810358705651712) * Real.log (5 : ℝ)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_z6_32 :
    physicalGlobalCellMatrixRate32 3 .Z 7 =
      releasedPhysicalGlobalCellR3Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 7 =
      1923607108008745500672 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 3 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow43Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResXRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion3MatrixZ32 : ℝ :=
  ((59530999797114903114630012054554773 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((70586094053363 : ℝ) / 9007199254740992)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((174979438874181 : ℝ) / 1125899906842624)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((278772706508603 : ℝ) / 9007199254740992)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((400586942421687 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((400586942514225 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((431412929913887 : ℝ) / 36028797018963968)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((709987506878011 : ℝ) / 72057594037927936)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((801174026053797 : ℝ) / 72057594037927936)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((1129377488744315 : ℝ) / 144115188075855872)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((1129444804640803 : ℝ) / 144115188075855872)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((1146914007009039 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((1602347770013519 : ℝ) / 144115188075855872)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((1605801160325929 : ℝ) / 144115188075855872)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((1943653417429433 : ℝ) / 9007199254740992)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((1984847855416335 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2090251735081825 : ℝ) / 1152921504606846976)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1622939792801299 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828013991279 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828015227801 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828016434745 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828094953425 : ℝ) / 72057594037927936)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((2293828214122723 : ℝ) / 72057594037927936)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355378171 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355449403 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((2839950355451833 : ℝ) / 288230376151711744)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979711077541325 : ℝ) / 18014398509481984)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979711078018391 : ℝ) / 18014398509481984)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((3204696104090599 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211577997103911 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211577997355371 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3211602274045293 : ℝ) / 288230376151711744)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((3887307792305721 : ℝ) / 18014398509481984)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((3947881131204179 : ℝ) / 18014398509481984)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((3969695712926323 : ℝ) / 576460752303423488)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4180503470190611 : ℝ) / 2305843009213693952)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1630661950012839 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((4517779214719385 : ℝ) / 576460752303423488)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4587656184718849 : ℝ) / 144115188075855872)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((4587656189264499 : ℝ) / 144115188075855872)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844091804293 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844095379737 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844100627745 : ℝ) / 36028797018963968)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((5515844105253179 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599342392696055 : ℝ) / 36028797018963968)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054292591 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054537559 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900054737167 : ℝ) / 576460752303423488)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((5679900710985941 : ℝ) / 576460752303423488)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959422155336671 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959422155594819 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409391078534321 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409392207925893 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6409392208163713 : ℝ) / 576460752303423488)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((6417675996752989 : ℝ) / 36028797018963968)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902533737781375 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902533813711089 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((6902606891809309 : ℝ) / 576460752303423488)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((7774613665834341 : ℝ) / 36028797018963968)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((7895762279511955 : ℝ) / 36028797018963968)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((7895763605940099 : ℝ) / 36028797018963968)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((7939391773487575 : ℝ) / 1152921504606846976)
      + ((4637502216867611 : ℝ) / 55340232221128654848) * Real.negMulLog ((7939392106776807 : ℝ) / 1152921504606846976)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8361006940334559 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8361006940456641 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8403920653245797 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8403970387417341 : ℝ) / 4611686018427387904)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726585810355 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726585963219 : ℝ) / 288230376151711744)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((8920726612232719 : ℝ) / 288230376151711744)
      + ((453432722961661 : ℝ) / 576460752303423488) * Real.negMulLog ((62196925554309557 : ℝ) / 288230376151711744)
      + ((681500856867143 : ℝ) / 864691128455135232) * Real.negMulLog ((63166108848603935 : ℝ) / 288230376151711744)
      + ((4586280076839905 : ℝ) / 55340232221128654848) * Real.negMulLog ((102693335658661311 : ℝ) / 576460752303423488)
      + ((885519649630133 : ℝ) / 432345564227567616) * Real.negMulLog ((704016906445344305 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region3_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 3 .Z =
      releasedPhysicalGlobalRegion3MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r3_z0_32]
  rw [physical_global_cell_r3_z1_32]
  rw [physical_global_cell_r3_z2_32]
  rw [physical_global_cell_r3_z3_32]
  rw [physical_global_cell_r3_z4_32]
  rw [physical_global_cell_r3_z5_32]
  rw [physical_global_cell_r3_z6_32]
  unfold releasedPhysicalGlobalRegion3MatrixZ32
  unfold releasedPhysicalGlobalCellR3Z0_32
  unfold releasedPhysicalGlobalCellR3Z1_32
  unfold releasedPhysicalGlobalCellR3Z2_32
  unfold releasedPhysicalGlobalCellR3Z3_32
  unfold releasedPhysicalGlobalCellR3Z4_32
  unfold releasedPhysicalGlobalCellR3Z5_32
  unfold releasedPhysicalGlobalCellR3Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

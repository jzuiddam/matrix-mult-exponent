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

private theorem chunk4_reindex_physical_cell_r3_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR3X0_32 : ℝ :=
  ((2454753528520693 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x0_32 :
    physicalGlobalCellMatrixRate32 3 .X 9 =
      releasedPhysicalGlobalCellR3X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 9 =
      1930496726941585637376 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow07Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X1_32 : ℝ :=
  ((1730712359303572115372437615659957 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((644322612655979 : ℝ) / 4503599627370496)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554141116470573 : ℝ) / 9007199254740992)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((1705572736845531 : ℝ) / 288230376151711744)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((5155132595272205 : ℝ) / 36028797018963968)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216564461603875 : ℝ) / 36028797018963968)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216564463680767 : ℝ) / 36028797018963968)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822290908433859 : ℝ) / 1152921504606846976)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822919346578015 : ℝ) / 1152921504606846976)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822919489019675 : ℝ) / 1152921504606846976)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((198930063509450231 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x1_32 :
    physicalGlobalCellMatrixRate32 3 .X 17 =
      releasedPhysicalGlobalCellR3X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 17 =
      58040511564440754192384 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow06Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X2_32 : ℝ :=
  ((1462949056846746143147879699508879 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((649288174091837 : ℝ) / 72057594037927936)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((1375235828579361 : ℝ) / 144115188075855872)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2003525863387869 : ℝ) / 9007199254740992)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2597152381307269 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2597152695565337 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2750471655769111 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((4007052169271557 : ℝ) / 18014398509481984)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762571403 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762773357 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762951653 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194305391581107 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194305392628989 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5500887670553177 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5500887684333081 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((8014103468855205 : ℝ) / 36028797018963968)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((128225669528498427 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x2_32 :
    physicalGlobalCellMatrixRate32 3 .X 24 =
      releasedPhysicalGlobalCellR3X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 24 =
      551463748926251804393472 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow05Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X3_32 : ℝ :=
  ((4435946076632066039966553014051197 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((71717256370173 : ℝ) / 2251799813685248)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((145612171865437 : ℝ) / 4503599627370496)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((454137811705755 : ℝ) / 288230376151711744)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((573738172318173 : ℝ) / 18014398509481984)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1147476101602049 : ℝ) / 36028797018963968)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1147476342993339 : ℝ) / 36028797018963968)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1816607530317085 : ℝ) / 1152921504606846976)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((2329794656728891 : ℝ) / 72057594037927936)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589904406530993 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589904407086091 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589905390933437 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589905396471083 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4659589462632517 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4659589462654585 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220864057 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220896393 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220932215 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220959237 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1398778556752332111 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x3_32 :
    physicalGlobalCellMatrixRate32 3 .X 30 =
      releasedPhysicalGlobalCellR3X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 30 =
      1454802615897972352745472 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow04Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X4_32 : ℝ :=
  ((720614181908149663441619677491685 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((1612776175853325 : ℝ) / 144115188075855872)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552572470965 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552572626325 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552574879945 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355563934248909 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104709652265 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104710822617 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104716786259 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451105149896099 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711103067610565 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711103069784949 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711127865979255 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781365821890657 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781365847230395 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781366997637231 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((124501872332893363 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x4_32 :
    physicalGlobalCellMatrixRate32 3 .X 35 =
      releasedPhysicalGlobalCellR3X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 35 =
      553568369697324118573056 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow03Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X5_32 : ℝ :=
  ((2541813589826045670275747006253379 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((18090760023239 : ℝ) / 2251799813685248)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((87778398332499 : ℝ) / 562949953421312)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((702227187247133 : ℝ) / 4503599627370496)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((1157808640774343 : ℝ) / 144115188075855872)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315617283399415 : ℝ) / 288230376151711744)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((2808908759580795 : ℝ) / 18014398509481984)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631234340582719 : ℝ) / 576460752303423488)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617817526101913 : ℝ) / 36028797018963968)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((6199666550061837 : ℝ) / 36028797018963968)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((99200828881677943 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x5_32 :
    physicalGlobalCellMatrixRate32 3 .X 39 =
      releasedPhysicalGlobalCellR3X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 39 =
      57324545052201719955456 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow02Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3X6_32 : ℝ :=
  ((407791088479707 : ℝ) / 147573952589676412928) * Real.log (5 : ℝ)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_x6_32 :
    physicalGlobalCellMatrixRate32 3 .X 42 =
      releasedPhysicalGlobalCellR3X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 42 =
      1924199767771637612544 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow01Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion3MatrixX32 : ℝ :=
  ((362778287278456684227966700652146117 : ℝ) / 31901471898837980949691369446728269824) * Real.log (5 : ℝ)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((18090760023239 : ℝ) / 2251799813685248)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((71717256370173 : ℝ) / 2251799813685248)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((87778398332499 : ℝ) / 562949953421312)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((145612171865437 : ℝ) / 4503599627370496)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((454137811705755 : ℝ) / 288230376151711744)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((573738172318173 : ℝ) / 18014398509481984)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((644322612655979 : ℝ) / 4503599627370496)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((649288174091837 : ℝ) / 72057594037927936)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((702227187247133 : ℝ) / 4503599627370496)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1147476101602049 : ℝ) / 36028797018963968)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1147476342993339 : ℝ) / 36028797018963968)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((1157808640774343 : ℝ) / 144115188075855872)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((1375235828579361 : ℝ) / 144115188075855872)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554141116470573 : ℝ) / 9007199254740992)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((1612776175853325 : ℝ) / 144115188075855872)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((1705572736845531 : ℝ) / 288230376151711744)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1816607530317085 : ℝ) / 1152921504606846976)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2003525863387869 : ℝ) / 9007199254740992)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2454753528520693 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315617283399415 : ℝ) / 288230376151711744)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((2329794656728891 : ℝ) / 72057594037927936)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2597152381307269 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2597152695565337 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((2750471655769111 : ℝ) / 288230376151711744)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((2808908759580795 : ℝ) / 18014398509481984)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552572470965 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552572626325 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225552574879945 : ℝ) / 288230376151711744)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((3355563934248909 : ℝ) / 288230376151711744)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((4007052169271557 : ℝ) / 18014398509481984)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((407791088479707 : ℝ) / 147573952589676412928) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589904406530993 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589904407086091 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589905390933437 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589905396471083 : ℝ) / 144115188075855872)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631234340582719 : ℝ) / 576460752303423488)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4659589462632517 : ℝ) / 144115188075855872)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((4659589462654585 : ℝ) / 144115188075855872)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((5155132595272205 : ℝ) / 36028797018963968)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762571403 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762773357 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194304762951653 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194305391581107 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5194305392628989 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5500887670553177 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((5500887684333081 : ℝ) / 576460752303423488)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617817526101913 : ℝ) / 36028797018963968)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((6199666550061837 : ℝ) / 36028797018963968)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216564461603875 : ℝ) / 36028797018963968)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216564463680767 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104709652265 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104710822617 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451104716786259 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451105149896099 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711103067610565 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711103069784949 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711127865979255 : ℝ) / 576460752303423488)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822290908433859 : ℝ) / 1152921504606846976)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822919346578015 : ℝ) / 1152921504606846976)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((6822919489019675 : ℝ) / 1152921504606846976)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220864057 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220896393 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220932215 : ℝ) / 4611686018427387904)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((7038292220959237 : ℝ) / 4611686018427387904)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781365821890657 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781365847230395 : ℝ) / 36028797018963968)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781366997637231 : ℝ) / 36028797018963968)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((8014103468855205 : ℝ) / 36028797018963968)
      + ((4555745526329813 : ℝ) / 55340232221128654848) * Real.negMulLog ((99200828881677943 : ℝ) / 576460752303423488)
      + ((916534612075031 : ℝ) / 1152921504606846976) * Real.negMulLog ((124501872332893363 : ℝ) / 576460752303423488)
      + ((1826100047847469 : ℝ) / 2305843009213693952) * Real.negMulLog ((128225669528498427 : ℝ) / 576460752303423488)
      + ((1537548477502419 : ℝ) / 18446744073709551616) * Real.negMulLog ((198930063509450231 : ℝ) / 1152921504606846976)
      + ((2408694253858547 : ℝ) / 1152921504606846976) * Real.negMulLog ((1398778556752332111 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region3_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 3 .X =
      releasedPhysicalGlobalRegion3MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r3_x0_32]
  rw [physical_global_cell_r3_x1_32]
  rw [physical_global_cell_r3_x2_32]
  rw [physical_global_cell_r3_x3_32]
  rw [physical_global_cell_r3_x4_32]
  rw [physical_global_cell_r3_x5_32]
  rw [physical_global_cell_r3_x6_32]
  unfold releasedPhysicalGlobalRegion3MatrixX32
  unfold releasedPhysicalGlobalCellR3X0_32
  unfold releasedPhysicalGlobalCellR3X1_32
  unfold releasedPhysicalGlobalCellR3X2_32
  unfold releasedPhysicalGlobalCellR3X3_32
  unfold releasedPhysicalGlobalCellR3X4_32
  unfold releasedPhysicalGlobalCellR3X5_32
  unfold releasedPhysicalGlobalCellR3X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

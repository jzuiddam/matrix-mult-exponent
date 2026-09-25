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

private theorem chunk4_reindex_physical_cell_r2_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR2X0_32 : ℝ :=
  ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x0_32 :
    physicalGlobalCellMatrixRate32 2 .X 9 =
      releasedPhysicalGlobalCellR2X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 9 =
      1920771630631269040128 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow01Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X1_32 : ℝ :=
  ((847216667724542616086916456583391 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((1157811603974981 : ℝ) / 144115188075855872)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315623245000967 : ℝ) / 288230376151711744)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315623247261141 : ℝ) / 288230376151711744)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2808817112179027 : ℝ) / 18014398509481984)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2808817113387557 : ℝ) / 18014398509481984)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631246494537337 : ℝ) / 576460752303423488)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617634253553289 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617634259467357 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((6200222411957499 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((99203616390681003 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x1_32 :
    physicalGlobalCellMatrixRate32 2 .X 17 =
      releasedPhysicalGlobalCellR2X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 17 =
      57320860662157453295616 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow02Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X2_32 : ℝ :=
  ((1441177170662329136900176741842465 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((15197995682617 : ℝ) / 70368744177664)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((201600357962323 : ℝ) / 18014398509481984)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((972671723306885 : ℝ) / 4503599627370496)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605720527207 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605720725967 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605963505699 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605963622297 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3890687592837029 : ℝ) / 18014398509481984)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211441081801 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211926957497 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211927017833 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710764331780081 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710764332848119 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710781486776829 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710781488381135 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((124502002990958845 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x2_32 :
    physicalGlobalCellMatrixRate32 2 .X 24 =
      releasedPhysicalGlobalCellR2X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 24 =
      553548343259192591646720 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow03Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X3_32 : ℝ :=
  ((6653974727798501885880325591626757 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((573679758126727 : ℝ) / 18014398509481984)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((878462931846309 : ℝ) / 576460752303423488)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1147359515896273 : ℝ) / 36028797018963968)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1165987628795767 : ℝ) / 36028797018963968)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1756925863676801 : ℝ) / 1152921504606846976)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719032532287 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719034609901 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719097448407 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2331975239894041 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((3513851720330113 : ℝ) / 2305843009213693952)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((3632500594279175 : ℝ) / 2305843009213693952)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438194238793 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438194785911 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438195046721 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4663950499331299 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4663950514385889 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((7027703454132189 : ℝ) / 4611686018427387904)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((7265049192005509 : ℝ) / 4611686018427387904)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1398581664312639201 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x3_32 :
    physicalGlobalCellMatrixRate32 2 .X 30 =
      releasedPhysicalGlobalCellR2X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 30 =
      1454883671367666464980992 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow04Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X4_32 : ℝ :=
  ((1462933624099603983798260548767617 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((21489330635583 : ℝ) / 2251799813685248)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((687652276271837 : ℝ) / 72057594037927936)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((1001689643469009 : ℝ) / 4503599627370496)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((1299710246253063 : ℝ) / 144115188075855872)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420492144703 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420492633145 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420740165551 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420741458561 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198840985232993 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198841480274653 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198841480351315 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5501218207798047 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5501268602596789 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((8013515597568175 : ℝ) / 36028797018963968)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((8013515654997113 : ℝ) / 36028797018963968)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((128216274371391815 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x4_32 :
    physicalGlobalCellMatrixRate32 2 .X 35 =
      releasedPhysicalGlobalCellR2X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 35 =
      551483815218243629481984 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow05Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X5_32 : ℝ :=
  ((432853176342463453237304837421305 : ℝ) / 2658455991569831745807614120560689152) * Real.log (5 : ℝ)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((194277206450993 : ℝ) / 1125899906842624)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((777108825706971 : ℝ) / 4503599627370496)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((1554217652148459 : ℝ) / 9007199254740992)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((2576739492215647 : ℝ) / 18014398509481984)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((3417425911638227 : ℝ) / 576460752303423488)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((5153479198178383 : ℝ) / 36028797018963968)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834850476314147 : ℝ) / 1152921504606846976)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834850481212715 : ℝ) / 1152921504606846976)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834851407929167 : ℝ) / 1152921504606846976)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((198939860312800669 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x5_32 :
    physicalGlobalCellMatrixRate32 2 .X 39 =
      releasedPhysicalGlobalCellR2X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 39 =
      58066524954309364285440 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow06Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2X6_32 : ℝ :=
  ((820218958656555 : ℝ) / 295147905179352825856) * Real.log (5 : ℝ)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_x6_32 :
    physicalGlobalCellMatrixRate32 2 .X 42 =
      releasedPhysicalGlobalCellR2X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 42 =
      1935139308282575585280 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow07Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion2MatrixX32 : ℝ :=
  ((60463116391437253197604543577261393 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((15197995682617 : ℝ) / 70368744177664)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((21489330635583 : ℝ) / 2251799813685248)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((194277206450993 : ℝ) / 1125899906842624)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((201600357962323 : ℝ) / 18014398509481984)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((573679758126727 : ℝ) / 18014398509481984)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((687652276271837 : ℝ) / 72057594037927936)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((777108825706971 : ℝ) / 4503599627370496)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((878462931846309 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((972671723306885 : ℝ) / 4503599627370496)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((1001689643469009 : ℝ) / 4503599627370496)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1147359515896273 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((1157811603974981 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1165987628795767 : ℝ) / 36028797018963968)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((1299710246253063 : ℝ) / 144115188075855872)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((1554217652148459 : ℝ) / 9007199254740992)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1756925863676801 : ℝ) / 1152921504606846976)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4884774858172783 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719032532287 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719034609901 : ℝ) / 72057594037927936)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2294719097448407 : ℝ) / 72057594037927936)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315623245000967 : ℝ) / 288230376151711744)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315623247261141 : ℝ) / 288230376151711744)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((2331975239894041 : ℝ) / 72057594037927936)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((2576739492215647 : ℝ) / 18014398509481984)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420492144703 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420492633145 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420740165551 : ℝ) / 288230376151711744)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((2599420741458561 : ℝ) / 288230376151711744)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2808817112179027 : ℝ) / 18014398509481984)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((2808817113387557 : ℝ) / 18014398509481984)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605720527207 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605720725967 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605963505699 : ℝ) / 288230376151711744)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3225605963622297 : ℝ) / 288230376151711744)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((3417425911638227 : ℝ) / 576460752303423488)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((3513851720330113 : ℝ) / 2305843009213693952)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((3632500594279175 : ℝ) / 2305843009213693952)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((3890687592837029 : ℝ) / 18014398509481984)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((820218958656555 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438194238793 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438194785911 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4589438195046721 : ℝ) / 144115188075855872)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631246494537337 : ℝ) / 576460752303423488)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4663950499331299 : ℝ) / 144115188075855872)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((4663950514385889 : ℝ) / 144115188075855872)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((5153479198178383 : ℝ) / 36028797018963968)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198840985232993 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198841480274653 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5198841480351315 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5501218207798047 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((5501268602596789 : ℝ) / 576460752303423488)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617634253553289 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617634259467357 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((6200222411957499 : ℝ) / 36028797018963968)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211441081801 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211926957497 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6451211927017833 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710764331780081 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710764332848119 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710781486776829 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((6710781488381135 : ℝ) / 576460752303423488)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834850476314147 : ℝ) / 1152921504606846976)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834850481212715 : ℝ) / 1152921504606846976)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((6834851407929167 : ℝ) / 1152921504606846976)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((7027703454132189 : ℝ) / 4611686018427387904)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((7265049192005509 : ℝ) / 4611686018427387904)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((8013515597568175 : ℝ) / 36028797018963968)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((8013515654997113 : ℝ) / 36028797018963968)
      + ((1518484239105581 : ℝ) / 18446744073709551616) * Real.negMulLog ((99203616390681003 : ℝ) / 576460752303423488)
      + ((1833002909220565 : ℝ) / 2305843009213693952) * Real.negMulLog ((124502002990958845 : ℝ) / 576460752303423488)
      + ((5478499484243429 : ℝ) / 6917529027641081856) * Real.negMulLog ((128216274371391815 : ℝ) / 576460752303423488)
      + ((1153678197747655 : ℝ) / 13835058055282163712) * Real.negMulLog ((198939860312800669 : ℝ) / 1152921504606846976)
      + ((3613242684224413 : ℝ) / 1729382256910270464) * Real.negMulLog ((1398581664312639201 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region2_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 2 .X =
      releasedPhysicalGlobalRegion2MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r2_x0_32]
  rw [physical_global_cell_r2_x1_32]
  rw [physical_global_cell_r2_x2_32]
  rw [physical_global_cell_r2_x3_32]
  rw [physical_global_cell_r2_x4_32]
  rw [physical_global_cell_r2_x5_32]
  rw [physical_global_cell_r2_x6_32]
  unfold releasedPhysicalGlobalRegion2MatrixX32
  unfold releasedPhysicalGlobalCellR2X0_32
  unfold releasedPhysicalGlobalCellR2X1_32
  unfold releasedPhysicalGlobalCellR2X2_32
  unfold releasedPhysicalGlobalCellR2X3_32
  unfold releasedPhysicalGlobalCellR2X4_32
  unfold releasedPhysicalGlobalCellR2X5_32
  unfold releasedPhysicalGlobalCellR2X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

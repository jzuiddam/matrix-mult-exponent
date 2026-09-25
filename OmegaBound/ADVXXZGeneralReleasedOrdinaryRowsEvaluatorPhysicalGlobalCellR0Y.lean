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

private theorem chunk4_reindex_physical_cell_r0_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR0Y0_32 : ℝ :=
  ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y0_32 :
    physicalGlobalCellMatrixRate32 0 .Y 16 =
      releasedPhysicalGlobalCellR0Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 16 =
      1906885156246009282560 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow16Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y1_32 : ℝ :=
  ((853420511715517718305583853668289 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((141303262465739 : ℝ) / 18014398509481984)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((2758128963024687 : ℝ) / 18014398509481984)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4521704226753575 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4523454502369871 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4523454524975743 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257913822417 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257925428439 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257926174923 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((6414420679823531 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((102699196709641707 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y1_32 :
    physicalGlobalCellMatrixRate32 0 .Y 23 =
      releasedPhysicalGlobalCellR0Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 23 =
      57695650762568031535104 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow23Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y2_32 : ℝ :=
  ((1425268308161607114500436159048793 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((199994911811399 : ℝ) / 18014398509481984)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((399989866226997 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((799979732716103 : ℝ) / 72057594037927936)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959294469897 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959463432113 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959465486277 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1725258777757545 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3199918588604421 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450511691709695 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450511700186637 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450517554145351 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((6399837178036091 : ℝ) / 576460752303423488)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905128880131 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905137743631 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905339158479 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((124414485459670461 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y2_32 :
    physicalGlobalCellMatrixRate32 0 .Y 29 =
      releasedPhysicalGlobalCellR0Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 29 =
      547681662344044996460544 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow29Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y3_32 : ℝ :=
  ((3266539550376148994235859890984217 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((260846272008321 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((286664311288619 : ℝ) / 9007199254740992)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((558950243325445 : ℝ) / 18014398509481984)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((1043385086800867 : ℝ) / 576460752303423488)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((1146657164877945 : ℝ) / 36028797018963968)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2100583589320215 : ℝ) / 1152921504606846976)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2235801006763253 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2235801028821065 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314329734271 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314488693547 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314489190211 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4173540352113591 : ℝ) / 2305843009213693952)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628658740495 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628659422067 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628978325235 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8347080704306073 : ℝ) / 4611686018427387904)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8402400101826689 : ℝ) / 4611686018427387904)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8943203929859723 : ℝ) / 288230376151711744)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((703737732013823701 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y3_32 :
    physicalGlobalCellMatrixRate32 0 .Y 34 =
      releasedPhysicalGlobalCellR0Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 34 =
      1426467897403731653689344 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow34Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y4_32 : ℝ :=
  ((2163370600230956354843438979028507 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((493528826701499 : ℝ) / 2251799813685248)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418505498984079 : ℝ) / 144115188075855872)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((1605929126659341 : ℝ) / 144115188075855872)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837010998075247 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837011042416789 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211858251828669 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211890037945071 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3948231624372457 : ℝ) / 18014398509481984)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674021996064593 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674021996095831 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022084850251 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022085002123 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022085264425 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423780075605295 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896461200028653 : ℝ) / 36028797018963968)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((63171706000737461 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y4_32 :
    physicalGlobalCellMatrixRate32 0 .Y 38 =
      releasedPhysicalGlobalCellR0Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 38 =
      548817864698209335508992 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow38Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y5_32 : ℝ :=
  ((108330800428582758367665797813823 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((1399774730282987 : ℝ) / 9007199254740992)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((1985705671880815 : ℝ) / 288230376151711744)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((2799549531869295 : ℝ) / 18014398509481984)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((3971411358705063 : ℝ) / 576460752303423488)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((3971411540414611 : ℝ) / 576460752303423488)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436535947591 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436542428089 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436542536875 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((7942823352185909 : ℝ) / 1152921504606846976)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((190701969383839483 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y5_32 :
    physicalGlobalCellMatrixRate32 0 .Y 41 =
      releasedPhysicalGlobalCellR0Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 41 =
      58359363296346318569472 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow41Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Y6_32 : ℝ :=
  ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_y6_32 :
    physicalGlobalCellMatrixRate32 0 .Y 43 =
      releasedPhysicalGlobalCellR0Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 43 =
      1927017389007710846976 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow43Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion0MatrixY32 : ℝ :=
  ((178597656615965397666013440054483539 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((141303262465739 : ℝ) / 18014398509481984)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((199994911811399 : ℝ) / 18014398509481984)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((260846272008321 : ℝ) / 144115188075855872)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((286664311288619 : ℝ) / 9007199254740992)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((399989866226997 : ℝ) / 36028797018963968)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((493528826701499 : ℝ) / 2251799813685248)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((558950243325445 : ℝ) / 18014398509481984)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((799979732716103 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((1043385086800867 : ℝ) / 576460752303423488)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((1146657164877945 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((1399774730282987 : ℝ) / 9007199254740992)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418505498984079 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959294469897 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959463432113 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1599959465486277 : ℝ) / 144115188075855872)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((1605929126659341 : ℝ) / 144115188075855872)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((1725258777757545 : ℝ) / 144115188075855872)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((1985705671880815 : ℝ) / 288230376151711744)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2100583589320215 : ℝ) / 1152921504606846976)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2235801006763253 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2235801028821065 : ℝ) / 72057594037927936)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4849459727595035 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314329734271 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314488693547 : ℝ) / 72057594037927936)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((2293314489190211 : ℝ) / 72057594037927936)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((2758128963024687 : ℝ) / 18014398509481984)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((2799549531869295 : ℝ) / 18014398509481984)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837010998075247 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837011042416789 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3199918588604421 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211858251828669 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211890037945071 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450511691709695 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450511700186637 : ℝ) / 288230376151711744)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450517554145351 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((3948231624372457 : ℝ) / 18014398509481984)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((3971411358705063 : ℝ) / 576460752303423488)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((3971411540414611 : ℝ) / 576460752303423488)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4173540352113591 : ℝ) / 2305843009213693952)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4900658643106361 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4521704226753575 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4523454502369871 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((4523454524975743 : ℝ) / 576460752303423488)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628658740495 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628659422067 : ℝ) / 144115188075855872)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((4586628978325235 : ℝ) / 144115188075855872)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257913822417 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257925428439 : ℝ) / 36028797018963968)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((5516257926174923 : ℝ) / 36028797018963968)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674021996064593 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674021996095831 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022084850251 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022085002123 : ℝ) / 576460752303423488)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674022085264425 : ℝ) / 576460752303423488)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436535947591 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436542428089 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((5959436542536875 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((6399837178036091 : ℝ) / 576460752303423488)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((6414420679823531 : ℝ) / 36028797018963968)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423780075605295 : ℝ) / 576460752303423488)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905128880131 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905137743631 : ℝ) / 36028797018963968)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((7775905339158479 : ℝ) / 36028797018963968)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896461200028653 : ℝ) / 36028797018963968)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((7942823352185909 : ℝ) / 1152921504606846976)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8347080704306073 : ℝ) / 4611686018427387904)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8402400101826689 : ℝ) / 4611686018427387904)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((8943203929859723 : ℝ) / 288230376151711744)
      + ((5452015645287527 : ℝ) / 6917529027641081856) * Real.negMulLog ((63171706000737461 : ℝ) / 288230376151711744)
      + ((1528412786127939 : ℝ) / 18446744073709551616) * Real.negMulLog ((102699196709641707 : ℝ) / 576460752303423488)
      + ((5440728489002039 : ℝ) / 6917529027641081856) * Real.negMulLog ((124414485459670461 : ℝ) / 576460752303423488)
      + ((96624697738797 : ℝ) / 1152921504606846976) * Real.negMulLog ((190701969383839483 : ℝ) / 1152921504606846976)
      + ((3542671346176991 : ℝ) / 1729382256910270464) * Real.negMulLog ((703737732013823701 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region0_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 0 .Y =
      releasedPhysicalGlobalRegion0MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r0_y0_32]
  rw [physical_global_cell_r0_y1_32]
  rw [physical_global_cell_r0_y2_32]
  rw [physical_global_cell_r0_y3_32]
  rw [physical_global_cell_r0_y4_32]
  rw [physical_global_cell_r0_y5_32]
  rw [physical_global_cell_r0_y6_32]
  unfold releasedPhysicalGlobalRegion0MatrixY32
  unfold releasedPhysicalGlobalCellR0Y0_32
  unfold releasedPhysicalGlobalCellR0Y1_32
  unfold releasedPhysicalGlobalCellR0Y2_32
  unfold releasedPhysicalGlobalCellR0Y3_32
  unfold releasedPhysicalGlobalCellR0Y4_32
  unfold releasedPhysicalGlobalCellR0Y5_32
  unfold releasedPhysicalGlobalCellR0Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

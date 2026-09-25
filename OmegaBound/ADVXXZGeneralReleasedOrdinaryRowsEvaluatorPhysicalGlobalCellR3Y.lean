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

private theorem chunk4_reindex_physical_cell_r3_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR3Y0_32 : ℝ :=
  ((19215205390979 : ℝ) / 6917529027641081856) * Real.log (5 : ℝ)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y0_32 :
    physicalGlobalCellMatrixRate32 3 .Y 16 =
      releasedPhysicalGlobalCellR3Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 16 =
      1934265907972914806784 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow42Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y1_32 : ℝ :=
  ((1313978341122304154624749732898375 : ℝ) / 7975367974709495237422842361682067456) * Real.log (5 : ℝ)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((697485543926157 : ℝ) / 4503599627370496)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((744599491333893 : ℝ) / 4503599627370496)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((4167374326688961 : ℝ) / 576460752303423488)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((4167374680255723 : ℝ) / 576460752303423488)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5579885472895301 : ℝ) / 36028797018963968)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5956795775518305 : ℝ) / 36028797018963968)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5956795930912991 : ℝ) / 36028797018963968)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((8334748655115715 : ℝ) / 1152921504606846976)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((8334749374618707 : ℝ) / 1152921504606846976)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((95308734899099641 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y1_32 :
    physicalGlobalCellMatrixRate32 3 .Y 23 =
      releasedPhysicalGlobalCellR3Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 23 =
      59070854393628721152000 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow39Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y2_32 : ℝ :=
  ((364868551078115870925351000630737 : ℝ) / 166153499473114484112975882535043072) * Real.log (5 : ℝ)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((89741881342681 : ℝ) / 9007199254740992)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((179483761910409 : ℝ) / 18014398509481984)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((358967525374001 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((1971816193032105 : ℝ) / 9007199254740992)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740190539091 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740190603503 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740202328043 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740203045929 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((3215996291934041 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((5743480381069249 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431985753369429 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431985760518419 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431992583954501 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((7887264769731097 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((7887264980689571 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((31549060028444145 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y2_32 :
    physicalGlobalCellMatrixRate32 3 .Y 29 =
      releasedPhysicalGlobalCellR3Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 29 =
      555785538550316748767232 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow35Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y3_32 : ℝ :=
  ((3305068644983067890259108709766405 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((36637891114133 : ℝ) / 1125899906842624)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((1007046908333717 : ℝ) / 576460752303423488)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172412566978871 : ℝ) / 36028797018963968)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344825133921717 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344825621100133 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368178331657581 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368178333040865 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4028187633402889 : ℝ) / 2305843009213693952)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4169681549765459 : ℝ) / 2305843009213693952)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4169797860001213 : ℝ) / 2305843009213693952)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689650267959079 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651221941835 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651227817045 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651253856253 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736356620040943 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736356620244967 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056375266514363 : ℝ) / 4611686018427387904)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056375266662727 : ℝ) / 4611686018427387904)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((688994330580698713 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y3_32 :
    physicalGlobalCellMatrixRate32 3 .Y 34 =
      releasedPhysicalGlobalCellR3Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 34 =
      1454668951284149146091520 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow30Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y4_32 : ℝ :=
  ((1069193482048683851425022508507391 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((101043310201563 : ℝ) / 9007199254740992)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((972073514971959 : ℝ) / 4503599627370496)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616692961509679 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616692964879507 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616693079086927 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616693079145379 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1689059049566179 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1944147311896197 : ℝ) / 9007199254740992)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((3233386155679133 : ℝ) / 288230376151711744)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((3888294060060333 : ℝ) / 18014398509481984)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6466771855739565 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6466772311504967 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756213280279763 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756213280547351 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756236198961211 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((124425428875683633 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y4_32 :
    physicalGlobalCellMatrixRate32 3 .Y 38 =
      releasedPhysicalGlobalCellR3Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 38 =
      547775292164682031300608 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow24Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y5_32 : ℝ :=
  ((629064894555386114077551906088843 : ℝ) / 3987683987354747618711421180841033728) * Real.log (5 : ℝ)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((579014454808033 : ℝ) / 72057594037927936)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((702269145631011 : ℝ) / 4503599627370496)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((1158028967075995 : ℝ) / 144115188075855872)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((1549721271585795 : ℝ) / 9007199254740992)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316057931454617 : ℝ) / 288230376151711744)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316057933915691 : ℝ) / 288230376151711744)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809076578256451 : ℝ) / 18014398509481984)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809076583158431 : ℝ) / 18014398509481984)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618153161751105 : ℝ) / 36028797018963968)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((24797081322590109 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y5_32 :
    physicalGlobalCellMatrixRate32 3 .Y 41 =
      releasedPhysicalGlobalCellR3Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 41 =
      56748593803249569497088 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow17Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR3Y6_32 : ℝ :=
  ((810037284794007 : ℝ) / 295147905179352825856) * Real.log (5 : ℝ)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r3_y6_32 :
    physicalGlobalCellMatrixRate32 3 .Y 43 =
      releasedPhysicalGlobalCellR3Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 3 43 =
      1911117725865361539072 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 3 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r3_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow09Dist,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR3CertificateSplitData.r3ResZRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR3Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion3MatrixY32 : ℝ :=
  ((30039344913228363383255122049355503 : ℝ) / 2658455991569831745807614120560689152) * Real.log (5 : ℝ)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((36637891114133 : ℝ) / 1125899906842624)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((89741881342681 : ℝ) / 9007199254740992)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((101043310201563 : ℝ) / 9007199254740992)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((179483761910409 : ℝ) / 18014398509481984)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((358967525374001 : ℝ) / 36028797018963968)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((579014454808033 : ℝ) / 72057594037927936)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((697485543926157 : ℝ) / 4503599627370496)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((702269145631011 : ℝ) / 4503599627370496)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((744599491333893 : ℝ) / 4503599627370496)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((972073514971959 : ℝ) / 4503599627370496)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((1007046908333717 : ℝ) / 576460752303423488)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((1158028967075995 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172412566978871 : ℝ) / 36028797018963968)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((1549721271585795 : ℝ) / 9007199254740992)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616692961509679 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616692964879507 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616693079086927 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1616693079145379 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1689059049566179 : ℝ) / 144115188075855872)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((1944147311896197 : ℝ) / 9007199254740992)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((1971816193032105 : ℝ) / 9007199254740992)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((19215205390979 : ℝ) / 6917529027641081856) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316057931454617 : ℝ) / 288230376151711744)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316057933915691 : ℝ) / 288230376151711744)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344825133921717 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344825621100133 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368178331657581 : ℝ) / 72057594037927936)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368178333040865 : ℝ) / 72057594037927936)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809076578256451 : ℝ) / 18014398509481984)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809076583158431 : ℝ) / 18014398509481984)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740190539091 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740190603503 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740202328043 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((2871740203045929 : ℝ) / 288230376151711744)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((3215996291934041 : ℝ) / 288230376151711744)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((3233386155679133 : ℝ) / 288230376151711744)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((3888294060060333 : ℝ) / 18014398509481984)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4028187633402889 : ℝ) / 2305843009213693952)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((4167374326688961 : ℝ) / 576460752303423488)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((4167374680255723 : ℝ) / 576460752303423488)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4169681549765459 : ℝ) / 2305843009213693952)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4169797860001213 : ℝ) / 2305843009213693952)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((810037284794007 : ℝ) / 295147905179352825856) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689650267959079 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651221941835 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651227817045 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689651253856253 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736356620040943 : ℝ) / 144115188075855872)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736356620244967 : ℝ) / 144115188075855872)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5579885472895301 : ℝ) / 36028797018963968)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618153161751105 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((5743480381069249 : ℝ) / 576460752303423488)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5956795775518305 : ℝ) / 36028797018963968)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((5956795930912991 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431985753369429 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431985760518419 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((6431992583954501 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6466771855739565 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6466772311504967 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756213280279763 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756213280547351 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((6756236198961211 : ℝ) / 576460752303423488)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((7887264769731097 : ℝ) / 36028797018963968)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((7887264980689571 : ℝ) / 36028797018963968)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056375266514363 : ℝ) / 4611686018427387904)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056375266662727 : ℝ) / 4611686018427387904)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((8334748655115715 : ℝ) / 1152921504606846976)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((8334749374618707 : ℝ) / 1152921504606846976)
      + ((4509973033527499 : ℝ) / 55340232221128654848) * Real.negMulLog ((24797081322590109 : ℝ) / 144115188075855872)
      + ((1840411088699489 : ℝ) / 2305843009213693952) * Real.negMulLog ((31549060028444145 : ℝ) / 144115188075855872)
      + ((2347264861807375 : ℝ) / 27670116110564327424) * Real.negMulLog ((95308734899099641 : ℝ) / 576460752303423488)
      + ((1360414654425487 : ℝ) / 1729382256910270464) * Real.negMulLog ((124425428875683633 : ℝ) / 576460752303423488)
      + ((3612709421128405 : ℝ) / 1729382256910270464) * Real.negMulLog ((688994330580698713 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region3_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 3 .Y =
      releasedPhysicalGlobalRegion3MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r3_y0_32]
  rw [physical_global_cell_r3_y1_32]
  rw [physical_global_cell_r3_y2_32]
  rw [physical_global_cell_r3_y3_32]
  rw [physical_global_cell_r3_y4_32]
  rw [physical_global_cell_r3_y5_32]
  rw [physical_global_cell_r3_y6_32]
  unfold releasedPhysicalGlobalRegion3MatrixY32
  unfold releasedPhysicalGlobalCellR3Y0_32
  unfold releasedPhysicalGlobalCellR3Y1_32
  unfold releasedPhysicalGlobalCellR3Y2_32
  unfold releasedPhysicalGlobalCellR3Y3_32
  unfold releasedPhysicalGlobalCellR3Y4_32
  unfold releasedPhysicalGlobalCellR3Y5_32
  unfold releasedPhysicalGlobalCellR3Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

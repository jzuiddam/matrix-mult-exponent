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

private theorem chunk4_reindex_physical_cell_r1_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR1Z0_32 : ℝ :=
  ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z0_32 :
    physicalGlobalCellMatrixRate32 1 .Z 1 =
      releasedPhysicalGlobalCellR1Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 1 =
      1936653414294013476864 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow07Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z1_32 : ℝ :=
  ((865836792155349618842830355227875 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554195199213949 : ℝ) / 9007199254740992)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554195199220911 : ℝ) / 9007199254740992)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((5153476135088481 : ℝ) / 36028797018963968)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((5153600832812907 : ℝ) / 36028797018963968)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216780792944341 : ℝ) / 36028797018963968)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836703704929815 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836703751906697 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836846032037827 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836846039070259 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((99468492866088485 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z1_32 :
    physicalGlobalCellMatrixRate32 1 .Z 2 =
      releasedPhysicalGlobalCellR1Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 2 =
      58075671121658118144000 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow06Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z2_32 : ℝ :=
  ((45717941157673328983927673257653 : ℝ) / 20769187434139310514121985316880384) * Real.log (5 : ℝ)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((1375429854519879 : ℝ) / 144115188075855872)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((1375450705226557 : ℝ) / 144115188075855872)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542503213055 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504087119 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504305679 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504429345 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542649214771 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651355421 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651364347 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651367789 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5501719418239031 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5501802828199153 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014270262188385 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014270263509441 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014272442468749 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((64114179853998417 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z2_32 :
    physicalGlobalCellMatrixRate32 1 .Z 3 =
      releasedPhysicalGlobalCellR1Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 3 =
      551465817989000164540416 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow05Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z3_32 : ℝ :=
  ((69312135212845320179570650777197 : ℝ) / 10384593717069655257060992658440192) * Real.log (5 : ℝ)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((71705275847843 : ℝ) / 2251799813685248)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((286821059191297 : ℝ) / 9007199254740992)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((439482164456943 : ℝ) / 288230376151711744)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((573642117906583 : ℝ) / 18014398509481984)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((908498789150091 : ℝ) / 576460752303423488)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((1147284414049297 : ℝ) / 36028797018963968)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((1816965033858471 : ℝ) / 1152921504606846976)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2294568767212505 : ℝ) / 72057594037927936)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2331221243443465 : ℝ) / 72057594037927936)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2331221285569421 : ℝ) / 72057594037927936)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((3515857327142637 : ℝ) / 2305843009213693952)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589136945197477 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589136946466121 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589137655545031 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4662442624202535 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4662442638090295 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((7031714630802509 : ℝ) / 4611686018427387904)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((7031714631153413 : ℝ) / 4611686018427387904)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((174838219634000469 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z3_32 :
    physicalGlobalCellMatrixRate32 1 .Z 4 =
      releasedPhysicalGlobalCellR1Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 4 =
      1454836837500488238759936 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow04Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z4_32 : ℝ :=
  ((1080867833874552236140865389693933 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((1677637354938517 : ℝ) / 144115188075855872)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606528394367 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606550698409 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606550915711 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606551192389 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3355274707657633 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3890694139155145 : ℝ) / 18014398509481984)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3890694149596185 : ℝ) / 18014398509481984)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213056557397 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213056931429 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213058606521 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213097044373 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6710549013426925 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6710549016387865 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((7781388294368595 : ℝ) / 36028797018963968)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((31125553214264453 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z4_32 :
    physicalGlobalCellMatrixRate32 1 .Z 5 =
      releasedPhysicalGlobalCellR1Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 5 =
      553540016664199563313152 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow03Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z5_32 : ℝ :=
  ((211833326561429687205218384901935 : ℝ) / 1329227995784915872903807060280344576) * Real.log (5 : ℝ)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((702381676792343 : ℝ) / 4503599627370496)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((1404763358781317 : ℝ) / 9007199254740992)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315607957135009 : ℝ) / 288230376151711744)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315607976543411 : ℝ) / 288230376151711744)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809526665712577 : ℝ) / 18014398509481984)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809526706346779 : ℝ) / 18014398509481984)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631215886440983 : ℝ) / 576460752303423488)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631216050878525 : ℝ) / 576460752303423488)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((6194063609307035 : ℝ) / 36028797018963968)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((24802863313127749 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z5_32 :
    physicalGlobalCellMatrixRate32 1 .Z 6 =
      releasedPhysicalGlobalCellR1Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 6 =
      57328739629102767538176 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow02Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Z6_32 : ℝ :=
  ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_z6_32 :
    physicalGlobalCellMatrixRate32 1 .Z 7 =
      releasedPhysicalGlobalCellR1Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 7 =
      1930098616210254594048 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 1 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow01Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResZRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion1MatrixZ32 : ℝ :=
  ((60463557733537926017441675023710847 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((71705275847843 : ℝ) / 2251799813685248)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((286821059191297 : ℝ) / 9007199254740992)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((439482164456943 : ℝ) / 288230376151711744)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((573642117906583 : ℝ) / 18014398509481984)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((702381676792343 : ℝ) / 4503599627370496)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((908498789150091 : ℝ) / 576460752303423488)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((1147284414049297 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((1375429854519879 : ℝ) / 144115188075855872)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((1375450705226557 : ℝ) / 144115188075855872)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((1404763358781317 : ℝ) / 9007199254740992)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554195199213949 : ℝ) / 9007199254740992)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((1554195199220911 : ℝ) / 9007199254740992)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((1677637354938517 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((1816965033858471 : ℝ) / 1152921504606846976)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4925164322647129 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2294568767212505 : ℝ) / 72057594037927936)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315607957135009 : ℝ) / 288230376151711744)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2315607976543411 : ℝ) / 288230376151711744)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2331221243443465 : ℝ) / 72057594037927936)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((2331221285569421 : ℝ) / 72057594037927936)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809526665712577 : ℝ) / 18014398509481984)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((2809526706346779 : ℝ) / 18014398509481984)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606528394367 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606550698409 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606550915711 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3225606551192389 : ℝ) / 288230376151711744)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3355274707657633 : ℝ) / 288230376151711744)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((3515857327142637 : ℝ) / 2305843009213693952)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3890694139155145 : ℝ) / 18014398509481984)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((3890694149596185 : ℝ) / 18014398509481984)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4908494609095903 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589136945197477 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589136946466121 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4589137655545031 : ℝ) / 144115188075855872)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631215886440983 : ℝ) / 576460752303423488)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((4631216050878525 : ℝ) / 576460752303423488)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4662442624202535 : ℝ) / 144115188075855872)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((4662442638090295 : ℝ) / 144115188075855872)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((5153476135088481 : ℝ) / 36028797018963968)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((5153600832812907 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542503213055 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504087119 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504305679 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542504429345 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542649214771 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651355421 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651364347 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5192542651367789 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5501719418239031 : ℝ) / 576460752303423488)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((5501802828199153 : ℝ) / 576460752303423488)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((6194063609307035 : ℝ) / 36028797018963968)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216780792944341 : ℝ) / 36028797018963968)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213056557397 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213056931429 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213058606521 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6451213097044373 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6710549013426925 : ℝ) / 576460752303423488)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((6710549016387865 : ℝ) / 576460752303423488)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836703704929815 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836703751906697 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836846032037827 : ℝ) / 1152921504606846976)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((6836846039070259 : ℝ) / 1152921504606846976)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((7031714630802509 : ℝ) / 4611686018427387904)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((7031714631153413 : ℝ) / 4611686018427387904)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((7781388294368595 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014270262188385 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014270263509441 : ℝ) / 36028797018963968)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((8014272442468749 : ℝ) / 36028797018963968)
      + ((4556078881351373 : ℝ) / 55340232221128654848) * Real.negMulLog ((24802863313127749 : ℝ) / 144115188075855872)
      + ((5498926010372237 : ℝ) / 6917529027641081856) * Real.negMulLog ((31125553214264453 : ℝ) / 144115188075855872)
      + ((114131681204877 : ℝ) / 144115188075855872) * Real.negMulLog ((64114179853998417 : ℝ) / 288230376151711744)
      + ((1538479887688375 : ℝ) / 18446744073709551616) * Real.negMulLog ((99468492866088485 : ℝ) / 576460752303423488)
      + ((602187728509509 : ℝ) / 288230376151711744) * Real.negMulLog ((174838219634000469 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region1_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 1 .Z =
      releasedPhysicalGlobalRegion1MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r1_z0_32]
  rw [physical_global_cell_r1_z1_32]
  rw [physical_global_cell_r1_z2_32]
  rw [physical_global_cell_r1_z3_32]
  rw [physical_global_cell_r1_z4_32]
  rw [physical_global_cell_r1_z5_32]
  rw [physical_global_cell_r1_z6_32]
  unfold releasedPhysicalGlobalRegion1MatrixZ32
  unfold releasedPhysicalGlobalCellR1Z0_32
  unfold releasedPhysicalGlobalCellR1Z1_32
  unfold releasedPhysicalGlobalCellR1Z2_32
  unfold releasedPhysicalGlobalCellR1Z3_32
  unfold releasedPhysicalGlobalCellR1Z4_32
  unfold releasedPhysicalGlobalCellR1Z5_32
  unfold releasedPhysicalGlobalCellR1Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

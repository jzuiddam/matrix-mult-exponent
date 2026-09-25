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

private theorem chunk4_reindex_physical_cell_r1_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR1X0_32 : ℝ :=
  ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x0_32 :
    physicalGlobalCellMatrixRate32 1 .X 9 =
      releasedPhysicalGlobalCellR1X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 9 =
      1909712642135466049536 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow16Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X1_32 : ℝ :=
  ((853163368132938119486880854629251 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((2257631050233097 : ℝ) / 288230376151711744)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((2757791778097583 : ℝ) / 18014398509481984)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((3209372797281857 : ℝ) / 18014398509481984)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515262110968073 : ℝ) / 576460752303423488)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515322859383847 : ℝ) / 576460752303423488)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515322947412257 : ℝ) / 576460752303423488)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583550425813 : ℝ) / 36028797018963968)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583550561923 : ℝ) / 36028797018963968)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583552218871 : ℝ) / 36028797018963968)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((102702305421745325 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x1_32 :
    physicalGlobalCellMatrixRate32 1 .X 17 =
      releasedPhysicalGlobalCellR1X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 17 =
      57675255802882223505408 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow23Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X2_32 : ℝ :=
  ((1068934252688210984347687150504039 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((1601760094576007 : ℝ) / 144115188075855872)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((1725535847003029 : ℝ) / 144115188075855872)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3203520388322991 : ℝ) / 288230376151711744)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3451052857770477 : ℝ) / 288230376151711744)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3887467916183555 : ℝ) / 18014398509481984)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040362528737 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040363774043 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040363800307 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776469797 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776472865 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776474655 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6902105719686157 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6902143388382317 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((7774935875549455 : ℝ) / 36028797018963968)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((7774936942566673 : ℝ) / 36028797018963968)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((62199495554799861 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x2_32 :
    physicalGlobalCellMatrixRate32 1 .X 24 =
      releasedPhysicalGlobalCellR1X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 24 =
      547716177514728127463424 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow29Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X3_32 : ℝ :=
  ((1088826242536916503195311385350693 : ℝ) / 166153499473114484112975882535043072) * Real.log (5 : ℝ)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((278600409430113 : ℝ) / 9007199254740992)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((278600413884855 : ℝ) / 9007199254740992)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((573454642340307 : ℝ) / 18014398509481984)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909284447687 : ℝ) / 36028797018963968)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909325341235 : ℝ) / 36028797018963968)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909326133305 : ℝ) / 36028797018963968)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((2091779070295891 : ℝ) / 1152921504606846976)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((2293818568077715 : ℝ) / 72057594037927936)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4183558140642667 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4183558141572139 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4202085759988519 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4457606547532481 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637136626717 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637302919591 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637302969893 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8367116280696891 : ℝ) / 4611686018427387904)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8404153268221137 : ℝ) / 4611686018427387904)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8915213204494377 : ℝ) / 288230376151711744)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1408200228914005391 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x3_32 :
    physicalGlobalCellMatrixRate32 1 .X 30 =
      releasedPhysicalGlobalCellR1X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 30 =
      1426177270553102990180352 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow34Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X4_32 : ℝ :=
  ((1081701271355098674369034694472577 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((401450956075759 : ℝ) / 36028797018963968)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((1419615522858591 : ℝ) / 144115188075855872)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((2839230657190603 : ℝ) / 288230376151711744)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((2839230657369863 : ℝ) / 288230376151711744)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((3947969060547045 : ℝ) / 18014398509481984)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((3947969818410021 : ℝ) / 18014398509481984)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678461314298167 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678461314375187 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091012135 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091494357 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091510557 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423215303941239 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423270185849573 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423270186907469 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((7895938086042365 : ℝ) / 36028797018963968)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((31583758550740853 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x4_32 :
    physicalGlobalCellMatrixRate32 1 .X 35 =
      releasedPhysicalGlobalCellR1X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 35 =
      548849132981247799197696 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow38Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X5_32 : ℝ :=
  ((866776125213440485717487066413853 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((992474071767249 : ℝ) / 144115188075855872)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((992474155505571 : ℝ) / 144115188075855872)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((2799549510808427 : ℝ) / 18014398509481984)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((2979766540090969 : ℝ) / 18014398509481984)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((3969896254340587 : ℝ) / 576460752303423488)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5599091560653873 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5959533079780041 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5959533080477749 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((7939792510118933 : ℝ) / 1152921504606846976)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((190705059443129749 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x5_32 :
    physicalGlobalCellMatrixRate32 1 .X 39 =
      releasedPhysicalGlobalCellR1X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 39 =
      58367467647198585421824 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow41Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1X6_32 : ℝ :=
  ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_x6_32 :
    physicalGlobalCellMatrixRate32 1 .X 42 =
      releasedPhysicalGlobalCellR1X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 42 =
      1924810913040177168384 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow43Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion1MatrixX32 : ℝ :=
  ((2790551719016409501200010296908603 : ℝ) / 249230249209671726169463823802564608) * Real.log (5 : ℝ)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((278600409430113 : ℝ) / 9007199254740992)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((278600413884855 : ℝ) / 9007199254740992)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((401450956075759 : ℝ) / 36028797018963968)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((573454642340307 : ℝ) / 18014398509481984)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((992474071767249 : ℝ) / 144115188075855872)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((992474155505571 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909284447687 : ℝ) / 36028797018963968)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909325341235 : ℝ) / 36028797018963968)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1146909326133305 : ℝ) / 36028797018963968)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((1419615522858591 : ℝ) / 144115188075855872)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((1601760094576007 : ℝ) / 144115188075855872)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((1725535847003029 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((2091779070295891 : ℝ) / 1152921504606846976)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4856650396055771 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((2257631050233097 : ℝ) / 288230376151711744)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((2293818568077715 : ℝ) / 72057594037927936)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((2757791778097583 : ℝ) / 18014398509481984)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((2799549510808427 : ℝ) / 18014398509481984)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((2839230657190603 : ℝ) / 288230376151711744)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((2839230657369863 : ℝ) / 288230376151711744)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((2979766540090969 : ℝ) / 18014398509481984)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3203520388322991 : ℝ) / 288230376151711744)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((3209372797281857 : ℝ) / 18014398509481984)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3451052857770477 : ℝ) / 288230376151711744)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((3887467916183555 : ℝ) / 18014398509481984)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((3947969060547045 : ℝ) / 18014398509481984)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((3947969818410021 : ℝ) / 18014398509481984)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((3969896254340587 : ℝ) / 576460752303423488)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4183558140642667 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4183558141572139 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4202085759988519 : ℝ) / 2305843009213693952)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4457606547532481 : ℝ) / 144115188075855872)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4895047284546349 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515262110968073 : ℝ) / 576460752303423488)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515322859383847 : ℝ) / 576460752303423488)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((4515322947412257 : ℝ) / 576460752303423488)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637136626717 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637302919591 : ℝ) / 144115188075855872)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((4587637302969893 : ℝ) / 144115188075855872)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583550425813 : ℝ) / 36028797018963968)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583550561923 : ℝ) / 36028797018963968)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((5515583552218871 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5599091560653873 : ℝ) / 36028797018963968)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678461314298167 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678461314375187 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091012135 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091494357 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((5678462091510557 : ℝ) / 576460752303423488)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5959533079780041 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((5959533080477749 : ℝ) / 36028797018963968)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040362528737 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040363774043 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040363800307 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776469797 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776472865 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6407040776474655 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423215303941239 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423270185849573 : ℝ) / 576460752303423488)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423270186907469 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6902105719686157 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((6902143388382317 : ℝ) / 576460752303423488)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((7774935875549455 : ℝ) / 36028797018963968)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((7774936942566673 : ℝ) / 36028797018963968)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((7895938086042365 : ℝ) / 36028797018963968)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((7939792510118933 : ℝ) / 1152921504606846976)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8367116280696891 : ℝ) / 4611686018427387904)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8404153268221137 : ℝ) / 4611686018427387904)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((8915213204494377 : ℝ) / 288230376151711744)
      + ((5452326267771401 : ℝ) / 6917529027641081856) * Real.negMulLog ((31583758550740853 : ℝ) / 144115188075855872)
      + ((2720535683208347 : ℝ) / 3458764513820540928) * Real.negMulLog ((62199495554799861 : ℝ) / 288230376151711744)
      + ((1527872504204703 : ℝ) / 18446744073709551616) * Real.negMulLog ((102702305421745325 : ℝ) / 576460752303423488)
      + ((2319314783700251 : ℝ) / 27670116110564327424) * Real.negMulLog ((190705059443129749 : ℝ) / 1152921504606846976)
      + ((590324927764263 : ℝ) / 288230376151711744) * Real.negMulLog ((1408200228914005391 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region1_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 1 .X =
      releasedPhysicalGlobalRegion1MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r1_x0_32]
  rw [physical_global_cell_r1_x1_32]
  rw [physical_global_cell_r1_x2_32]
  rw [physical_global_cell_r1_x3_32]
  rw [physical_global_cell_r1_x4_32]
  rw [physical_global_cell_r1_x5_32]
  rw [physical_global_cell_r1_x6_32]
  unfold releasedPhysicalGlobalRegion1MatrixX32
  unfold releasedPhysicalGlobalCellR1X0_32
  unfold releasedPhysicalGlobalCellR1X1_32
  unfold releasedPhysicalGlobalCellR1X2_32
  unfold releasedPhysicalGlobalCellR1X3_32
  unfold releasedPhysicalGlobalCellR1X4_32
  unfold releasedPhysicalGlobalCellR1X5_32
  unfold releasedPhysicalGlobalCellR1X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

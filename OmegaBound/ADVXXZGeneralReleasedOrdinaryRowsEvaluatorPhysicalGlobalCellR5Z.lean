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

private theorem chunk4_reindex_physical_cell_r5_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR5Z0_32 : ℝ :=
  ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z0_32 :
    physicalGlobalCellMatrixRate32 5 .Z 1 =
      releasedPhysicalGlobalCellR5Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 1 =
      1932845645987795042304 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow43Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z1_32 : ℝ :=
  ((5197289850231932897038721582285441 : ℝ) / 31901471898837980949691369446728269824) * Real.log (5 : ℝ)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((744955001779329 : ℝ) / 4503599627370496)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((1399702056115187 : ℝ) / 9007199254740992)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489910003808419 : ℝ) / 9007199254740992)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979820007357017 : ℝ) / 18014398509481984)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970474363237421 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970474668706215 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970475081645577 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((5598810008976781 : ℝ) / 36028797018963968)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((7940950152574601 : ℝ) / 1152921504606846976)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((190708481343258077 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z1_32 :
    physicalGlobalCellMatrixRate32 5 .Z 2 =
      releasedPhysicalGlobalCellR5Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 2 =
      58329921348919684497408 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow41Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z2_32 : ℝ :=
  ((2163459428590990876597187826140861 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418736794586183 : ℝ) / 144115188075855872)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418736798630153 : ℝ) / 144115188075855872)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1605902988946421 : ℝ) / 144115188075855872)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837473589195869 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837473597234069 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211838302947557 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947178511215 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947178691357 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947194305421 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947195774197 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423611954702639 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423676611965371 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896352048222485 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896352068886419 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896354116754551 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((63170832970125995 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z2_32 :
    physicalGlobalCellMatrixRate32 5 .Z 3 =
      releasedPhysicalGlobalCellR5Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 3 =
      548845230072312688017408 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow38Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z3_32 : ℝ :=
  ((6532921411928096657889914809199221 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((65360951383523 : ℝ) / 36028797018963968)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((573409808244599 : ℝ) / 18014398509481984)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((573409845862639 : ℝ) / 18014398509481984)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1114489316101533 : ℝ) / 36028797018963968)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146819616583631 : ℝ) / 36028797018963968)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146819690848451 : ℝ) / 36028797018963968)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((2091550444288173 : ℝ) / 1152921504606846976)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293639233683569 : ℝ) / 72057594037927936)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4457957332538195 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278465968125 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278767219409 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278767275047 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8366201777155065 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8366201785699697 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8404878890657705 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8404956437541341 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8915914116258503 : ℝ) / 288230376151711744)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8915914526526167 : ℝ) / 288230376151711744)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((704112381205501711 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z3_32 :
    physicalGlobalCellMatrixRate32 5 .Z 4 =
      releasedPhysicalGlobalCellR5Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 4 =
      1426159502165691926052864 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow34Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z4_32 : ℝ :=
  ((4275703950555565170497605911426053 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((800888365685165 : ℝ) / 72057594037927936)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3203553462840627 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450908927704577 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3451018630277597 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3451018632745127 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104040365123 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104043953453 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104048924617 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104048983611 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407106925598583 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407106925775065 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6901817967523265 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774937653766145 : ℝ) / 36028797018963968)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774937823481069 : ℝ) / 36028797018963968)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774943447126625 : ℝ) / 36028797018963968)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((124399095279701171 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z4_32 :
    physicalGlobalCellMatrixRate32 5 .Z 5 =
      releasedPhysicalGlobalCellR5Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 5 =
      547711755369937310318592 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow29Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z5_32 : ℝ :=
  ((2560753198939039355705358337487995 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2693569370029 : ℝ) / 17592186044416)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((1128993589224969 : ℝ) / 144115188075855872)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2257126850175503 : ℝ) / 288230376151711744)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2257987126179317 : ℝ) / 288230376151711744)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2758215031869959 : ℝ) / 18014398509481984)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2758215033500287 : ℝ) / 18014398509481984)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((4514253721237967 : ℝ) / 576460752303423488)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((5516430064377811 : ℝ) / 36028797018963968)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((6415046444443831 : ℝ) / 36028797018963968)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((102708028922471589 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z5_32 :
    physicalGlobalCellMatrixRate32 5 .Z 6 =
      releasedPhysicalGlobalCellR5Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 6 =
      57703644448354297970688 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow23Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5Z6_32 : ℝ :=
  ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_z6_32 :
    physicalGlobalCellMatrixRate32 5 .Z 7 =
      releasedPhysicalGlobalCellR5Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 7 =
      1909860208492140429312 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 5 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow16Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResYRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion5MatrixZ32 : ℝ :=
  ((119063430725774446241559582812614829 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2693569370029 : ℝ) / 17592186044416)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((65360951383523 : ℝ) / 36028797018963968)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((573409808244599 : ℝ) / 18014398509481984)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((573409845862639 : ℝ) / 18014398509481984)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((744955001779329 : ℝ) / 4503599627370496)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((800888365685165 : ℝ) / 72057594037927936)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1114489316101533 : ℝ) / 36028797018963968)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((1128993589224969 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146819616583631 : ℝ) / 36028797018963968)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((1146819690848451 : ℝ) / 36028797018963968)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((1399702056115187 : ℝ) / 9007199254740992)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418736794586183 : ℝ) / 144115188075855872)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1418736798630153 : ℝ) / 144115188075855872)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489910003808419 : ℝ) / 9007199254740992)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((1605902988946421 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((2091550444288173 : ℝ) / 1152921504606846976)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4915480667083219 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2257126850175503 : ℝ) / 288230376151711744)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2257987126179317 : ℝ) / 288230376151711744)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((2293639233683569 : ℝ) / 72057594037927936)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2758215031869959 : ℝ) / 18014398509481984)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((2758215033500287 : ℝ) / 18014398509481984)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837473589195869 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((2837473597234069 : ℝ) / 288230376151711744)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((2979820007357017 : ℝ) / 18014398509481984)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3203553462840627 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((3211838302947557 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3450908927704577 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3451018630277597 : ℝ) / 288230376151711744)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((3451018632745127 : ℝ) / 288230376151711744)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970474363237421 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970474668706215 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((3970475081645577 : ℝ) / 576460752303423488)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4457957332538195 : ℝ) / 144115188075855872)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4857025676707307 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((4514253721237967 : ℝ) / 576460752303423488)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278465968125 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278767219409 : ℝ) / 144115188075855872)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((4587278767275047 : ℝ) / 144115188075855872)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((5516430064377811 : ℝ) / 36028797018963968)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((5598810008976781 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947178511215 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947178691357 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947194305421 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((5674947195774197 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104040365123 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104043953453 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104048924617 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407104048983611 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407106925598583 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6407106925775065 : ℝ) / 576460752303423488)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((6415046444443831 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423611954702639 : ℝ) / 576460752303423488)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423676611965371 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((6901817967523265 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774937653766145 : ℝ) / 36028797018963968)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774937823481069 : ℝ) / 36028797018963968)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((7774943447126625 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896352048222485 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896352068886419 : ℝ) / 36028797018963968)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896354116754551 : ℝ) / 36028797018963968)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((7940950152574601 : ℝ) / 1152921504606846976)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8366201777155065 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8366201785699697 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8404878890657705 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8404956437541341 : ℝ) / 4611686018427387904)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8915914116258503 : ℝ) / 288230376151711744)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((8915914526526167 : ℝ) / 288230376151711744)
      + ((5452287495854623 : ℝ) / 6917529027641081856) * Real.negMulLog ((63170832970125995 : ℝ) / 288230376151711744)
      + ((4585873639452799 : ℝ) / 55340232221128654848) * Real.negMulLog ((102708028922471589 : ℝ) / 576460752303423488)
      + ((5441027436355127 : ℝ) / 6917529027641081856) * Real.negMulLog ((124399095279701171 : ℝ) / 576460752303423488)
      + ((4635645655705109 : ℝ) / 55340232221128654848) * Real.negMulLog ((190708481343258077 : ℝ) / 1152921504606846976)
      + ((7083810876636167 : ℝ) / 3458764513820540928) * Real.negMulLog ((704112381205501711 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region5_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 5 .Z =
      releasedPhysicalGlobalRegion5MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r5_z0_32]
  rw [physical_global_cell_r5_z1_32]
  rw [physical_global_cell_r5_z2_32]
  rw [physical_global_cell_r5_z3_32]
  rw [physical_global_cell_r5_z4_32]
  rw [physical_global_cell_r5_z5_32]
  rw [physical_global_cell_r5_z6_32]
  unfold releasedPhysicalGlobalRegion5MatrixZ32
  unfold releasedPhysicalGlobalCellR5Z0_32
  unfold releasedPhysicalGlobalCellR5Z1_32
  unfold releasedPhysicalGlobalCellR5Z2_32
  unfold releasedPhysicalGlobalCellR5Z3_32
  unfold releasedPhysicalGlobalCellR5Z4_32
  unfold releasedPhysicalGlobalCellR5Z5_32
  unfold releasedPhysicalGlobalCellR5Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

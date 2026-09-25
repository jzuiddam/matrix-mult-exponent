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

private theorem chunk4_reindex_physical_cell_r5_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR5X0_32 : ℝ :=
  ((1228878892511735 : ℝ) / 442721857769029238784) * Real.log (5 : ℝ)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x0_32 :
    physicalGlobalCellMatrixRate32 5 .X 9 =
      releasedPhysicalGlobalCellR5X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 9 =
      1932859370391577559040 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow42Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X1_32 : ℝ :=
  ((1313423828647892897894485005560813 : ℝ) / 7975367974709495237422842361682067456) * Real.log (5 : ℝ)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489182495062393 : ℝ) / 9007199254740992)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489182495129913 : ℝ) / 9007199254740992)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2789731015450075 : ℝ) / 18014398509481984)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2789731582457193 : ℝ) / 18014398509481984)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2978364990256289 : ℝ) / 18014398509481984)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343613179721395 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343613220638255 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343614942458081 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343614945578593 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((47653840982841959 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x1_32 :
    physicalGlobalCellMatrixRate32 5 .X 17 =
      releasedPhysicalGlobalCellR5X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 17 =
      59047796086470724288512 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow39Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X2_32 : ℝ :=
  ((729735007624879692302709022106967 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((492959687338629 : ℝ) / 2251799813685248)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((1607915949499367 : ℝ) / 144115188075855872)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((1607915949695849 : ℝ) / 144115188075855872)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462283147341 : ℝ) / 288230376151711744)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462309256079 : ℝ) / 288230376151711744)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462309367959 : ℝ) / 288230376151711744)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((3943677390174195 : ℝ) / 18014398509481984)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924563625013 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924563937579 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924564026253 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924618728431 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924618735253 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((6431657394668991 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((6431657400332527 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((7887354795087663 : ℝ) / 36028797018963968)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((126197680013379947 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x2_32 :
    physicalGlobalCellMatrixRate32 5 .X 24 =
      releasedPhysicalGlobalCellR5X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 24 =
      555779905950022876790784 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow35Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X3_32 : ℝ :=
  ((8813709639140336573818927890504535 : ℝ) / 1329227995784915872903807060280344576) * Real.log (5 : ℝ)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((148106513779105 : ℝ) / 4503599627370496)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((586145535916875 : ℝ) / 18014398509481984)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1006180606251759 : ℝ) / 576460752303423488)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172290901719375 : ℝ) / 36028797018963968)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1184852128433503 : ℝ) / 36028797018963968)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2012361212474161 : ℝ) / 1152921504606846976)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344581800627539 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344581802771983 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2369704223073353 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4169616784901485 : ℝ) / 2305843009213693952)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689163609141327 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164287708581 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164288886529 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164290280015 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4739408617202341 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8049444844690435 : ℝ) / 4611686018427387904)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8049444849990793 : ℝ) / 4611686018427387904)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8339086567464939 : ℝ) / 4611686018427387904)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2755739659854170771 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x3_32 :
    physicalGlobalCellMatrixRate32 5 .X 30 =
      releasedPhysicalGlobalCellR5X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 30 =
      1454742450343953102274560 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow30Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X4_32 : ℝ :=
  ((712823406249126400375740962993833 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((404174576640897 : ℝ) / 36028797018963968)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((844458519633057 : ℝ) / 72057594037927936)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616697298148661 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616698306631953 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616698306873247 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3233396613285179 : ℝ) / 288230376151711744)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3377922862618237 : ℝ) / 288230376151711744)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3888305293228955 : ℝ) / 18014398509481984)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3888305295757985 : ℝ) / 18014398509481984)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789192592081 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789195364815 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789222123281 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6755668157249851 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6755845724911119 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((7776620497653449 : ℝ) / 36028797018963968)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((124425928019403993 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x4_32 :
    physicalGlobalCellMatrixRate32 5 .X 35 =
      releasedPhysicalGlobalCellR5X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 35 =
      547795421357747793297408 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow24Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X5_32 : ℝ :=
  ((838748613189837750206256647537665 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((351134044080519 : ℝ) / 2251799813685248)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((702268085383319 : ℝ) / 4503599627370496)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056667575711 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056670180811 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056675490525 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632113194866029 : ℝ) / 576460752303423488)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618144685855163 : ℝ) / 36028797018963968)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618144715409537 : ℝ) / 36028797018963968)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((6198847146954245 : ℝ) / 36028797018963968)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((99189484096882549 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x5_32 :
    physicalGlobalCellMatrixRate32 5 .X 39 =
      releasedPhysicalGlobalCellR5X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 39 =
      56748282939992237408256 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow17Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR5X6_32 : ℝ :=
  ((1622231493871517 : ℝ) / 590295810358705651712) * Real.log (5 : ℝ)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r5_x6_32 :
    physicalGlobalCellMatrixRate32 5 .X 42 =
      releasedPhysicalGlobalCellR5X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 5 42 =
      1913662137282547286016 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 5 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r5_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow09Dist,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR5CertificateSplitData.r5ResZRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR5X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion5MatrixX32 : ℝ :=
  ((180238523347588675603386802390166513 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((148106513779105 : ℝ) / 4503599627370496)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((351134044080519 : ℝ) / 2251799813685248)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((404174576640897 : ℝ) / 36028797018963968)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((492959687338629 : ℝ) / 2251799813685248)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((586145535916875 : ℝ) / 18014398509481984)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((702268085383319 : ℝ) / 4503599627370496)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((844458519633057 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1006180606251759 : ℝ) / 576460752303423488)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172290901719375 : ℝ) / 36028797018963968)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((1184852128433503 : ℝ) / 36028797018963968)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489182495062393 : ℝ) / 9007199254740992)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((1489182495129913 : ℝ) / 9007199254740992)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((1607915949499367 : ℝ) / 144115188075855872)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((1607915949695849 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616697298148661 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616698306631953 : ℝ) / 144115188075855872)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((1616698306873247 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2012361212474161 : ℝ) / 1152921504606846976)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1228878892511735 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056667575711 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056670180811 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316056675490525 : ℝ) / 288230376151711744)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344581800627539 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344581802771983 : ℝ) / 72057594037927936)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2369704223073353 : ℝ) / 72057594037927936)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2789731015450075 : ℝ) / 18014398509481984)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2789731582457193 : ℝ) / 18014398509481984)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462283147341 : ℝ) / 288230376151711744)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462309256079 : ℝ) / 288230376151711744)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((2871462309367959 : ℝ) / 288230376151711744)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((2978364990256289 : ℝ) / 18014398509481984)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3233396613285179 : ℝ) / 288230376151711744)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3377922862618237 : ℝ) / 288230376151711744)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3888305293228955 : ℝ) / 18014398509481984)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((3888305295757985 : ℝ) / 18014398509481984)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((3943677390174195 : ℝ) / 18014398509481984)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4169616784901485 : ℝ) / 2305843009213693952)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1622231493871517 : ℝ) / 590295810358705651712) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632113194866029 : ℝ) / 576460752303423488)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689163609141327 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164287708581 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164288886529 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689164290280015 : ℝ) / 144115188075855872)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((4739408617202341 : ℝ) / 144115188075855872)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618144685855163 : ℝ) / 36028797018963968)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((5618144715409537 : ℝ) / 36028797018963968)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924563625013 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924563937579 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924564026253 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924618728431 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((5742924618735253 : ℝ) / 576460752303423488)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((6198847146954245 : ℝ) / 36028797018963968)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((6431657394668991 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((6431657400332527 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789192592081 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789195364815 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6466789222123281 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6755668157249851 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((6755845724911119 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((7776620497653449 : ℝ) / 36028797018963968)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((7887354795087663 : ℝ) / 36028797018963968)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8049444844690435 : ℝ) / 4611686018427387904)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8049444849990793 : ℝ) / 4611686018427387904)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((8339086567464939 : ℝ) / 4611686018427387904)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343613179721395 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343613220638255 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343614942458081 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((8343614945578593 : ℝ) / 1152921504606846976)
      + ((4692697214005051 : ℝ) / 55340232221128654848) * Real.negMulLog ((47653840982841959 : ℝ) / 288230376151711744)
      + ((4509948328335463 : ℝ) / 55340232221128654848) * Real.negMulLog ((99189484096882549 : ℝ) / 576460752303423488)
      + ((906976430544833 : ℝ) / 1152921504606846976) * Real.negMulLog ((124425928019403993 : ℝ) / 576460752303423488)
      + ((920196218540309 : ℝ) / 1152921504606846976) * Real.negMulLog ((126197680013379947 : ℝ) / 576460752303423488)
      + ((2408594638678685 : ℝ) / 1152921504606846976) * Real.negMulLog ((2755739659854170771 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region5_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 5 .X =
      releasedPhysicalGlobalRegion5MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r5_x0_32]
  rw [physical_global_cell_r5_x1_32]
  rw [physical_global_cell_r5_x2_32]
  rw [physical_global_cell_r5_x3_32]
  rw [physical_global_cell_r5_x4_32]
  rw [physical_global_cell_r5_x5_32]
  rw [physical_global_cell_r5_x6_32]
  unfold releasedPhysicalGlobalRegion5MatrixX32
  unfold releasedPhysicalGlobalCellR5X0_32
  unfold releasedPhysicalGlobalCellR5X1_32
  unfold releasedPhysicalGlobalCellR5X2_32
  unfold releasedPhysicalGlobalCellR5X3_32
  unfold releasedPhysicalGlobalCellR5X4_32
  unfold releasedPhysicalGlobalCellR5X5_32
  unfold releasedPhysicalGlobalCellR5X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

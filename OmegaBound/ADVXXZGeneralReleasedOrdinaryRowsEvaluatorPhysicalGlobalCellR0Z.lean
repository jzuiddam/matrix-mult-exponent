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

private theorem chunk4_reindex_physical_cell_r0_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR0Z0_32 : ℝ :=
  ((1221852444378077 : ℝ) / 442721857769029238784) * Real.log (5 : ℝ)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z0_32 :
    physicalGlobalCellMatrixRate32 0 .Z 1 =
      releasedPhysicalGlobalCellR0Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 1 =
      1921807723074279702528 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow01Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow01Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow01Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow01Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z1_32 : ℝ :=
  ((423590515389441643183665493266979 : ℝ) / 2658455991569831745807614120560689152) * Real.log (5 : ℝ)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((144725469602291 : ℝ) / 18014398509481984)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((351102201620837 : ℝ) / 2251799813685248)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315607513877397 : ℝ) / 288230376151711744)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((3100112473837749 : ℝ) / 18014398509481984)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631214995575397 : ℝ) / 576460752303423488)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631215028403383 : ℝ) / 576460752303423488)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635202598649 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635203757633 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635232451645 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((49601819612873765 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z1_32 :
    physicalGlobalCellMatrixRate32 0 .Z 2 =
      releasedPhysicalGlobalCellR0Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 2 =
      57318436617475634233344 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow02Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow02Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow02Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow02Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z2_32 : ℝ :=
  ((360302259284715887350626522685599 : ℝ) / 166153499473114484112975882535043072) * Real.log (5 : ℝ)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((100800407618365 : ℝ) / 9007199254740992)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((403201630520863 : ℝ) / 36028797018963968)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((1612806522031529 : ℝ) / 144115188075855872)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225613043934433 : ℝ) / 288230376151711744)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((3890666279351359 : ℝ) / 18014398509481984)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226500313001 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226500971709 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226501264281 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226510182415 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711396784875631 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711396787946527 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711416496088211 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711416496105513 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781332492365207 : ℝ) / 36028797018963968)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781333567454117 : ℝ) / 36028797018963968)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((62250668738709689 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z2_32 :
    physicalGlobalCellMatrixRate32 0 .Z 3 =
      releasedPhysicalGlobalCellR0Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 3 =
      553562450040524994772992 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow03Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow03Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow03Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow03Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z3_32 : ℝ :=
  ((8871918322103182941983227316457865 : ℝ) / 1329227995784915872903807060280344576) * Real.log (5 : ℝ)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((573721349559899 : ℝ) / 18014398509481984)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((1164351670105663 : ℝ) / 36028797018963968)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((2294885479004405 : ℝ) / 72057594037927936)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((3522279835075647 : ℝ) / 2305843009213693952)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770791321583 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770792694247 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770796252337 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770957477857 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770958386533 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770960665201 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406537406155 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406537681969 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406605469653 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559654309793 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559670224629 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559670327287 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7266304509921303 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7266349622674629 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((2797845737717260921 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z3_32 :
    physicalGlobalCellMatrixRate32 0 .Z 4 =
      releasedPhysicalGlobalCellR0Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 4 =
      1454754863806913584300032 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow04Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow04Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow04Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow04Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z4_32 : ℝ :=
  ((731499747722133280889671912781577 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((324758570805465 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((687715357492069 : ℝ) / 72057594037927936)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((1299034054785887 : ℝ) / 144115188075855872)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((2750833798204269 : ℝ) / 288230376151711744)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((2750861436623097 : ℝ) / 288230376151711744)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136216993563 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136217285915 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136217728485 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137132899169 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137132954883 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137134733283 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501667595290739 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013825435503723 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013825437711153 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013826976626213 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((128221232376457755 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z4_32 :
    physicalGlobalCellMatrixRate32 0 .Z 5 =
      releasedPhysicalGlobalCellR0Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 5 =
      551494995879816251572224 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow05Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow05Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow05Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow05Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z5_32 : ℝ :=
  ((1731757440439716313894923884153057 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((97130590550113 : ℝ) / 562949953421312)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((322214088458345 : ℝ) / 2251799813685248)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((777044724688049 : ℝ) / 4503599627370496)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3394661819470197 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3394661942687315 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3396699668435045 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((5159020218230195 : ℝ) / 36028797018963968)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216357798036021 : ℝ) / 36028797018963968)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((6793399423149543 : ℝ) / 1152921504606846976)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((198923449544548799 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z5_32 :
    physicalGlobalCellMatrixRate32 0 .Z 6 =
      releasedPhysicalGlobalCellR0Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 6 =
      58069111822151590084608 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow06Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow06Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow06Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow06Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0Z6_32 : ℝ :=
  ((2463428946431203 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_z6_32 :
    physicalGlobalCellMatrixRate32 0 .Z 7 =
      releasedPhysicalGlobalCellR0Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 7 =
      1937319353199783837696 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 0 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow07Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow07Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow07Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResYRow07Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion0MatrixZ32 : ℝ :=
  ((362783205929351940075556748461470655 : ℝ) / 31901471898837980949691369446728269824) * Real.log (5 : ℝ)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((97130590550113 : ℝ) / 562949953421312)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((100800407618365 : ℝ) / 9007199254740992)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((144725469602291 : ℝ) / 18014398509481984)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((322214088458345 : ℝ) / 2251799813685248)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((324758570805465 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((351102201620837 : ℝ) / 2251799813685248)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((403201630520863 : ℝ) / 36028797018963968)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((573721349559899 : ℝ) / 18014398509481984)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((687715357492069 : ℝ) / 72057594037927936)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((777044724688049 : ℝ) / 4503599627370496)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((1164351670105663 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((1299034054785887 : ℝ) / 144115188075855872)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((1612806522031529 : ℝ) / 144115188075855872)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((1221852444378077 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((2294885479004405 : ℝ) / 72057594037927936)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((2315607513877397 : ℝ) / 288230376151711744)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((2750833798204269 : ℝ) / 288230376151711744)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((2750861436623097 : ℝ) / 288230376151711744)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((3100112473837749 : ℝ) / 18014398509481984)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((3225613043934433 : ℝ) / 288230376151711744)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3394661819470197 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3394661942687315 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((3396699668435045 : ℝ) / 576460752303423488)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((3522279835075647 : ℝ) / 2305843009213693952)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((3890666279351359 : ℝ) / 18014398509481984)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((2463428946431203 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770791321583 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770792694247 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770796252337 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770957477857 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770958386533 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4589770960665201 : ℝ) / 144115188075855872)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631214995575397 : ℝ) / 576460752303423488)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((4631215028403383 : ℝ) / 576460752303423488)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406537406155 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406537681969 : ℝ) / 144115188075855872)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((4657406605469653 : ℝ) / 144115188075855872)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((5159020218230195 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136216993563 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136217285915 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196136217728485 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137132899169 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137132954883 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5196137134733283 : ℝ) / 576460752303423488)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((5501667595290739 : ℝ) / 576460752303423488)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635202598649 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635203757633 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((5617635232451645 : ℝ) / 36028797018963968)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((6216357798036021 : ℝ) / 36028797018963968)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226500313001 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226500971709 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226501264281 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6451226510182415 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711396784875631 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711396787946527 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711416496088211 : ℝ) / 576460752303423488)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((6711416496105513 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((6793399423149543 : ℝ) / 1152921504606846976)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559654309793 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559670224629 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7044559670327287 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7266304509921303 : ℝ) / 4611686018427387904)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((7266349622674629 : ℝ) / 4611686018427387904)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781332492365207 : ℝ) / 36028797018963968)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((7781333567454117 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013825435503723 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013825437711153 : ℝ) / 36028797018963968)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((8013826976626213 : ℝ) / 36028797018963968)
      + ((1518420023851279 : ℝ) / 18446744073709551616) * Real.negMulLog ((49601819612873765 : ℝ) / 288230376151711744)
      + ((916524810990567 : ℝ) / 1152921504606846976) * Real.negMulLog ((62250668738709689 : ℝ) / 288230376151711744)
      + ((2739305277068497 : ℝ) / 3458764513820540928) * Real.negMulLog ((128221232376457755 : ℝ) / 576460752303423488)
      + ((1538306125591903 : ℝ) / 18446744073709551616) * Real.negMulLog ((198923449544548799 : ℝ) / 1152921504606846976)
      + ((2408615191457857 : ℝ) / 1152921504606846976) * Real.negMulLog ((2797845737717260921 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region0_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 0 .Z =
      releasedPhysicalGlobalRegion0MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r0_z0_32]
  rw [physical_global_cell_r0_z1_32]
  rw [physical_global_cell_r0_z2_32]
  rw [physical_global_cell_r0_z3_32]
  rw [physical_global_cell_r0_z4_32]
  rw [physical_global_cell_r0_z5_32]
  rw [physical_global_cell_r0_z6_32]
  unfold releasedPhysicalGlobalRegion0MatrixZ32
  unfold releasedPhysicalGlobalCellR0Z0_32
  unfold releasedPhysicalGlobalCellR0Z1_32
  unfold releasedPhysicalGlobalCellR0Z2_32
  unfold releasedPhysicalGlobalCellR0Z3_32
  unfold releasedPhysicalGlobalCellR0Z4_32
  unfold releasedPhysicalGlobalCellR0Z5_32
  unfold releasedPhysicalGlobalCellR0Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

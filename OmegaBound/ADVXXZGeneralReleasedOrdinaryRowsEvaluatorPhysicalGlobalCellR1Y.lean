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

private theorem chunk4_reindex_physical_cell_r1_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR1Y0_32 : ℝ :=
  ((808636607214945 : ℝ) / 295147905179352825856) * Real.log (5 : ℝ)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y0_32 :
    physicalGlobalCellMatrixRate32 1 .Y 16 =
      releasedPhysicalGlobalCellR1Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 16 =
      1907813112855790878720 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow09Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y1_32 : ℝ :=
  ((838945654953330453266051759068095 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((579012359148137 : ℝ) / 72057594037927936)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((702423688353537 : ℝ) / 4503599627370496)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2316049385186651 : ℝ) / 288230376151711744)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2316049531411485 : ℝ) / 288230376151711744)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809694704799583 : ℝ) / 18014398509481984)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809694755475989 : ℝ) / 18014398509481984)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((3096640577220349 : ℝ) / 18014398509481984)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((4632099038482507 : ℝ) / 576460752303423488)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619389556140783 : ℝ) / 36028797018963968)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((99198930351184877 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y1_32 :
    physicalGlobalCellMatrixRate32 1 .Y 23 =
      releasedPhysicalGlobalCellR1Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 23 =
      56761608598078189731840 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow17Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y2_32 : ℝ :=
  ((712822657662849759265446718665687 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((202088586158287 : ℝ) / 18014398509481984)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((808354347047973 : ℝ) / 72057594037927936)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((972077009542719 : ℝ) / 4503599627370496)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1616708689103033 : ℝ) / 144115188075855872)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1688915550246241 : ℝ) / 144115188075855872)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1944154031432761 : ℝ) / 9007199254740992)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417376339639 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417378688159 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417387852511 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3377829744684883 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3888308043328915 : ℝ) / 18014398509481984)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466834757244239 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466834775223941 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755659485629041 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755662207705269 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((62212929095977267 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y2_32 :
    physicalGlobalCellMatrixRate32 1 .Y 29 =
      releasedPhysicalGlobalCellR1Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 29 =
      547794820999481338626048 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow24Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y3_32 : ℝ :=
  ((103285540601809702351078591183235 : ℝ) / 15576890575604482885591488987660288) * Real.log (5 : ℝ)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((251618889241401 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((586109771659917 : ℝ) / 18014398509481984)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((1172219543334405 : ℝ) / 36028797018963968)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((1184689331724593 : ℝ) / 36028797018963968)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((2344438740534007 : ℝ) / 72057594037927936)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((2369378726484607 : ℝ) / 72057594037927936)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4025902227909257 : ℝ) / 2305843009213693952)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877479670469 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877480344767 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877481004955 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688878173172209 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688878174276643 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4738757409160059 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4738757465030683 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8051804455754239 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8051804477201675 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8341295664807145 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8341435651512395 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((172242649788735887 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y3_32 :
    physicalGlobalCellMatrixRate32 1 .Y 34 =
      releasedPhysicalGlobalCellR1Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 34 =
      1454715151984408280432640 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow30Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y4_32 : ℝ :=
  ((34205482007785606576308641456257 : ℝ) / 15576890575604482885591488987660288) * Real.log (5 : ℝ)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((179381078842837 : ℝ) / 18014398509481984)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((717524315212395 : ℝ) / 72057594037927936)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((717524366336005 : ℝ) / 72057594037927936)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1435048630759949 : ℝ) / 144115188075855872)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1435048732673989 : ℝ) / 144115188075855872)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1608162057277973 : ℝ) / 144115188075855872)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((2870097465377195 : ℝ) / 288230376151711744)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((3216324116473851 : ℝ) / 288230376151711744)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((5740194523042591 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((5740194930556891 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((6432715772617069 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((6432715775150329 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887631371983775 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887631376852107 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887633188506043 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((15775266435334761 : ℝ) / 72057594037927936)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y4_32 :
    physicalGlobalCellMatrixRate32 1 .Y 38 =
      releasedPhysicalGlobalCellR1Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 38 =
      555753710927198067621888 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow35Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y5_32 : ℝ :=
  ((5254057687091693081047268921978201 : ℝ) / 31901471898837980949691369446728269824) * Real.log (5 : ℝ)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((697399910203667 : ℝ) / 4503599627370496)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((744600796903861 : ℝ) / 4503599627370496)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((4172691809968621 : ℝ) / 576460752303423488)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5579199310630377 : ℝ) / 36028797018963968)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5956806376076653 : ℝ) / 36028797018963968)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5956806376442801 : ℝ) / 36028797018963968)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383121653867 : ℝ) / 1152921504606846976)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383158263871 : ℝ) / 1152921504606846976)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383619325887 : ℝ) / 1152921504606846976)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((190617804047344349 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y5_32 :
    physicalGlobalCellMatrixRate32 1 .Y 41 =
      releasedPhysicalGlobalCellR1Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 41 =
      59052242194951902855168 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow39Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR1Y6_32 : ℝ :=
  ((308422605747451 : ℝ) / 110680464442257309696) * Real.log (5 : ℝ)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r1_y6_32 :
    physicalGlobalCellMatrixRate32 1 .Y 43 =
      releasedPhysicalGlobalCellR1Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 1 43 =
      1940427253465435078656 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 1 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r1_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow42Dist,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR1CertificateSplitData.r1ResXRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR1Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion1MatrixY32 : ℝ :=
  ((120158873477705025703378705495680721 : ℝ) / 10633823966279326983230456482242756608) * Real.log (5 : ℝ)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((179381078842837 : ℝ) / 18014398509481984)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((202088586158287 : ℝ) / 18014398509481984)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((251618889241401 : ℝ) / 144115188075855872)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((579012359148137 : ℝ) / 72057594037927936)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((586109771659917 : ℝ) / 18014398509481984)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((697399910203667 : ℝ) / 4503599627370496)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((702423688353537 : ℝ) / 4503599627370496)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((717524315212395 : ℝ) / 72057594037927936)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((717524366336005 : ℝ) / 72057594037927936)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((744600796903861 : ℝ) / 4503599627370496)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((808354347047973 : ℝ) / 72057594037927936)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((972077009542719 : ℝ) / 4503599627370496)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((1172219543334405 : ℝ) / 36028797018963968)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((1184689331724593 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1435048630759949 : ℝ) / 144115188075855872)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1435048732673989 : ℝ) / 144115188075855872)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((1608162057277973 : ℝ) / 144115188075855872)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1616708689103033 : ℝ) / 144115188075855872)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1688915550246241 : ℝ) / 144115188075855872)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((1944154031432761 : ℝ) / 9007199254740992)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((808636607214945 : ℝ) / 295147905179352825856) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2316049385186651 : ℝ) / 288230376151711744)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2316049531411485 : ℝ) / 288230376151711744)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((2344438740534007 : ℝ) / 72057594037927936)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((2369378726484607 : ℝ) / 72057594037927936)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809694704799583 : ℝ) / 18014398509481984)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((2809694755475989 : ℝ) / 18014398509481984)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((2870097465377195 : ℝ) / 288230376151711744)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((3096640577220349 : ℝ) / 18014398509481984)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((3216324116473851 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417376339639 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417378688159 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233417387852511 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3377829744684883 : ℝ) / 288230376151711744)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((3888308043328915 : ℝ) / 18014398509481984)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4025902227909257 : ℝ) / 2305843009213693952)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((4172691809968621 : ℝ) / 576460752303423488)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((308422605747451 : ℝ) / 110680464442257309696) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((4632099038482507 : ℝ) / 576460752303423488)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877479670469 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877480344767 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688877481004955 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688878173172209 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4688878174276643 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4738757409160059 : ℝ) / 144115188075855872)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((4738757465030683 : ℝ) / 144115188075855872)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5579199310630377 : ℝ) / 36028797018963968)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((5619389556140783 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((5740194523042591 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((5740194930556891 : ℝ) / 576460752303423488)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5956806376076653 : ℝ) / 36028797018963968)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((5956806376442801 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((6432715772617069 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((6432715775150329 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466834757244239 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466834775223941 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755659485629041 : ℝ) / 576460752303423488)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755662207705269 : ℝ) / 576460752303423488)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887631371983775 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887631376852107 : ℝ) / 36028797018963968)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((7887633188506043 : ℝ) / 36028797018963968)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8051804455754239 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8051804477201675 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8341295664807145 : ℝ) / 4611686018427387904)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((8341435651512395 : ℝ) / 4611686018427387904)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383121653867 : ℝ) / 1152921504606846976)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383158263871 : ℝ) / 1152921504606846976)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((8345383619325887 : ℝ) / 1152921504606846976)
      + ((345057317941883 : ℝ) / 432345564227567616) * Real.negMulLog ((15775266435334761 : ℝ) / 72057594037927936)
      + ((1813950873081821 : ℝ) / 2305843009213693952) * Real.negMulLog ((62212929095977267 : ℝ) / 288230376151711744)
      + ((1503669118830315 : ℝ) / 18446744073709551616) * Real.negMulLog ((99198930351184877 : ℝ) / 576460752303423488)
      + ((1806412080904355 : ℝ) / 864691128455135232) * Real.negMulLog ((172242649788735887 : ℝ) / 288230376151711744)
      + ((4693050558960589 : ℝ) / 55340232221128654848) * Real.negMulLog ((190617804047344349 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region1_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 1 .Y =
      releasedPhysicalGlobalRegion1MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r1_y0_32]
  rw [physical_global_cell_r1_y1_32]
  rw [physical_global_cell_r1_y2_32]
  rw [physical_global_cell_r1_y3_32]
  rw [physical_global_cell_r1_y4_32]
  rw [physical_global_cell_r1_y5_32]
  rw [physical_global_cell_r1_y6_32]
  unfold releasedPhysicalGlobalRegion1MatrixY32
  unfold releasedPhysicalGlobalCellR1Y0_32
  unfold releasedPhysicalGlobalCellR1Y1_32
  unfold releasedPhysicalGlobalCellR1Y2_32
  unfold releasedPhysicalGlobalCellR1Y3_32
  unfold releasedPhysicalGlobalCellR1Y4_32
  unfold releasedPhysicalGlobalCellR1Y5_32
  unfold releasedPhysicalGlobalCellR1Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

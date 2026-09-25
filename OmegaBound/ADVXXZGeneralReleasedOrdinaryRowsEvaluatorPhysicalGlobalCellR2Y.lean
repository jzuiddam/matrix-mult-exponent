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

private theorem chunk4_reindex_physical_cell_r2_y32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR2Y0_32 : ℝ :=
  ((2451111932559715 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y0_32 :
    physicalGlobalCellMatrixRate32 2 .Y 16 =
      releasedPhysicalGlobalCellR2Y0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 16 =
      1927632859346801786880 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 16) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow43Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow43Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow43Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow43Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y1_32 : ℝ :=
  ((2599883283903155250648368817087175 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((372472587951343 : ℝ) / 2251799813685248)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983930993948233 : ℝ) / 288230376151711744)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983931130366781 : ℝ) / 288230376151711744)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983931293391121 : ℝ) / 288230376151711744)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((3967861981060423 : ℝ) / 576460752303423488)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599292864833841 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599292949477053 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959561406860857 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959561407277405 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((95352982916220491 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y1_32 :
    physicalGlobalCellMatrixRate32 2 .Y 23 =
      releasedPhysicalGlobalCellR2Y1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 23 =
      58356630010843449262080 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 23) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow41Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow41Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow41Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow41Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y2_32 : ℝ :=
  ((1442184265135376101522353678956539 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((401473572046707 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((802947143934125 : ℝ) / 72057594037927936)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((1419215123253707 : ℝ) / 144115188075855872)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246491461 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246535769 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246599983 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269479977 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269547855 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269581329 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((5676860538948905 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423570790097345 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423570807943233 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118203786835 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118210577501 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118424181143 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((126337894855998453 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y2_32 :
    physicalGlobalCellMatrixRate32 2 .Y 29 =
      releasedPhysicalGlobalCellR2Y2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 29 =
      548809187971421869965312 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 29) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow38Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow38Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow38Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow38Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y3_32 : ℝ :=
  ((3266445086031266487148001685078125 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((557056879173919 : ℝ) / 18014398509481984)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((573452678976609 : ℝ) / 18014398509481984)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1046016869268379 : ℝ) / 576460752303423488)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1114113736147967 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1146905358084447 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1146905358330583 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((2293810469618223 : ℝ) / 72057594037927936)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4202331488846129 : ℝ) / 2305843009213693952)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4456454942899211 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939135703 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939476899 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939515005 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587621437931435 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134946048461 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134953762799 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134954651361 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8404758480468863 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8912910059388913 : ℝ) / 288230376151711744)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1408273397486782685 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y3_32 :
    physicalGlobalCellMatrixRate32 2 .Y 34 =
      releasedPhysicalGlobalCellR2Y3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 34 =
      1426135294865716543488000 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 34) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow34Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow34Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow34Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow34Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y4_32 : ℝ :=
  ((712646696442843325515691411887841 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((800328899813801 : ℝ) / 72057594037927936)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((862716460075115 : ℝ) / 72057594037927936)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315597274583 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315655465125 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315655476531 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3450860579967521 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3450865859993907 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3887756211885947 : ℝ) / 18014398509481984)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631198603689 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631198648083 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631311146949 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631312111601 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6901721163169211 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((7775512414222917 : ℝ) / 36028797018963968)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((7775512470844113 : ℝ) / 36028797018963968)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((124408199602854509 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y4_32 :
    physicalGlobalCellMatrixRate32 2 .Y 38 =
      releasedPhysicalGlobalCellR2Y4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 38 =
      547708821381808146874368 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 38) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow29Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow29Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow29Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow29Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y5_32 : ℝ :=
  ((320152156663301276839524211378039 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((344710094761753 : ℝ) / 2251799813685248)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((564472086066279 : ℝ) / 72057594037927936)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((1604800779419831 : ℝ) / 9007199254740992)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2257888466437709 : ℝ) / 288230376151711744)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680757228161 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680758732307 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680758788755 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((4515777208648423 : ℝ) / 576460752303423488)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((4515777209071163 : ℝ) / 576460752303423488)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((25676814332611291 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y5_32 :
    physicalGlobalCellMatrixRate32 2 .Y 41 =
      releasedPhysicalGlobalCellR2Y5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 41 =
      57714375485406704566272 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 41) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow23Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow23Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow23Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow23Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Y6_32 : ℝ :=
  ((1213184302523891 : ℝ) / 442721857769029238784) * Real.log (5 : ℝ)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_y6_32 :
    physicalGlobalCellMatrixRate32 2 .Y 43 =
      releasedPhysicalGlobalCellR2Y6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 43 =
      1908173914804937293824 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 2 (physicalShapeAt32 43) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow16Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_y32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow16Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow16Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResYRow16Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Y6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion2MatrixY32 : ℝ :=
  ((59531557320280767665117917560339613 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((344710094761753 : ℝ) / 2251799813685248)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((372472587951343 : ℝ) / 2251799813685248)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((401473572046707 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((557056879173919 : ℝ) / 18014398509481984)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((564472086066279 : ℝ) / 72057594037927936)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((573452678976609 : ℝ) / 18014398509481984)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((800328899813801 : ℝ) / 72057594037927936)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((802947143934125 : ℝ) / 72057594037927936)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((862716460075115 : ℝ) / 72057594037927936)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1046016869268379 : ℝ) / 576460752303423488)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1114113736147967 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1146905358084447 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1146905358330583 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((1419215123253707 : ℝ) / 144115188075855872)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((1604800779419831 : ℝ) / 9007199254740992)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983930993948233 : ℝ) / 288230376151711744)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983931130366781 : ℝ) / 288230376151711744)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((1983931293391121 : ℝ) / 288230376151711744)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2451111932559715 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2257888466437709 : ℝ) / 288230376151711744)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((2293810469618223 : ℝ) / 72057594037927936)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680757228161 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680758732307 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((2757680758788755 : ℝ) / 18014398509481984)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246491461 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246535769 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430246599983 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269479977 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269547855 : ℝ) / 288230376151711744)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((2838430269581329 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315597274583 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315655465125 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3201315655476531 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3450860579967521 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3450865859993907 : ℝ) / 288230376151711744)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((3887756211885947 : ℝ) / 18014398509481984)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((3967861981060423 : ℝ) / 576460752303423488)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4202331488846129 : ℝ) / 2305843009213693952)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4456454942899211 : ℝ) / 144115188075855872)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((1213184302523891 : ℝ) / 442721857769029238784) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((4515777208648423 : ℝ) / 576460752303423488)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((4515777209071163 : ℝ) / 576460752303423488)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939135703 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939476899 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587620939515005 : ℝ) / 144115188075855872)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((4587621437931435 : ℝ) / 144115188075855872)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599292864833841 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5599292949477053 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((5676860538948905 : ℝ) / 576460752303423488)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959561406860857 : ℝ) / 36028797018963968)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((5959561407277405 : ℝ) / 36028797018963968)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631198603689 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631198648083 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631311146949 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6402631312111601 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423570790097345 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((6423570807943233 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((6901721163169211 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((7775512414222917 : ℝ) / 36028797018963968)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((7775512470844113 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118203786835 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118210577501 : ℝ) / 36028797018963968)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((7896118424181143 : ℝ) / 36028797018963968)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134946048461 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134953762799 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8368134954651361 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8404758480468863 : ℝ) / 4611686018427387904)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((8912910059388913 : ℝ) / 288230376151711744)
      + ((2293363232827453 : ℝ) / 27670116110564327424) * Real.negMulLog ((25676814332611291 : ℝ) / 144115188075855872)
      + ((4637768269446965 : ℝ) / 55340232221128654848) * Real.negMulLog ((95352982916220491 : ℝ) / 576460752303423488)
      + ((906833048300293 : ℝ) / 1152921504606846976) * Real.negMulLog ((124408199602854509 : ℝ) / 576460752303423488)
      + ((5451929449751197 : ℝ) / 6917529027641081856) * Real.negMulLog ((126337894855998453 : ℝ) / 576460752303423488)
      + ((1770922659419125 : ℝ) / 864691128455135232) * Real.negMulLog ((1408273397486782685 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region2_matrix_y32 :
    physicalGlobalRegionalMatrixRate32 2 .Y =
      releasedPhysicalGlobalRegion2MatrixY32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r2_y0_32]
  rw [physical_global_cell_r2_y1_32]
  rw [physical_global_cell_r2_y2_32]
  rw [physical_global_cell_r2_y3_32]
  rw [physical_global_cell_r2_y4_32]
  rw [physical_global_cell_r2_y5_32]
  rw [physical_global_cell_r2_y6_32]
  unfold releasedPhysicalGlobalRegion2MatrixY32
  unfold releasedPhysicalGlobalCellR2Y0_32
  unfold releasedPhysicalGlobalCellR2Y1_32
  unfold releasedPhysicalGlobalCellR2Y2_32
  unfold releasedPhysicalGlobalCellR2Y3_32
  unfold releasedPhysicalGlobalCellR2Y4_32
  unfold releasedPhysicalGlobalCellR2Y5_32
  unfold releasedPhysicalGlobalCellR2Y6_32
  ring

end OmegaBound.ADVXXZGeneral
end

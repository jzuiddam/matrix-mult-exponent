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

private theorem chunk4_reindex_physical_cell_r4_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR4Z0_32 : ℝ :=
  ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z0_32 :
    physicalGlobalCellMatrixRate32 4 .Z 1 =
      releasedPhysicalGlobalCellR4Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 1 =
      1941451405465030361088 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow42Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z1_32 : ℝ :=
  ((656983677340820259591481393267673 : ℝ) / 3987683987354747618711421180841033728) * Real.log (5 : ℝ)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((93075749142495 : ℝ) / 562949953421312)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((1489211986223347 : ℝ) / 9007199254740992)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((1489211986293525 : ℝ) / 9007199254740992)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((2086556560081641 : ℝ) / 288230376151711744)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((2789531677593349 : ℝ) / 18014398509481984)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((4173113125725011 : ℝ) / 576460752303423488)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((5579063592336917 : ℝ) / 36028797018963968)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((8346226341914265 : ℝ) / 1152921504606846976)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((8346226343125817 : ℝ) / 1152921504606846976)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((47654783595821313 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z1_32 :
    physicalGlobalCellMatrixRate32 4 .Z 2 =
      releasedPhysicalGlobalCellR4Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 2 =
      59072782804061232562176 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow39Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z2_32 : ℝ :=
  ((4377600902002314589521635721114727 : ℝ) / 1993841993677373809355710590420516864) * Real.log (5 : ℝ)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((358758331243139 : ℝ) / 36028797018963968)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((717516662490321 : ℝ) / 72057594037927936)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((804080709823095 : ℝ) / 72057594037927936)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((804088903567189 : ℝ) / 72057594037927936)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((1971910273095839 : ℝ) / 9007199254740992)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((2870066650051069 : ℝ) / 288230376151711744)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((3943819664248189 : ℝ) / 18014398509481984)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910026277 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910082885 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910139281 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910268663 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740133299906735 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((6432645678597719 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((6432711216019951 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887639319708547 : ℝ) / 36028797018963968)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((126202257811932279 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z2_32 :
    physicalGlobalCellMatrixRate32 4 .Z 3 =
      releasedPhysicalGlobalCellR4Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 3 =
      555664401106961241735168 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow35Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z3_32 : ℝ :=
  ((3305007201049360362176880763696871 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((15740859308835 : ℝ) / 9007199254740992)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((31481718620649 : ℝ) / 18014398509481984)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((36633934087537 : ℝ) / 1125899906842624)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((586142868088821 : ℝ) / 18014398509481984)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172285890731363 : ℝ) / 36028797018963968)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172285890802161 : ℝ) / 36028797018963968)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344571452776897 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344571455933751 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2367862696192677 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2367862746236281 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4029659983111367 : ℝ) / 2305843009213693952)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4170827702168771 : ℝ) / 2305843009213693952)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689142912167847 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689143562999607 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4735725452151123 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4735725512530503 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((8059319966124167 : ℝ) / 4611686018427387904)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((8341521547740353 : ℝ) / 4611686018427387904)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((689043008193066825 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z3_32 :
    physicalGlobalCellMatrixRate32 4 .Z 4 =
      releasedPhysicalGlobalCellR4Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 4 =
      1454606388410154271899648 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow30Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z4_32 : ℝ :=
  ((1425881149404799698381117038485671 : ℝ) / 664613997892457936451903530140172288) * Real.log (5 : ℝ)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((486039988052081 : ℝ) / 2251799813685248)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((1688805633576855 : ℝ) / 144115188075855872)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((1944160064374359 : ℝ) / 9007199254740992)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430255502931 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430349577043 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430349693143 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430350160719 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3888319899553847 : ℝ) / 18014398509481984)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511064561 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511277739 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511429689 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860699830505 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755222531122425 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755230172746719 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755230186071545 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((124426244188690397 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z4_32 :
    physicalGlobalCellMatrixRate32 4 .Z 5 =
      releasedPhysicalGlobalCellR4Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 5 =
      547884371255213753892864 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow24Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z5_32 : ℝ :=
  ((629035954607137290581758752974171 : ℝ) / 3987683987354747618711421180841033728) * Real.log (5 : ℝ)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((579012020528331 : ℝ) / 72057594037927936)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((579012039764033 : ℝ) / 72057594037927936)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2316048093696233 : ℝ) / 288230376151711744)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695291281803 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695300767763 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695307823331 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((3096653854940293 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((4632096412927061 : ℝ) / 576460752303423488)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((5619390582088265 : ℝ) / 36028797018963968)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((99198445753330729 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z5_32 :
    physicalGlobalCellMatrixRate32 4 .Z 6 =
      releasedPhysicalGlobalCellR4Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 6 =
      56745975151685158305792 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow17Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR4Z6_32 : ℝ :=
  ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r4_z6_32 :
    physicalGlobalCellMatrixRate32 4 .Z 7 =
      releasedPhysicalGlobalCellR4Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 4 7 =
      1913219622928903176192 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 4 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r4_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow09Dist,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR4CertificateSplitData.r4ResZRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR4Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion4MatrixZ32 : ℝ :=
  ((11264660047195330498212036714505033 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((15740859308835 : ℝ) / 9007199254740992)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((31481718620649 : ℝ) / 18014398509481984)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((36633934087537 : ℝ) / 1125899906842624)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((93075749142495 : ℝ) / 562949953421312)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((358758331243139 : ℝ) / 36028797018963968)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((486039988052081 : ℝ) / 2251799813685248)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((579012020528331 : ℝ) / 72057594037927936)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((579012039764033 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((586142868088821 : ℝ) / 18014398509481984)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((717516662490321 : ℝ) / 72057594037927936)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((804080709823095 : ℝ) / 72057594037927936)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((804088903567189 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172285890731363 : ℝ) / 36028797018963968)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172285890802161 : ℝ) / 36028797018963968)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((1489211986223347 : ℝ) / 9007199254740992)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((1489211986293525 : ℝ) / 9007199254740992)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((1688805633576855 : ℝ) / 144115188075855872)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((1944160064374359 : ℝ) / 9007199254740992)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((1971910273095839 : ℝ) / 9007199254740992)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((2086556560081641 : ℝ) / 288230376151711744)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((4937366245180843 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2316048093696233 : ℝ) / 288230376151711744)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344571452776897 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344571455933751 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2367862696192677 : ℝ) / 72057594037927936)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((2367862746236281 : ℝ) / 72057594037927936)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((2789531677593349 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695291281803 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695300767763 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((2809695307823331 : ℝ) / 18014398509481984)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((2870066650051069 : ℝ) / 288230376151711744)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((3096653854940293 : ℝ) / 18014398509481984)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430255502931 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430349577043 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430349693143 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3233430350160719 : ℝ) / 288230376151711744)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((3888319899553847 : ℝ) / 18014398509481984)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((3943819664248189 : ℝ) / 18014398509481984)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4029659983111367 : ℝ) / 2305843009213693952)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4170827702168771 : ℝ) / 2305843009213693952)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((4173113125725011 : ℝ) / 576460752303423488)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4865569109417987 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((4632096412927061 : ℝ) / 576460752303423488)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689142912167847 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689143562999607 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4735725452151123 : ℝ) / 144115188075855872)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((4735725512530503 : ℝ) / 144115188075855872)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((5579063592336917 : ℝ) / 36028797018963968)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((5619390582088265 : ℝ) / 36028797018963968)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910026277 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910082885 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910139281 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740132910268663 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((5740133299906735 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((6432645678597719 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((6432711216019951 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511064561 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511277739 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860511429689 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6466860699830505 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755222531122425 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755230172746719 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((6755230186071545 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887639319708547 : ℝ) / 36028797018963968)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((8059319966124167 : ℝ) / 4611686018427387904)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((8341521547740353 : ℝ) / 4611686018427387904)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((8346226341914265 : ℝ) / 1152921504606846976)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((8346226343125817 : ℝ) / 1152921504606846976)
      + ((2347341489953249 : ℝ) / 27670116110564327424) * Real.negMulLog ((47654783595821313 : ℝ) / 288230376151711744)
      + ((1127441230449779 : ℝ) / 13835058055282163712) * Real.negMulLog ((99198445753330729 : ℝ) / 576460752303423488)
      + ((1814247407036403 : ℝ) / 2305843009213693952) * Real.negMulLog ((124426244188690397 : ℝ) / 576460752303423488)
      + ((5520029873718433 : ℝ) / 6917529027641081856) * Real.negMulLog ((126202257811932279 : ℝ) / 576460752303423488)
      + ((3612554044550047 : ℝ) / 1729382256910270464) * Real.negMulLog ((689043008193066825 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region4_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 4 .Z =
      releasedPhysicalGlobalRegion4MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r4_z0_32]
  rw [physical_global_cell_r4_z1_32]
  rw [physical_global_cell_r4_z2_32]
  rw [physical_global_cell_r4_z3_32]
  rw [physical_global_cell_r4_z4_32]
  rw [physical_global_cell_r4_z5_32]
  rw [physical_global_cell_r4_z6_32]
  unfold releasedPhysicalGlobalRegion4MatrixZ32
  unfold releasedPhysicalGlobalCellR4Z0_32
  unfold releasedPhysicalGlobalCellR4Z1_32
  unfold releasedPhysicalGlobalCellR4Z2_32
  unfold releasedPhysicalGlobalCellR4Z3_32
  unfold releasedPhysicalGlobalCellR4Z4_32
  unfold releasedPhysicalGlobalCellR4Z5_32
  unfold releasedPhysicalGlobalCellR4Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

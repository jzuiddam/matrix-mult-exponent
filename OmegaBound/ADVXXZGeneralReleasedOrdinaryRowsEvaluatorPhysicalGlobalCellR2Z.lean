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

private theorem chunk4_reindex_physical_cell_r2_z32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR2Z0_32 : ℝ :=
  ((152154256473269 : ℝ) / 55340232221128654848) * Real.log (5 : ℝ)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z0_32 :
    physicalGlobalCellMatrixRate32 2 .Z 1 =
      releasedPhysicalGlobalCellR2Z0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 1 =
      1914543619628574179328 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 1) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow09Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z1_32 : ℝ :=
  ((2515121647224100866646005066763171 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((144753772694461 : ℝ) / 18014398509481984)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((1158030180546391 : ℝ) / 144115188075855872)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316060362078547 : ℝ) / 288230376151711744)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632120663260769 : ℝ) / 576460752303423488)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970458115809 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970458783515 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970481918097 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970484126625 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((6199440675381309 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((99191108534391629 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z1_32 :
    physicalGlobalCellMatrixRate32 2 .Z 2 =
      releasedPhysicalGlobalCellR2Z1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 2 =
      56722932313119919177728 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 2) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow17Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z2_32 : ℝ :=
  ((133650933060179417475183707569475 : ℝ) / 62307562302417931542365955950641152) * Real.log (5 : ℝ)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((404173641544803 : ℝ) / 36028797018963968)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((808347282987797 : ℝ) / 72057594037927936)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694565994981 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694688485477 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694688545341 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1944152252149297 : ℝ) / 9007199254740992)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233389132162345 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377944762115265 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377944762639301 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377953530733589 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377953531380277 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3888303794392975 : ℝ) / 18014398509481984)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466778753181523 : ℝ) / 576460752303423488)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466778753874535 : ℝ) / 576460752303423488)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776607592594773 : ℝ) / 36028797018963968)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776609001121055 : ℝ) / 36028797018963968)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z2_32 :
    physicalGlobalCellMatrixRate32 2 .Z 3 =
      releasedPhysicalGlobalCellR2Z2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 3 =
      547781581440686789492736 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 3) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow24Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z3_32 : ℝ :=
  ((8813927666380609913266600520962923 : ℝ) / 1329227995784915872903807060280344576) * Real.log (5 : ℝ)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295602016331 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612938331 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612952839 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612963055 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2011912435625111 : ℝ) / 1152921504606846976)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2084562206779881 : ℝ) / 1152921504606846976)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2084563610733795 : ℝ) / 1152921504606846976)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344591204155411 : ℝ) / 72057594037927936)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2370037851886463 : ℝ) / 72057594037927936)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2370037857694523 : ℝ) / 72057594037927936)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182408267725 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182447975073 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182451922679 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4740075714526535 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4740075717027493 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649751934581 : ℝ) / 4611686018427387904)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649752025593 : ℝ) / 4611686018427387904)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649752069227 : ℝ) / 4611686018427387904)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2755658521577218619 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z3_32 :
    physicalGlobalCellMatrixRate32 2 .Z 4 =
      releasedPhysicalGlobalCellR2Z3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 4 =
      1454792777025373448699904 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 4) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow30Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z4_32 : ℝ :=
  ((1094603630629609847546490171999767 : ℝ) / 498460498419343452338927647605129216) * Real.log (5 : ℝ)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((718067750579881 : ℝ) / 72057594037927936)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((803969288837859 : ℝ) / 72057594037927936)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((1436135501175003 : ℝ) / 144115188075855872)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((1607925939233229 : ℝ) / 144115188075855872)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((2872271242477419 : ℝ) / 288230376151711744)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542004624401 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542004698335 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485029819 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485030151 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485045531 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((6431703755535497 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((6431754280701281 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887147675938313 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887147678234265 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887149093148179 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((126194387083696675 : ℝ) / 576460752303423488)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z4_32 :
    physicalGlobalCellMatrixRate32 2 .Z 5 =
      releasedPhysicalGlobalCellR2Z4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 5 =
      555789735919825597759488 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 5) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow35Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z5_32 : ℝ :=
  ((219009221482014338585009568963925 : ℝ) / 1329227995784915872903807060280344576) * Real.log (5 : ℝ)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((1489175748969433 : ℝ) / 9007199254740992)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2086107234470015 : ℝ) / 288230376151711744)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2978351497663215 : ℝ) / 18014398509481984)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2978351498531463 : ℝ) / 18014398509481984)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((4172214647740641 : ℝ) / 576460752303423488)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((5579465598264827 : ℝ) / 36028797018963968)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((5579465793746875 : ℝ) / 36028797018963968)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((8344428960097883 : ℝ) / 1152921504606846976)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((8344429295596367 : ℝ) / 1152921504606846976)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((23826811993608763 : ℝ) / 144115188075855872)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z5_32 :
    physicalGlobalCellMatrixRate32 2 .Z 6 =
      releasedPhysicalGlobalCellR2Z5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 6 =
      59076358574160583065600 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 6) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow39Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR2Z6_32 : ℝ :=
  ((2469450013223387 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r2_z6_32 :
    physicalGlobalCellMatrixRate32 2 .Z 7 =
      releasedPhysicalGlobalCellR2Z6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 2 7 =
      1942054512799294685184 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .Y 2 (physicalShapeAt32 7) =
      OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r2_z32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow42Dist,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZR2CertificateSplitData.r2ResXRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR2Z6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion2MatrixZ32 : ℝ :=
  ((180240660480342863877877671160994435 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((144753772694461 : ℝ) / 18014398509481984)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((404173641544803 : ℝ) / 36028797018963968)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((718067750579881 : ℝ) / 72057594037927936)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((803969288837859 : ℝ) / 72057594037927936)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((808347282987797 : ℝ) / 72057594037927936)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((1158030180546391 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295602016331 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612938331 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612952839 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((1172295612963055 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((1436135501175003 : ℝ) / 144115188075855872)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((1489175748969433 : ℝ) / 9007199254740992)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((1607925939233229 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694565994981 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694688485477 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616694688545341 : ℝ) / 144115188075855872)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((1944152252149297 : ℝ) / 9007199254740992)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2011912435625111 : ℝ) / 1152921504606846976)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2084562206779881 : ℝ) / 1152921504606846976)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2084563610733795 : ℝ) / 1152921504606846976)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2086107234470015 : ℝ) / 288230376151711744)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((152154256473269 : ℝ) / 55340232221128654848) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316060362078547 : ℝ) / 288230376151711744)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2344591204155411 : ℝ) / 72057594037927936)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2370037851886463 : ℝ) / 72057594037927936)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2370037857694523 : ℝ) / 72057594037927936)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((2872271242477419 : ℝ) / 288230376151711744)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2978351497663215 : ℝ) / 18014398509481984)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((2978351498531463 : ℝ) / 18014398509481984)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233389132162345 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377944762115265 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377944762639301 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377953530733589 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3377953531380277 : ℝ) / 288230376151711744)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((3888303794392975 : ℝ) / 18014398509481984)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((4172214647740641 : ℝ) / 576460752303423488)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((2469450013223387 : ℝ) / 885443715538058477568) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632120663260769 : ℝ) / 576460752303423488)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182408267725 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182447975073 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4689182451922679 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4740075714526535 : ℝ) / 144115188075855872)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((4740075717027493 : ℝ) / 144115188075855872)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((5579465598264827 : ℝ) / 36028797018963968)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((5579465793746875 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970458115809 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970458783515 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970481918097 : ℝ) / 36028797018963968)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970484126625 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542004624401 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542004698335 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485029819 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485030151 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((5744542485045531 : ℝ) / 576460752303423488)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((6199440675381309 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((6431703755535497 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((6431754280701281 : ℝ) / 576460752303423488)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466778753181523 : ℝ) / 576460752303423488)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466778753874535 : ℝ) / 576460752303423488)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776607592594773 : ℝ) / 36028797018963968)
      + ((5441721096045641 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776609001121055 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887147675938313 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887147678234265 : ℝ) / 36028797018963968)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((7887149093148179 : ℝ) / 36028797018963968)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649751934581 : ℝ) / 4611686018427387904)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649752025593 : ℝ) / 4611686018427387904)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((8047649752069227 : ℝ) / 4611686018427387904)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((8344428960097883 : ℝ) / 1152921504606846976)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((8344429295596367 : ℝ) / 1152921504606846976)
      + ((1564989052193975 : ℝ) / 18446744073709551616) * Real.negMulLog ((23826811993608763 : ℝ) / 144115188075855872)
      + ((4507933641522719 : ℝ) / 55340232221128654848) * Real.negMulLog ((99191108534391629 : ℝ) / 576460752303423488)
      + ((1380318740804557 : ℝ) / 1729382256910270464) * Real.negMulLog ((126194387083696675 : ℝ) / 576460752303423488)
      + ((2408677963788929 : ℝ) / 1152921504606846976) * Real.negMulLog ((2755658521577218619 : ℝ) / 4611686018427387904)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region2_matrix_z32 :
    physicalGlobalRegionalMatrixRate32 2 .Z =
      releasedPhysicalGlobalRegion2MatrixZ32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r2_z0_32]
  rw [physical_global_cell_r2_z1_32]
  rw [physical_global_cell_r2_z2_32]
  rw [physical_global_cell_r2_z3_32]
  rw [physical_global_cell_r2_z4_32]
  rw [physical_global_cell_r2_z5_32]
  rw [physical_global_cell_r2_z6_32]
  unfold releasedPhysicalGlobalRegion2MatrixZ32
  unfold releasedPhysicalGlobalCellR2Z0_32
  unfold releasedPhysicalGlobalCellR2Z1_32
  unfold releasedPhysicalGlobalCellR2Z2_32
  unfold releasedPhysicalGlobalCellR2Z3_32
  unfold releasedPhysicalGlobalCellR2Z4_32
  unfold releasedPhysicalGlobalCellR2Z5_32
  unfold releasedPhysicalGlobalCellR2Z6_32
  ring

end OmegaBound.ADVXXZGeneral
end

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

private theorem chunk4_reindex_physical_cell_r0_x32 (f : Chunk 4 → ℝ) :
    ∑ sigma : Chunk 4, f sigma =
      ∑ i : Fin 81,
        f (OmegaBound.ADVXXZT6DenominatorData.wordOfId4 i) :=
  (Equiv.sum_comp OmegaBound.ADVXXZT6DenominatorData.wordEquiv4.symm f).symm

private noncomputable def releasedPhysicalGlobalCellR0X0_32 : ℝ :=
  ((2427599316902791 : ℝ) / 885443715538058477568) * Real.log (5 : ℝ)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x0_32 :
    physicalGlobalCellMatrixRate32 0 .X 9 =
      releasedPhysicalGlobalCellR0X0_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 9 =
      1909141785990495731712 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 9) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow09Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow09Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow09Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow09Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X0_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X1_32 : ℝ :=
  ((1258432942090640491238678792595473 : ℝ) / 7975367974709495237422842361682067456) * Real.log (5 : ℝ)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((9047081230775 : ℝ) / 1125899906842624)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316052768530671 : ℝ) / 288230376151711744)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((2808985259799957 : ℝ) / 18014398509481984)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((3099721498523115 : ℝ) / 18014398509481984)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632105584691125 : ℝ) / 576460752303423488)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632105585213243 : ℝ) / 576460752303423488)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970519582177 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970534985977 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970555267755 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((49595563991294065 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x1_32 :
    physicalGlobalCellMatrixRate32 0 .X 17 =
      releasedPhysicalGlobalCellR0X1_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 17 =
      56762263509801614966784 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 17) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow17Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow17Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow17Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow17Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X1_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X2_32 : ℝ :=
  ((8353319366148733546765865025983 : ℝ) / 3894222643901120721397872246915072) * Real.log (5 : ℝ)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((404168869433751 : ℝ) / 36028797018963968)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((486036106541847 : ℝ) / 2251799813685248)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616675582001895 : ℝ) / 144115188075855872)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616675582150841 : ℝ) / 144115188075855872)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1944144161903855 : ℝ) / 9007199254740992)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233350955477769 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233351163396761 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233351164038469 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466701910364443 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466701910939395 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756540336193043 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756540338404053 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756557491898967 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756557491924197 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776576709989497 : ℝ) / 36028797018963968)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776577668370683 : ℝ) / 36028797018963968)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x2_32 :
    physicalGlobalCellMatrixRate32 0 .X 24 =
      releasedPhysicalGlobalCellR0X2_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 24 =
      547791891237426551586816 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 24) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow24Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow24Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow24Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow24Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X2_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X3_32 : ℝ :=
  ((6610104161937546307723768233282277 : ℝ) / 996920996838686904677855295210258432) * Real.log (5 : ℝ)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((296012330995259 : ℝ) / 9007199254740992)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1007117214678227 : ℝ) / 576460752303423488)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172317571667813 : ℝ) / 36028797018963968)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172317597135181 : ℝ) / 36028797018963968)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344635142649583 : ℝ) / 72057594037927936)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368098646588087 : ℝ) / 72057594037927936)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368098711016347 : ℝ) / 72057594037927936)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4028468853800613 : ℝ) / 2305843009213693952)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270282849161 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270286334489 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270389272691 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270389296857 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270443074203 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736197347612821 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056937717453713 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056937717515571 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8338961121158677 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8338978853459531 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1378046930035036669 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x3_32 :
    physicalGlobalCellMatrixRate32 0 .X 30 =
      releasedPhysicalGlobalCellR0X3_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 30 =
      1454638743134746007568384 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 30) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow30Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow30Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow30Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow30Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X3_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X4_32 : ℝ :=
  ((729747629497473831869654039380727 : ℝ) / 332306998946228968225951765070086144) * Real.log (5 : ℝ)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((1434989627042209 : ℝ) / 144115188075855872)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869978951347517 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869979253955451 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869979253995533 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((3215857328277245 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((3215884973921445 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902595841 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902596537 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902635013 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739958507922957 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((6431714651597519 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((6431769964659141 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887719782467555 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887719783084071 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887721386888105 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((63101771100608783 : ℝ) / 288230376151711744)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x4_32 :
    physicalGlobalCellMatrixRate32 0 .X 35 =
      releasedPhysicalGlobalCellR0X4_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 35 =
      555773116592863095816192 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 35) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow35Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow35Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow35Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow35Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X4_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X5_32 : ℝ :=
  ((875828860723036186731815548786161 : ℝ) / 5316911983139663491615228241121378304) * Real.log (5 : ℝ)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((43602671383921 : ℝ) / 281474976710656)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((4155300878369287 : ℝ) / 576460752303423488)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5581143409568111 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921556477767 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921556530727 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921557947611 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310601745424187 : ℝ) / 1152921504606846976)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310605278807095 : ℝ) / 1152921504606846976)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310605279304241 : ℝ) / 1152921504606846976)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((190621489981257551 : ℝ) / 1152921504606846976)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x5_32 :
    physicalGlobalCellMatrixRate32 0 .X 39 =
      releasedPhysicalGlobalCellR0X5_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 39 =
      59055193088361913909248 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 39) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow39Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow39Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow39Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow39Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X5_32 Real.negMulLog
  ring

private noncomputable def releasedPhysicalGlobalCellR0X6_32 : ℝ :=
  ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.log (5 : ℝ)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)

set_option maxHeartbeats 1000000 in
-- Normalize one released physical-global beta row only.
private theorem physical_global_cell_r0_x6_32 :
    physicalGlobalCellMatrixRate32 0 .X 42 =
      releasedPhysicalGlobalCellR0X6_32 := by
  unfold physicalGlobalCellMatrixRate32
  rw [physical_global_joint_index32]
  have ha : OmegaBound.ADVXXZG1.alphaIdx 0 42 =
      1941492531710704091136 := by decide +kernel
  rw [physical_global_region_num32, physical_global_region_den32, ha,
    physical_global_shape_den32]
  have hb : physicalGlobalSpec.beta .X 0 (physicalShapeAt32 42) =
      OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow42Dist := by rfl
  simp only [ordinaryAtomRate]
  rw [hb]
  simp only [physicalShapeAt32, OmegaBound.ADVXXZG1.rowShape, coord,
    if_true]
  unfold entropyNats
  simp_rw [chunk4_reindex_physical_cell_r0_x32]
  simp_rw [physical_one_count4_32]
  simp only [Fin.sum_univ_succ]
  simp only [RatDist.prob, OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow42Dist,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow42Num]
  norm_num [physicalOneCount4_32,
    OmegaBound.ADVXXZCertSemantic.chunkIndex,
    OmegaBound.ADVXXZRegionalCertificateSplitData.r0ResXRow42Num,
    OmegaBound.ADVXXZT6DenominatorData.wordOfId4]
  unfold releasedPhysicalGlobalCellR0X6_32 Real.negMulLog
  ring

noncomputable def releasedPhysicalGlobalRegion0MatrixX32 : ℝ :=
  ((180237305922113123948291303153188501 : ℝ) / 15950735949418990474845684723364134912) * Real.log (5 : ℝ)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((9047081230775 : ℝ) / 1125899906842624)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((43602671383921 : ℝ) / 281474976710656)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((281474976710655 : ℝ) / 1125899906842624)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((296012330995259 : ℝ) / 9007199254740992)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((404168869433751 : ℝ) / 36028797018963968)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((486036106541847 : ℝ) / 2251799813685248)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((562949953421313 : ℝ) / 2251799813685248)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((562949953421315 : ℝ) / 2251799813685248)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1007117214678227 : ℝ) / 576460752303423488)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172317571667813 : ℝ) / 36028797018963968)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1172317597135181 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((1434989627042209 : ℝ) / 144115188075855872)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616675582001895 : ℝ) / 144115188075855872)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1616675582150841 : ℝ) / 144115188075855872)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((1944144161903855 : ℝ) / 9007199254740992)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((2251799813685245 : ℝ) / 9007199254740992)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685249 : ℝ) / 9007199254740992)
      + ((2427599316902791 : ℝ) / 885443715538058477568) * Real.negMulLog ((2251799813685251 : ℝ) / 9007199254740992)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((2316052768530671 : ℝ) / 288230376151711744)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2344635142649583 : ℝ) / 72057594037927936)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368098646588087 : ℝ) / 72057594037927936)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((2368098711016347 : ℝ) / 72057594037927936)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((2808985259799957 : ℝ) / 18014398509481984)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869978951347517 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869979253955451 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((2869979253995533 : ℝ) / 288230376151711744)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((3099721498523115 : ℝ) / 18014398509481984)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((3215857328277245 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((3215884973921445 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233350955477769 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233351163396761 : ℝ) / 288230376151711744)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((3233351164038469 : ℝ) / 288230376151711744)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4028468853800613 : ℝ) / 2305843009213693952)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((4155300878369287 : ℝ) / 576460752303423488)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370481 : ℝ) / 18014398509481984)
      + ((4937470834632121 : ℝ) / 1770887431076116955136) * Real.negMulLog ((4503599627370493 : ℝ) / 18014398509481984)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632105584691125 : ℝ) / 576460752303423488)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((4632105585213243 : ℝ) / 576460752303423488)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270282849161 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270286334489 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270389272691 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270389296857 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4689270443074203 : ℝ) / 144115188075855872)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((4736197347612821 : ℝ) / 144115188075855872)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5581143409568111 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970519582177 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970534985977 : ℝ) / 36028797018963968)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((5617970555267755 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902595841 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902596537 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739957902635013 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((5739958507922957 : ℝ) / 576460752303423488)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921556477767 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921556530727 : ℝ) / 36028797018963968)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((5956921557947611 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((6431714651597519 : ℝ) / 576460752303423488)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((6431769964659141 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466701910364443 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6466701910939395 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756540336193043 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756540338404053 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756557491898967 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((6756557491924197 : ℝ) / 576460752303423488)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776576709989497 : ℝ) / 36028797018963968)
      + ((5441823514674371 : ℝ) / 6917529027641081856) * Real.negMulLog ((7776577668370683 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887719782467555 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887719783084071 : ℝ) / 36028797018963968)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((7887721386888105 : ℝ) / 36028797018963968)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056937717453713 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8056937717515571 : ℝ) / 4611686018427387904)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310601745424187 : ℝ) / 1152921504606846976)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310605278807095 : ℝ) / 1152921504606846976)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((8310605279304241 : ℝ) / 1152921504606846976)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8338961121158677 : ℝ) / 4611686018427387904)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((8338978853459531 : ℝ) / 4611686018427387904)
      + ((4511059404198457 : ℝ) / 55340232221128654848) * Real.negMulLog ((49595563991294065 : ℝ) / 288230376151711744)
      + ((5521109865038227 : ℝ) / 6917529027641081856) * Real.negMulLog ((63101771100608783 : ℝ) / 288230376151711744)
      + ((782214179149759 : ℝ) / 9223372036854775808) * Real.negMulLog ((190621489981257551 : ℝ) / 1152921504606846976)
      + ((3612634398377801 : ℝ) / 1729382256910270464) * Real.negMulLog ((1378046930035036669 : ℝ) / 2305843009213693952)

set_option maxHeartbeats 1000000 in
-- Assemble the seven active physical-global rows in this region and direction.
theorem physical_global_region0_matrix_x32 :
    physicalGlobalRegionalMatrixRate32 0 .X =
      releasedPhysicalGlobalRegion0MatrixX32 := by
  rw [physical_global_regional_support32]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    physicalGlobalBoundaryCell32, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_fin_one]
  rw [physical_global_cell_r0_x0_32]
  rw [physical_global_cell_r0_x1_32]
  rw [physical_global_cell_r0_x2_32]
  rw [physical_global_cell_r0_x3_32]
  rw [physical_global_cell_r0_x4_32]
  rw [physical_global_cell_r0_x5_32]
  rw [physical_global_cell_r0_x6_32]
  unfold releasedPhysicalGlobalRegion0MatrixX32
  unfold releasedPhysicalGlobalCellR0X0_32
  unfold releasedPhysicalGlobalCellR0X1_32
  unfold releasedPhysicalGlobalCellR0X2_32
  unfold releasedPhysicalGlobalCellR0X3_32
  unfold releasedPhysicalGlobalCellR0X4_32
  unfold releasedPhysicalGlobalCellR0X5_32
  unfold releasedPhysicalGlobalCellR0X6_32
  ring

end OmegaBound.ADVXXZGeneral
end

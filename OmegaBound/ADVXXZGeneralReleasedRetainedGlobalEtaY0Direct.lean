import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Data

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Exact normalization of the direct boundary summand expands 45 released rows over 81 words.
theorem released_global_eta_direct_weighted_nats_r0 :
    (1 : ℝ) / 6 * releasedGlobalEtaDirectRowsR0 = releasedGlobalEtaWeightedDirectNatsR0 := by
  classical
  unfold releasedGlobalEtaDirectRowsR0 releasedLogicalAlphaYZ releasedLogicalBetaYZ
    releasedGlobalEtaWeightedDirectNatsR0
  simp_rw [Entropy.H, released_chunk4_sum_y0]
  unfold RatDist.probR
  simp (config := { maxSteps := 10000000 }) only
    [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp (config := { maxSteps := 10000000 }) only [
    releasedLogicalAlphaYZ, releasedLogicalBetaYZ, RatDist.probR,
    releasedWordOfId4K,
    OmegaBound.ADVXXZG1.aw, OmegaBound.ADVXXZG1.alphaIdx,
    OmegaBound.ADVXXZG1.physRow, OmegaBound.ADVXXZG1.roleAt,
    OmegaBound.ADVXXZCertRegionalSemantic.shapeOffset, OmegaBound.ADVXXZG1.coordAt,
    OmegaBound.ADVXXZG1.rowLvl, OmegaBound.ADVXXZG1.rowShape,
    OmegaBound.ADVXXZG1.betaIdx,
    OmegaBound.ADVXXZCertRegionalSemantic.physicalSide,
    OmegaBound.ADVXXZCertSemantic.globalSpec,
    OmegaBound.ADVXXZCertSemantic.globalSpecs,
    OmegaBound.ADVXXZCertSemantic.globalSpecs00,
    OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeId,
    OmegaBound.ADVXXZRegionalCertificateSplitData.certificateSplitByIndex]
  simp_eta_y0_rows
  ring

end OmegaBound.ADVXXZGeneral


#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_direct_weighted_nats_r0

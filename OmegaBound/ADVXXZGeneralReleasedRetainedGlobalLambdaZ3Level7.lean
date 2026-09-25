import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Data

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Exact normalization of one released direct/level penalty summand.
theorem released_global_lambda_level7_weighted_nats_r3 :
    (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3 7 = releasedGlobalLambdaWeightedLevel7NatsR3 := by
  classical
  unfold releasedGlobalLambdaMixRowsR3 releasedLogicalAlphaYZ releasedLogicalBetaYZ
    releasedGlobalLambdaWeightedLevel7NatsR3
  simp_rw [Entropy.H, released_chunk4_sum_y0]
  unfold weightedSplit RatDist.probR
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
    OmegaBound.ADVXXZR3CertificateSplitData.certificateSplitByIndex]
  simp
  all_goals norm_lambda_z3_rows
  all_goals ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_lambda_level7_weighted_nats_r3

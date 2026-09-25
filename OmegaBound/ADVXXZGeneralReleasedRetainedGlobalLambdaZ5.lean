import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ5Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_lambda_weighted_nats_r5 :
    (1 : ℝ) / 6 * releasedGlobalLambdaRows 5 = releasedGlobalLambdaWeightedNatsR5 := by
  change (1 : ℝ) / 6 * (releasedGlobalLambdaDirectRowsR5 +
    ∑ a : Fin 9, releasedGlobalLambdaMixRowsR5 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ ((0 : Fin 8))) = releasedGlobalLambdaWeightedLevel1NatsR5 := by
    simpa using released_global_lambda_level1_weighted_nats_r5
  have h2 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalLambdaWeightedLevel2NatsR5 := by
    simpa using released_global_lambda_level2_weighted_nats_r5
  have h3 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalLambdaWeightedLevel3NatsR5 := by
    simpa using released_global_lambda_level3_weighted_nats_r5
  have h4 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalLambdaWeightedLevel4NatsR5 := by
    simpa using released_global_lambda_level4_weighted_nats_r5
  have h5 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalLambdaWeightedLevel5NatsR5 := by
    simpa using released_global_lambda_level5_weighted_nats_r5
  have h6 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalLambdaWeightedLevel6NatsR5 := by
    simpa using released_global_lambda_level6_weighted_nats_r5
  have h7 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalLambdaWeightedLevel7NatsR5 := by
    simpa using released_global_lambda_level7_weighted_nats_r5
  have h8 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalLambdaWeightedLevel8NatsR5 := by
    simpa using released_global_lambda_level8_weighted_nats_r5
  rw [released_global_lambda_direct_weighted_nats_r5,
    released_global_lambda_level0_weighted_nats_r5,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalLambdaWeightedNatsR5
  unfold releasedGlobalLambdaWeightedDirectNatsR5
    releasedGlobalLambdaWeightedLevel0NatsR5
    releasedGlobalLambdaWeightedLevel1NatsR5
    releasedGlobalLambdaWeightedLevel2NatsR5
    releasedGlobalLambdaWeightedLevel3NatsR5
    releasedGlobalLambdaWeightedLevel4NatsR5
    releasedGlobalLambdaWeightedLevel5NatsR5
    releasedGlobalLambdaWeightedLevel6NatsR5
    releasedGlobalLambdaWeightedLevel7NatsR5
    releasedGlobalLambdaWeightedLevel8NatsR5
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_lambda_weighted_nats_r5

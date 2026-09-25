import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ2Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_lambda_weighted_nats_r2 :
    (1 : ℝ) / 6 * releasedGlobalLambdaRows 2 = releasedGlobalLambdaWeightedNatsR2 := by
  change (1 : ℝ) / 6 * (releasedGlobalLambdaDirectRowsR2 +
    ∑ a : Fin 9, releasedGlobalLambdaMixRowsR2 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ ((0 : Fin 8))) = releasedGlobalLambdaWeightedLevel1NatsR2 := by
    simpa using released_global_lambda_level1_weighted_nats_r2
  have h2 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalLambdaWeightedLevel2NatsR2 := by
    simpa using released_global_lambda_level2_weighted_nats_r2
  have h3 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalLambdaWeightedLevel3NatsR2 := by
    simpa using released_global_lambda_level3_weighted_nats_r2
  have h4 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalLambdaWeightedLevel4NatsR2 := by
    simpa using released_global_lambda_level4_weighted_nats_r2
  have h5 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalLambdaWeightedLevel5NatsR2 := by
    simpa using released_global_lambda_level5_weighted_nats_r2
  have h6 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalLambdaWeightedLevel6NatsR2 := by
    simpa using released_global_lambda_level6_weighted_nats_r2
  have h7 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalLambdaWeightedLevel7NatsR2 := by
    simpa using released_global_lambda_level7_weighted_nats_r2
  have h8 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalLambdaWeightedLevel8NatsR2 := by
    simpa using released_global_lambda_level8_weighted_nats_r2
  rw [released_global_lambda_direct_weighted_nats_r2,
    released_global_lambda_level0_weighted_nats_r2,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalLambdaWeightedNatsR2
  unfold releasedGlobalLambdaWeightedDirectNatsR2
    releasedGlobalLambdaWeightedLevel0NatsR2
    releasedGlobalLambdaWeightedLevel1NatsR2
    releasedGlobalLambdaWeightedLevel2NatsR2
    releasedGlobalLambdaWeightedLevel3NatsR2
    releasedGlobalLambdaWeightedLevel4NatsR2
    releasedGlobalLambdaWeightedLevel5NatsR2
    releasedGlobalLambdaWeightedLevel6NatsR2
    releasedGlobalLambdaWeightedLevel7NatsR2
    releasedGlobalLambdaWeightedLevel8NatsR2
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_lambda_weighted_nats_r2

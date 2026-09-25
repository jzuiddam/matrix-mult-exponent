import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ3Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_lambda_weighted_nats_r3 :
    (1 : ℝ) / 6 * releasedGlobalLambdaRows 3 = releasedGlobalLambdaWeightedNatsR3 := by
  change (1 : ℝ) / 6 * (releasedGlobalLambdaDirectRowsR3 +
    ∑ a : Fin 9, releasedGlobalLambdaMixRowsR3 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ ((0 : Fin 8))) = releasedGlobalLambdaWeightedLevel1NatsR3 := by
    simpa using released_global_lambda_level1_weighted_nats_r3
  have h2 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalLambdaWeightedLevel2NatsR3 := by
    simpa using released_global_lambda_level2_weighted_nats_r3
  have h3 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalLambdaWeightedLevel3NatsR3 := by
    simpa using released_global_lambda_level3_weighted_nats_r3
  have h4 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalLambdaWeightedLevel4NatsR3 := by
    simpa using released_global_lambda_level4_weighted_nats_r3
  have h5 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalLambdaWeightedLevel5NatsR3 := by
    simpa using released_global_lambda_level5_weighted_nats_r3
  have h6 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalLambdaWeightedLevel6NatsR3 := by
    simpa using released_global_lambda_level6_weighted_nats_r3
  have h7 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalLambdaWeightedLevel7NatsR3 := by
    simpa using released_global_lambda_level7_weighted_nats_r3
  have h8 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalLambdaWeightedLevel8NatsR3 := by
    simpa using released_global_lambda_level8_weighted_nats_r3
  rw [released_global_lambda_direct_weighted_nats_r3,
    released_global_lambda_level0_weighted_nats_r3,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalLambdaWeightedNatsR3
  unfold releasedGlobalLambdaWeightedDirectNatsR3
    releasedGlobalLambdaWeightedLevel0NatsR3
    releasedGlobalLambdaWeightedLevel1NatsR3
    releasedGlobalLambdaWeightedLevel2NatsR3
    releasedGlobalLambdaWeightedLevel3NatsR3
    releasedGlobalLambdaWeightedLevel4NatsR3
    releasedGlobalLambdaWeightedLevel5NatsR3
    releasedGlobalLambdaWeightedLevel6NatsR3
    releasedGlobalLambdaWeightedLevel7NatsR3
    releasedGlobalLambdaWeightedLevel8NatsR3
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_lambda_weighted_nats_r3

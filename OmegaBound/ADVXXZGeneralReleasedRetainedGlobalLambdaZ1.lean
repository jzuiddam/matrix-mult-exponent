import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalLambdaZ1Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_lambda_weighted_nats_r1 :
    (1 : ℝ) / 6 * releasedGlobalLambdaRows 1 = releasedGlobalLambdaWeightedNatsR1 := by
  change (1 : ℝ) / 6 * (releasedGlobalLambdaDirectRowsR1 +
    ∑ a : Fin 9, releasedGlobalLambdaMixRowsR1 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ ((0 : Fin 8))) = releasedGlobalLambdaWeightedLevel1NatsR1 := by
    simpa using released_global_lambda_level1_weighted_nats_r1
  have h2 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalLambdaWeightedLevel2NatsR1 := by
    simpa using released_global_lambda_level2_weighted_nats_r1
  have h3 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalLambdaWeightedLevel3NatsR1 := by
    simpa using released_global_lambda_level3_weighted_nats_r1
  have h4 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalLambdaWeightedLevel4NatsR1 := by
    simpa using released_global_lambda_level4_weighted_nats_r1
  have h5 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalLambdaWeightedLevel5NatsR1 := by
    simpa using released_global_lambda_level5_weighted_nats_r1
  have h6 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalLambdaWeightedLevel6NatsR1 := by
    simpa using released_global_lambda_level6_weighted_nats_r1
  have h7 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalLambdaWeightedLevel7NatsR1 := by
    simpa using released_global_lambda_level7_weighted_nats_r1
  have h8 : (1 : ℝ) / 6 * releasedGlobalLambdaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalLambdaWeightedLevel8NatsR1 := by
    simpa using released_global_lambda_level8_weighted_nats_r1
  rw [released_global_lambda_direct_weighted_nats_r1,
    released_global_lambda_level0_weighted_nats_r1,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalLambdaWeightedNatsR1
  unfold releasedGlobalLambdaWeightedDirectNatsR1
    releasedGlobalLambdaWeightedLevel0NatsR1
    releasedGlobalLambdaWeightedLevel1NatsR1
    releasedGlobalLambdaWeightedLevel2NatsR1
    releasedGlobalLambdaWeightedLevel3NatsR1
    releasedGlobalLambdaWeightedLevel4NatsR1
    releasedGlobalLambdaWeightedLevel5NatsR1
    releasedGlobalLambdaWeightedLevel6NatsR1
    releasedGlobalLambdaWeightedLevel7NatsR1
    releasedGlobalLambdaWeightedLevel8NatsR1
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_lambda_weighted_nats_r1

import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY5Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_eta_weighted_nats_r5 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 5 = releasedGlobalEtaWeightedNatsR5 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR5 +
    ∑ a : Fin 9, releasedGlobalEtaMixRowsR5 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ ((0 : Fin 8))) = releasedGlobalEtaWeightedLevel1NatsR5 := by
    simpa using released_global_eta_level1_weighted_nats_r5
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalEtaWeightedLevel2NatsR5 := by
    simpa using released_global_eta_level2_weighted_nats_r5
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalEtaWeightedLevel3NatsR5 := by
    simpa using released_global_eta_level3_weighted_nats_r5
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalEtaWeightedLevel4NatsR5 := by
    simpa using released_global_eta_level4_weighted_nats_r5
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalEtaWeightedLevel5NatsR5 := by
    simpa using released_global_eta_level5_weighted_nats_r5
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalEtaWeightedLevel6NatsR5 := by
    simpa using released_global_eta_level6_weighted_nats_r5
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalEtaWeightedLevel7NatsR5 := by
    simpa using released_global_eta_level7_weighted_nats_r5
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR5
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalEtaWeightedLevel8NatsR5 := by
    simpa using released_global_eta_level8_weighted_nats_r5
  rw [released_global_eta_direct_weighted_nats_r5,
    released_global_eta_level0_weighted_nats_r5,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR5
  unfold releasedGlobalEtaWeightedDirectNatsR5
    releasedGlobalEtaWeightedLevel0NatsR5
    releasedGlobalEtaWeightedLevel1NatsR5
    releasedGlobalEtaWeightedLevel2NatsR5
    releasedGlobalEtaWeightedLevel3NatsR5
    releasedGlobalEtaWeightedLevel4NatsR5
    releasedGlobalEtaWeightedLevel5NatsR5
    releasedGlobalEtaWeightedLevel6NatsR5
    releasedGlobalEtaWeightedLevel7NatsR5
    releasedGlobalEtaWeightedLevel8NatsR5
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r5

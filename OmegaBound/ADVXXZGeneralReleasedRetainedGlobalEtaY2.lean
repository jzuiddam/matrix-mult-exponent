import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY2Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_eta_weighted_nats_r2 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 2 = releasedGlobalEtaWeightedNatsR2 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR2 +
    ∑ a : Fin 9, releasedGlobalEtaMixRowsR2 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ ((0 : Fin 8))) = releasedGlobalEtaWeightedLevel1NatsR2 := by
    simpa using released_global_eta_level1_weighted_nats_r2
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalEtaWeightedLevel2NatsR2 := by
    simpa using released_global_eta_level2_weighted_nats_r2
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalEtaWeightedLevel3NatsR2 := by
    simpa using released_global_eta_level3_weighted_nats_r2
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalEtaWeightedLevel4NatsR2 := by
    simpa using released_global_eta_level4_weighted_nats_r2
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalEtaWeightedLevel5NatsR2 := by
    simpa using released_global_eta_level5_weighted_nats_r2
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalEtaWeightedLevel6NatsR2 := by
    simpa using released_global_eta_level6_weighted_nats_r2
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalEtaWeightedLevel7NatsR2 := by
    simpa using released_global_eta_level7_weighted_nats_r2
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR2
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalEtaWeightedLevel8NatsR2 := by
    simpa using released_global_eta_level8_weighted_nats_r2
  rw [released_global_eta_direct_weighted_nats_r2,
    released_global_eta_level0_weighted_nats_r2,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR2
  unfold releasedGlobalEtaWeightedDirectNatsR2
    releasedGlobalEtaWeightedLevel0NatsR2
    releasedGlobalEtaWeightedLevel1NatsR2
    releasedGlobalEtaWeightedLevel2NatsR2
    releasedGlobalEtaWeightedLevel3NatsR2
    releasedGlobalEtaWeightedLevel4NatsR2
    releasedGlobalEtaWeightedLevel5NatsR2
    releasedGlobalEtaWeightedLevel6NatsR2
    releasedGlobalEtaWeightedLevel7NatsR2
    releasedGlobalEtaWeightedLevel8NatsR2
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r2

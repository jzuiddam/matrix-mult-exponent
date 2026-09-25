import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY1Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_eta_weighted_nats_r1 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 1 = releasedGlobalEtaWeightedNatsR1 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR1 +
    ∑ a : Fin 9, releasedGlobalEtaMixRowsR1 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ ((0 : Fin 8))) = releasedGlobalEtaWeightedLevel1NatsR1 := by
    simpa using released_global_eta_level1_weighted_nats_r1
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalEtaWeightedLevel2NatsR1 := by
    simpa using released_global_eta_level2_weighted_nats_r1
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalEtaWeightedLevel3NatsR1 := by
    simpa using released_global_eta_level3_weighted_nats_r1
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalEtaWeightedLevel4NatsR1 := by
    simpa using released_global_eta_level4_weighted_nats_r1
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalEtaWeightedLevel5NatsR1 := by
    simpa using released_global_eta_level5_weighted_nats_r1
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalEtaWeightedLevel6NatsR1 := by
    simpa using released_global_eta_level6_weighted_nats_r1
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalEtaWeightedLevel7NatsR1 := by
    simpa using released_global_eta_level7_weighted_nats_r1
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR1
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalEtaWeightedLevel8NatsR1 := by
    simpa using released_global_eta_level8_weighted_nats_r1
  rw [released_global_eta_direct_weighted_nats_r1,
    released_global_eta_level0_weighted_nats_r1,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR1
  unfold releasedGlobalEtaWeightedDirectNatsR1
    releasedGlobalEtaWeightedLevel0NatsR1
    releasedGlobalEtaWeightedLevel1NatsR1
    releasedGlobalEtaWeightedLevel2NatsR1
    releasedGlobalEtaWeightedLevel3NatsR1
    releasedGlobalEtaWeightedLevel4NatsR1
    releasedGlobalEtaWeightedLevel5NatsR1
    releasedGlobalEtaWeightedLevel6NatsR1
    releasedGlobalEtaWeightedLevel7NatsR1
    releasedGlobalEtaWeightedLevel8NatsR1
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r1

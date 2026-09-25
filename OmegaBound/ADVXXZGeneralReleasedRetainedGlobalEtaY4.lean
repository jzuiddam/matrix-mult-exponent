import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY4Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_eta_weighted_nats_r4 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 4 = releasedGlobalEtaWeightedNatsR4 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR4 +
    ∑ a : Fin 9, releasedGlobalEtaMixRowsR4 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ ((0 : Fin 8))) = releasedGlobalEtaWeightedLevel1NatsR4 := by
    simpa using released_global_eta_level1_weighted_nats_r4
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalEtaWeightedLevel2NatsR4 := by
    simpa using released_global_eta_level2_weighted_nats_r4
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalEtaWeightedLevel3NatsR4 := by
    simpa using released_global_eta_level3_weighted_nats_r4
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalEtaWeightedLevel4NatsR4 := by
    simpa using released_global_eta_level4_weighted_nats_r4
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalEtaWeightedLevel5NatsR4 := by
    simpa using released_global_eta_level5_weighted_nats_r4
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalEtaWeightedLevel6NatsR4 := by
    simpa using released_global_eta_level6_weighted_nats_r4
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalEtaWeightedLevel7NatsR4 := by
    simpa using released_global_eta_level7_weighted_nats_r4
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR4
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalEtaWeightedLevel8NatsR4 := by
    simpa using released_global_eta_level8_weighted_nats_r4
  rw [released_global_eta_direct_weighted_nats_r4,
    released_global_eta_level0_weighted_nats_r4,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR4
  unfold releasedGlobalEtaWeightedDirectNatsR4
    releasedGlobalEtaWeightedLevel0NatsR4
    releasedGlobalEtaWeightedLevel1NatsR4
    releasedGlobalEtaWeightedLevel2NatsR4
    releasedGlobalEtaWeightedLevel3NatsR4
    releasedGlobalEtaWeightedLevel4NatsR4
    releasedGlobalEtaWeightedLevel5NatsR4
    releasedGlobalEtaWeightedLevel6NatsR4
    releasedGlobalEtaWeightedLevel7NatsR4
    releasedGlobalEtaWeightedLevel8NatsR4
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r4

import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY3Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Join the direct and nine level-indexed exact penalty summands.
theorem released_global_eta_weighted_nats_r3 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 3 = releasedGlobalEtaWeightedNatsR3 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR3 +
    ∑ a : Fin 9, releasedGlobalEtaMixRowsR3 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ ((0 : Fin 8))) = releasedGlobalEtaWeightedLevel1NatsR3 := by
    simpa using released_global_eta_level1_weighted_nats_r3
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ ((0 : Fin 7)))) = releasedGlobalEtaWeightedLevel2NatsR3 := by
    simpa using released_global_eta_level2_weighted_nats_r3
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))) = releasedGlobalEtaWeightedLevel3NatsR3 := by
    simpa using released_global_eta_level3_weighted_nats_r3
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))) = releasedGlobalEtaWeightedLevel4NatsR3 := by
    simpa using released_global_eta_level4_weighted_nats_r3
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))) = releasedGlobalEtaWeightedLevel5NatsR3 := by
    simpa using released_global_eta_level5_weighted_nats_r3
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))) = releasedGlobalEtaWeightedLevel6NatsR3 := by
    simpa using released_global_eta_level6_weighted_nats_r3
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))) = releasedGlobalEtaWeightedLevel7NatsR3 := by
    simpa using released_global_eta_level7_weighted_nats_r3
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR3
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))) = releasedGlobalEtaWeightedLevel8NatsR3 := by
    simpa using released_global_eta_level8_weighted_nats_r3
  rw [released_global_eta_direct_weighted_nats_r3,
    released_global_eta_level0_weighted_nats_r3,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR3
  unfold releasedGlobalEtaWeightedDirectNatsR3
    releasedGlobalEtaWeightedLevel0NatsR3
    releasedGlobalEtaWeightedLevel1NatsR3
    releasedGlobalEtaWeightedLevel2NatsR3
    releasedGlobalEtaWeightedLevel3NatsR3
    releasedGlobalEtaWeightedLevel4NatsR3
    releasedGlobalEtaWeightedLevel5NatsR3
    releasedGlobalEtaWeightedLevel6NatsR3
    releasedGlobalEtaWeightedLevel7NatsR3
    releasedGlobalEtaWeightedLevel8NatsR3
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r3

import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Direct
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level0
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level1
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level2
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level3
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level4
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level5
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level6
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level7
import OmegaBound.ADVXXZGeneralReleasedRetainedGlobalEtaY0Level8

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- The join expands the nine-element finite sum before rewriting its certified summands.
theorem released_global_eta_weighted_nats_r0 :
    (1 : ℝ) / 6 * releasedGlobalEtaRows 0 =
      releasedGlobalEtaWeightedNatsR0 := by
  change (1 : ℝ) / 6 * (releasedGlobalEtaDirectRowsR0 +
    ∑ a : Fin (2 * 4 + 1), releasedGlobalEtaMixRowsR0 a) = _
  rw [mul_add, Finset.mul_sum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h1 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (0 : Fin 8)) = releasedGlobalEtaWeightedLevel1NatsR0 := by
    simpa using released_global_eta_level1_weighted_nats_r0
  have h2 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (0 : Fin 7))) = releasedGlobalEtaWeightedLevel2NatsR0 := by
    simpa using released_global_eta_level2_weighted_nats_r0
  have h3 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (0 : Fin 6)))) =
        releasedGlobalEtaWeightedLevel3NatsR0 := by
    simpa using released_global_eta_level3_weighted_nats_r0
  have h4 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 5))))) =
        releasedGlobalEtaWeightedLevel4NatsR0 := by
    simpa using released_global_eta_level4_weighted_nats_r0
  have h5 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 4)))))) =
        releasedGlobalEtaWeightedLevel5NatsR0 := by
    simpa using released_global_eta_level5_weighted_nats_r0
  have h6 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ
        (Fin.succ (0 : Fin 3))))))) = releasedGlobalEtaWeightedLevel6NatsR0 := by
    simpa using released_global_eta_level6_weighted_nats_r0
  have h7 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ
        (Fin.succ (Fin.succ (0 : Fin 2)))))))) =
          releasedGlobalEtaWeightedLevel7NatsR0 := by
    simpa using released_global_eta_level7_weighted_nats_r0
  have h8 : (1 : ℝ) / 6 * releasedGlobalEtaMixRowsR0
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ
        (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))))))) =
          releasedGlobalEtaWeightedLevel8NatsR0 := by
    simpa using released_global_eta_level8_weighted_nats_r0
  rw [released_global_eta_direct_weighted_nats_r0,
    released_global_eta_level0_weighted_nats_r0,
    h1, h2, h3, h4, h5, h6, h7, h8]
  unfold releasedGlobalEtaWeightedNatsR0
  unfold releasedGlobalEtaWeightedDirectNatsR0 releasedGlobalEtaWeightedLevel0NatsR0
    releasedGlobalEtaWeightedLevel1NatsR0 releasedGlobalEtaWeightedLevel2NatsR0
    releasedGlobalEtaWeightedLevel3NatsR0 releasedGlobalEtaWeightedLevel4NatsR0
    releasedGlobalEtaWeightedLevel5NatsR0 releasedGlobalEtaWeightedLevel6NatsR0
    releasedGlobalEtaWeightedLevel7NatsR0 releasedGlobalEtaWeightedLevel8NatsR0
  ring

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.released_global_eta_weighted_nats_r0

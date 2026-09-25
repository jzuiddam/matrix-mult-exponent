import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalGlobal
import OmegaBound.ADVXXZGeneralReleasedOrdinaryIntegralHelpers
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR0
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR1
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR2
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR3
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR4
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalDenR5
import OmegaBound.ADVXXZT9R2ScaleAlignment

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

theorem physical_global_A_den : physicalGlobalSpec.A.den = ordinaryD := by
  rfl

theorem physical_global_joint_den : physicalGlobalSpec.joint.den = ordinaryD ^ 2 := by
  exact OmegaBound.ADVXXZT9R2ScaleAlignment.logical_joint_den_eq_certDen_sq

theorem physical_global_beta_den_dvd_pow247
    (W : Side) (r : Fin 6) (u : Shape 4) :
    (physicalGlobalSpec.beta W r u).den ∣ 2 ^ 247 := by
  fin_cases r
  · exact physical_global_beta_den_dvd_pow247_r0 W u
  · exact physical_global_beta_den_dvd_pow247_r1 W u
  · exact physical_global_beta_den_dvd_pow247_r2 W u
  · exact physical_global_beta_den_dvd_pow247_r3 W u
  · exact physical_global_beta_den_dvd_pow247_r4 W u
  · exact physical_global_beta_den_dvd_pow247_r5 W u

theorem released_ordinary_physical_global_integral :
    GlobalIntegral physicalGlobalSpec
      (releasedOrdinaryCertificatePhysical.D ^ 4) := by
  refine ⟨by decide +kernel, ?_⟩
  intro r
  refine ⟨?_, ?_⟩
  · simpa using integral_nat_mul_prob
      (releasedOrdinaryCertificatePhysical.D ^ 4) 1 physicalGlobalSpec.A r
      (show physicalGlobalSpec.A.den ∣
          releasedOrdinaryCertificatePhysical.D ^ 4 by
        rw [physical_global_A_den]
        change ordinaryD ∣ (ordinaryD ^ 2) ^ 4
        refine ⟨ordinaryD ^ 7, ?_⟩
        ring)
  · intro u
    refine ⟨?_, ?_⟩
    · simpa using integral_nat_mul_prob
        (releasedOrdinaryCertificatePhysical.D ^ 4) 1 physicalGlobalSpec.joint (r, u)
        (show physicalGlobalSpec.joint.den ∣
            releasedOrdinaryCertificatePhysical.D ^ 4 by
          rw [physical_global_joint_den]
          change ordinaryD ^ 2 ∣ (ordinaryD ^ 2) ^ 4
          refine ⟨ordinaryD ^ 6, ?_⟩
          ring)
    · intro W sigma
      have hpow : 2 ^ 247 ∣ ordinaryD ^ 6 := by
        decide +kernel
      have hbeta : (physicalGlobalSpec.beta W r u).den ∣ ordinaryD ^ 6 :=
        dvd_trans (physical_global_beta_den_dvd_pow247 W r u) hpow
      have hdiv : physicalGlobalSpec.joint.den *
          (physicalGlobalSpec.beta W r u).den ∣
          releasedOrdinaryCertificatePhysical.D ^ 4 := by
        rw [physical_global_joint_den]
        change ordinaryD ^ 2 * (physicalGlobalSpec.beta W r u).den ∣
          (ordinaryD ^ 2) ^ 4
        obtain ⟨k, hk⟩ := hbeta
        refine ⟨k, ?_⟩
        calc
          (ordinaryD ^ 2) ^ 4 = ordinaryD ^ 2 * ordinaryD ^ 6 := by ring
          _ = ordinaryD ^ 2 *
              ((physicalGlobalSpec.beta W r u).den * k) := by rw [hk]
          _ = (ordinaryD ^ 2 * (physicalGlobalSpec.beta W r u).den) * k := by
            ring
      simpa using integral_nat_mul_two_probs
        (releasedOrdinaryCertificatePhysical.D ^ 4) 1 physicalGlobalSpec.joint (r, u)
        (physicalGlobalSpec.beta W r u) sigma hdiv

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralReleasedRetainedLegs

/-!
# The level-3 leg from the six regional closes (algebra only)

`cRate d * constituentBaseTotal p / D^2 = ∑ r, log 2 * constituentRegionRate d.toPaper r / D^2`
when the base total is nonzero, so the frozen `V17_I_Rows.10` body follows from the six regional
closes `R_{r+2} ≤ log 2 * constituentRegionRate releasedConstituentSpec.toPaper r / D^2`.
-/

open OmegaBound.ADVXXZPaper
open scoped BigOperators

namespace OmegaBound.ADVXXZGeneral

theorem level3_leg_of_regional_closes
    (h0 : OmegaBound.ADVXXZCert.R2 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 0 / (releasedCertificate.D ^ 2 : ℝ))
    (h1 : OmegaBound.ADVXXZCert.R3 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 1 / (releasedCertificate.D ^ 2 : ℝ))
    (h2 : OmegaBound.ADVXXZCert.R4 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 2 / (releasedCertificate.D ^ 2 : ℝ))
    (h3 : OmegaBound.ADVXXZCert.R5 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 3 / (releasedCertificate.D ^ 2 : ℝ))
    (h4 : OmegaBound.ADVXXZCert.R6 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 4 / (releasedCertificate.D ^ 2 : ℝ))
    (h5 : OmegaBound.ADVXXZCert.R7 ≤ Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 5 / (releasedCertificate.D ^ 2 : ℝ)) :
    S_released_level3_retained_leg := by
  unfold S_released_level3_retained_leg
  have hpos : 0 < constituentBaseTotal releasedParent := by
    unfold constituentBaseTotal
    let t : Fin 126 := ⟨0, releasedParent.terms_nonempty⟩
    exact lt_of_lt_of_le (releasedParent.baseN_pos t)
      (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
  have hbase : (constituentBaseTotal releasedParent : ℝ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hc : cRate releasedConstituentSpec * (constituentBaseTotal releasedParent : ℝ) /
      (releasedCertificate.D : ℝ) ^ 2 =
      ∑ r : Fin 6, Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper r /
        (releasedCertificate.D ^ 2 : ℝ) := by
    unfold cRate
    rw [← Finset.sum_div, ← Finset.mul_sum]
    field_simp
  rw [hc, Fin.sum_univ_six]
  linarith

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.level3_leg_of_regional_closes

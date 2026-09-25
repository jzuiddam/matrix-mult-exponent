import OmegaBound.ADVXXZGeneralRowsAggregateR4X30
import OmegaBound.ADVXXZGeneralRowsAggregateR4Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR4Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R6_le_constituentRegionRateR4_30 :
    OmegaBound.ADVXXZCert.R6 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 4 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R6_le_rowsR4XPaper30
  have hy := R6_le_rowsR4YPaper30
  have hz := R6_le_rowsR4ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R6 ≤
    Real.log 2 * min (paperRow30 4 .X) (min (paperRow30 4 .Y) (paperRow30 4 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R6_le_constituentRegionRateR4_30

import OmegaBound.ADVXXZGeneralRowsAggregateR5X30
import OmegaBound.ADVXXZGeneralRowsAggregateR5Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR5Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R7_le_constituentRegionRateR5_30 :
    OmegaBound.ADVXXZCert.R7 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 5 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R7_le_rowsR5XPaper30
  have hy := R7_le_rowsR5YPaper30
  have hz := R7_le_rowsR5ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R7 ≤
    Real.log 2 * min (paperRow30 5 .X) (min (paperRow30 5 .Y) (paperRow30 5 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R7_le_constituentRegionRateR5_30

import OmegaBound.ADVXXZGeneralRowsAggregateR0X30
import OmegaBound.ADVXXZGeneralRowsAggregateR0Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR0Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R2_le_constituentRegionRateR0_30 :
    OmegaBound.ADVXXZCert.R2 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 0 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R2_le_rowsR0XPaper30
  have hy := R2_le_rowsR0YPaper30
  have hz := R2_le_rowsR0ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R2 ≤
    Real.log 2 * min (paperRow30 0 .X) (min (paperRow30 0 .Y) (paperRow30 0 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R2_le_constituentRegionRateR0_30

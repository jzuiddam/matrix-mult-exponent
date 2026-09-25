import OmegaBound.ADVXXZGeneralRowsAggregateR1X30
import OmegaBound.ADVXXZGeneralRowsAggregateR1Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR1Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R3_le_constituentRegionRateR1_30 :
    OmegaBound.ADVXXZCert.R3 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 1 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R3_le_rowsR1XPaper30
  have hy := R3_le_rowsR1YPaper30
  have hz := R3_le_rowsR1ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R3 ≤
    Real.log 2 * min (paperRow30 1 .X) (min (paperRow30 1 .Y) (paperRow30 1 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R3_le_constituentRegionRateR1_30

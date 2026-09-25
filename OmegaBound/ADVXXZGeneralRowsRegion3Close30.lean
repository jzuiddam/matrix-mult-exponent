import OmegaBound.ADVXXZGeneralRowsAggregateR3X30
import OmegaBound.ADVXXZGeneralRowsAggregateR3Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR3Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R5_le_constituentRegionRateR3_30 :
    OmegaBound.ADVXXZCert.R5 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 3 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R5_le_rowsR3XPaper30
  have hy := R5_le_rowsR3YPaper30
  have hz := R5_le_rowsR3ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R5 ≤
    Real.log 2 * min (paperRow30 3 .X) (min (paperRow30 3 .Y) (paperRow30 3 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R5_le_constituentRegionRateR3_30

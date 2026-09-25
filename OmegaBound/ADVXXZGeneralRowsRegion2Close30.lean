import OmegaBound.ADVXXZGeneralRowsAggregateR2X30
import OmegaBound.ADVXXZGeneralRowsAggregateR2Y30
import OmegaBound.ADVXXZGeneralRowsAggregateR2Z30

open OmegaBound.ADVXXZPaper

namespace OmegaBound.ADVXXZGeneral

theorem R4_le_constituentRegionRateR2_30 :
    OmegaBound.ADVXXZCert.R4 ≤
      Real.log 2 * constituentRegionRate releasedConstituentSpec.toPaper 2 /
        (releasedCertificate.D ^ 2 : ℝ) := by
  have hx := R4_le_rowsR2XPaper30
  have hy := R4_le_rowsR2YPaper30
  have hz := R4_le_rowsR2ZPaper30
  unfold constituentRegionRate
  change OmegaBound.ADVXXZCert.R4 ≤
    Real.log 2 * min (paperRow30 2 .X) (min (paperRow30 2 .Y) (paperRow30 2 .Z)) /
      (releasedCertificate.D ^ 2 : ℝ)
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hD : 0 ≤ (releasedCertificate.D ^ 2 : ℝ) := sq_nonneg _
  rw [mul_min_of_nonneg _ _ hlog, mul_min_of_nonneg _ _ hlog]
  rw [← min_div_div_right hD, ← min_div_div_right hD]
  exact le_min hx (le_min hy hz)

end OmegaBound.ADVXXZGeneral

#print axioms OmegaBound.ADVXXZGeneral.R4_le_constituentRegionRateR2_30

import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalGlobal

open OmegaBound OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
namespace OmegaBound.ADVXXZGeneral

theorem physical_global_beta_den_dvd_pow247_r2 (W : Side) (u : Shape 4) :
    (physicalGlobalSpec.beta W 2 u).den ∣ 2 ^ 247 := by
  revert W u
  decide +kernel

end OmegaBound.ADVXXZGeneral

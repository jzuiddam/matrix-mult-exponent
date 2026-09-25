import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalIntegral
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalTopLink
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalNextLink
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalStage2
import OmegaBound.ADVXXZGeneralReleasedOrdinaryPhysicalStage3
import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage2Integral
import OmegaBound.ADVXXZGeneralReleasedOrdinaryStage3Integral

open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
set_library_suggestions Lean.LibrarySuggestions.empty
namespace OmegaBound.ADVXXZGeneral

set_option maxRecDepth 4000

private theorem released_ordinary_physical_stage_ok :
    ∀ (l : Stage releasedOrdinaryCertificatePhysical.top)
      (d : Step (wid (l.val - 1))),
      releasedOrdinaryCertificatePhysical.stage l = some d →
        ConstituentAdmissibleAt d.data
          (releasedOrdinaryCertificatePhysical.D ^ 2) := by
  intro l d hd
  rcases l with ⟨l, hlo, hhi⟩
  change 2 ≤ l at hlo
  change l ≤ 3 at hhi
  have hl : l = 2 ∨ l = 3 := by omega
  rcases hl with rfl | rfl
  · have hd' : some releasedOrdinaryStep2 = some d := by
      simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage] using hd
    have heq := Option.some.inj hd'
    subst d
    exact released_ordinary_physical_stage2_admissible
  · have hd' : some releasedOrdinaryStep3 = some d := by
      simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage] using hd
    have heq := Option.some.inj hd'
    subst d
    exact released_ordinary_physical_stage3_admissible

private theorem released_ordinary_physical_atomic_integral :
    AtomicIntegralAt releasedOrdinaryCertificatePhysical := by
  refine ⟨released_ordinary_physical_global_integral, ?_⟩
  intro l d hd
  rcases l with ⟨l, hlo, hhi⟩
  change 2 ≤ l at hlo
  change l ≤ 3 at hhi
  have hl : l = 2 ∨ l = 3 := by omega
  rcases hl with rfl | rfl
  · have hd' : some releasedOrdinaryStep2 = some d := by
      simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage] using hd
    have heq := Option.some.inj hd'
    subst d
    simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryCertificate] using
      released_ordinary_stage2_integral
  · have hd' : some releasedOrdinaryStep3 = some d := by
      simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryStage] using hd
    have heq := Option.some.inj hd'
    subst d
    simpa [releasedOrdinaryCertificatePhysical, releasedOrdinaryCertificate] using
      released_ordinary_stage3_integral

private theorem released_ordinary_physical_q_pos :
    0 < releasedOrdinaryCertificatePhysical.q := by
  change 0 < 5
  decide +kernel

private theorem released_ordinary_physical_top_pos :
    0 < releasedOrdinaryCertificatePhysical.top := by
  change 0 < 3
  decide +kernel

private theorem released_ordinary_physical_width_eq :
    releasedOrdinaryCertificatePhysical.width =
      wid releasedOrdinaryCertificatePhysical.top := by
  change 4 = wid 3
  decide +kernel

private theorem released_ordinary_physical_kappa_pos :
    0 < releasedOrdinaryCertificatePhysical.kappa := by
  change (0 : ℝ) < 1
  norm_num

private theorem released_ordinary_physical_D_pos :
    0 < releasedOrdinaryCertificatePhysical.D := by
  change 0 < ordinaryD ^ 2
  exact pow_pos (by
    change 0 < OmegaBound.ADVXXZT2.certDen
    decide +kernel) _

private theorem released_ordinary_physical_hash_floor :
    2 * releasedOrdinaryCertificatePhysical.width <
      releasedOrdinaryCertificatePhysical.modulus.floor := by
  change 2 * 4 < 11
  decide +kernel

theorem released_ordinary_physical_admissible :
    AdmissibleAt releasedOrdinaryCertificatePhysical where
  q_pos := released_ordinary_physical_q_pos
  top_pos := released_ordinary_physical_top_pos
  width_eq := released_ordinary_physical_width_eq
  kappa_pos := released_ordinary_physical_kappa_pos
  D_pos := released_ordinary_physical_D_pos
  global_ok := by
    change GlobalAdmissible physicalGlobalSpec
    exact physical_global_admissible
  stage_ok := released_ordinary_physical_stage_ok
  lattice := released_ordinary_physical_atomic_integral
  hash_floor := released_ordinary_physical_hash_floor
  top_link := released_ordinary_physical_top_link
  next_link := released_ordinary_physical_next_link

end OmegaBound.ADVXXZGeneral

import OmegaBound.ADVXXZGeneralGlobalExactTarget
import OmegaBound.ADVXXZGeneralGlobalPQFiniteQ

set_option autoImplicit false

section
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The finite P/Q estimates give the literal exponential compatibility bound for each
    represented exact-grid law. -/
theorem globalPcomp_entropy_bound27 {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (which : Fin 2)
    (beta : GlobalRepresentedLaw g (b * m) xi r which) :
    globalPcomp g (b * m) xi r which beta ≤
      Real.exp (GlobalBridge25.qExponent g (b * m) xi r which -
        GlobalBridge25.pExponent g (b * m) xi r which beta) *
        (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          Fintype.card (Chunk w) := by
  let P := globalPopulation g (b * m) xi r
  let A : ℝ := P.target.card
  let C : ℝ := Fintype.card (GlobalLawSample g (b * m) xi r which)
  let poly : ℝ := ((P.n : ℝ) + 1) ^ Fintype.card (Chunk w)
  let p := GlobalBridge25.pExponent g (b * m) xi r which beta
  let q := GlobalBridge25.qExponent g (b * m) xi r which
  let JP := globalJointP g (b * m) xi r which beta
  let JQ := globalJointQ g (b * m) xi r which beta
  have hquot := global_compatibility_quotient g hg hb m xi hxi r which beta
  have hfinite := global_PQ_finite_bounds g (b * m) xi hxi r which beta
  dsimp only at hfinite
  have hA : 0 < A := by
    unfold A P
    exact_mod_cast Finset.card_pos.mpr
      (Finset.nonempty_coe_sort.mp (globalTargetLabel_nonempty27 g xi r))
  have hC : 0 < C := by
    unfold C
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(globalFirstLawSample g (b * m) xi r which beta)⟩
  have hpoly : 0 < poly := by
    unfold poly P
    positivity
  have hep : 0 < Real.exp p := Real.exp_pos _
  have hfactor : 0 ≤ Real.exp (q - p) * poly := by positivity
  have hPlower : A * Real.exp p / poly / C ≤ JP := by
    rw [div_le_iff₀ hC]
    simpa only [A, C, poly, p, P, JP, mul_comm] using hfinite.2.2.2.1
  have hQupper : JQ ≤ A * Real.exp q / C := by
    rw [le_div_iff₀ hC]
    simpa only [A, C, q, JQ, P, mul_comm] using hfinite.2.2.2.2.2
  rw [hquot.2, div_le_iff₀ hquot.1]
  calc
    JQ ≤ A * Real.exp q / C := hQupper
    _ = (Real.exp (q - p) * poly) * (A * Real.exp p / poly / C) := by
      rw [Real.exp_sub]
      field_simp
    _ ≤ (Real.exp (q - p) * poly) * JP :=
      mul_le_mul_of_nonneg_left hPlower hfactor
    _ = _ := by rfl

private theorem representedLaw_eq27 {w n : ℕ} (g : GlobalSpec w)
    (xi : ExactGrid g n) (r : Fin 6) (which : Fin 2)
    (beta gamma : GlobalRepresentedLaw g n xi r which) : beta = gamma := by
  apply Subtype.ext
  funext sigma
  exact ((Finset.mem_filter.mp beta.property).2 sigma).trans
    ((Finset.mem_filter.mp gamma.property).2 sigma).symm

/-- Because the represented exact law is unique, the pointwise P/Q estimate controls the
    maximum compatibility ratio without an additional law-count factor. -/
theorem globalPcompMax_entropy_bound27 {w b : ℕ} (g : GlobalSpec w)
    (hg : GlobalAdmissible g) (hb : GlobalIntegral g b) (m : ℕ)
    (xi : ExactGrid g (b * m)) (hxi : GridBoundaryCompatible xi)
    (r : Fin 6) (which : Fin 2)
    (beta0 : GlobalRepresentedLaw g (b * m) xi r which) :
    globalPcompMax g (b * m) xi r which ≤
      Real.exp (GlobalBridge25.qExponent g (b * m) xi r which -
        GlobalBridge25.pExponent g (b * m) xi r which beta0) *
        (((globalPopulation g (b * m) xi r).n : ℝ) + 1) ^
          Fintype.card (Chunk w) := by
  classical
  unfold globalPcompMax
  let values := (Finset.univ : Finset (GlobalRepresentedLaw g (b * m) xi r which)).image
    (globalPcomp g (b * m) xi r which)
  have hvalues : values.Nonempty := by
    exact ⟨_, Finset.mem_image.mpr ⟨beta0, Finset.mem_univ _, rfl⟩⟩
  rw [dif_pos hvalues]
  obtain ⟨beta, _hbeta, hmax⟩ := Finset.mem_image.mp (Finset.max'_mem values hvalues)
  rw [← hmax]
  have heq : beta = beta0 := representedLaw_eq27 g xi r which beta beta0
  subst beta
  exact globalPcomp_entropy_bound27 g hg hb m xi hxi r which beta0

end
end OmegaBound.ADVXXZGeneral
end

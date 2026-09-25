import OmegaBound.ADVXXZGeneralCertComplete
import OmegaBound.ADVXXZCertRegionalSemanticBase
import OmegaBound.ADVXXZT3Dual
import OmegaBound.ADVXXZReAnchor
import OmegaBound.ADVXXZT6Round82RealDisintegration
import OmegaBound.ADVXXZT6Round78ReleasedComplement

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def releasedPerm (r : Fin 6) (W : Side) : Side :=
  OmegaBound.ADVXXZT3.paperSide
    (OmegaBound.ADVXXZCertRegionalSemantic.physicalSide r W)

private def regionOfPerm (σ : Side → Side) : Fin 6 :=
  match σ .X, σ .Y with
  | .X, .Y => 0
  | .X, .Z => 1
  | .Y, .X => 2
  | .Y, .Z => 3
  | .Z, .X => 4
  | .Z, .Y => 5
  | _, _ => 0

private theorem releasedPerm_injective : Function.Injective releasedPerm := by
  intro r s h
  have hX := congrFun h Side.X
  have hY := congrFun h Side.Y
  fin_cases r <;> fin_cases s <;>
    simp_all [releasedPerm, OmegaBound.ADVXXZT3.paperSide,
      OmegaBound.ADVXXZCertRegionalSemantic.physicalSide]

private theorem releasedPerm_regionOfPerm (σ : Side → Side)
    (hσ : Function.Bijective σ) : releasedPerm (regionOfPerm σ) = σ := by
  have hXY : σ .X ≠ σ .Y := by
    intro h
    have h' : (Side.X : Side) = .Y := hσ.1 h
    cases h'
  have hXZ : σ .X ≠ σ .Z := by
    intro h
    have h' : (Side.X : Side) = .Z := hσ.1 h
    cases h'
  have hYZ : σ .Y ≠ σ .Z := by
    intro h
    have h' : (Side.Y : Side) = .Z := hσ.1 h
    cases h'
  generalize hX : σ .X = x
  generalize hY : σ .Y = y
  generalize hZ : σ .Z = z
  fin_cases x <;> fin_cases y <;> fin_cases z
  all_goals
    apply funext
    intro W
    fin_cases W <;>
      simp_all [regionOfPerm, releasedPerm, OmegaBound.ADVXXZT3.paperSide,
        OmegaBound.ADVXXZCertRegionalSemantic.physicalSide]

set_option maxSynthPendingDepth 100 in
theorem releasedPerm_enumerates : EnumeratesPermutations releasedPerm := by
  refine ⟨?_, ?_⟩
  · intro r
    fin_cases r <;> decide +kernel
  · intro σ hσ
    refine ⟨regionOfPerm σ, releasedPerm_regionOfPerm σ hσ, ?_⟩
    intro r hr
    exact releasedPerm_injective (hr.trans (releasedPerm_regionOfPerm σ hσ).symm)

noncomputable def releasedGlobalSpec : GlobalSpec 4 where
  A := OmegaBound.ADVXXZCertificateGlobalData.Certificate.regionDist
  alpha := OmegaBound.ADVXXZCertificateGlobalData.Certificate.shapeDist
  beta := OmegaBound.ADVXXZRA.regionalBeta
  perm := releasedPerm
  joint := OmegaBound.ADVXXZCertificateGlobalData.certificateJoint

noncomputable def releasedParent : ConstituentInput 2 126 :=
  OmegaBound.ADVXXZT9R16PositiveParents.releasedPositiveInput

noncomputable def releasedConstituentSpec : ConstituentSpec releasedParent where
  A := OmegaBound.ADVXXZT6Round82.releasedRegionDist
  alpha := fun t r =>
    OmegaBound.ADVXXZCertificateGlobalData.RatDist.reindex
      (OmegaBound.ADVXXZT6Round78.childRowEquiv t)
      (OmegaBound.ADVXXZT6Round82.releasedChildRowDist t r)
  betaRegion := OmegaBound.ADVXXZT6Round82.certificateBetaRegion
  betaChild := OmegaBound.ADVXXZT6Round82.certificateBetaChild
  perm := releasedPerm
  outBase := OmegaBound.ADVXXZT6Round82.correctedOutBase

noncomputable def releasedStep3 : Step (wid (3 - 1)) where
  s := 126
  input := releasedParent
  data := releasedConstituentSpec

noncomputable def releasedStage (l : Stage 3) : Option (Step (wid (l.val - 1))) :=
  if h : l.val = 3 then by
    simpa [h] using (some releasedStep3)
  else none

noncomputable def releasedCertificate : Certificate where
  q := 5
  width := 4
  top := 3
  kappa := 1
  global := releasedGlobalSpec
  stage := releasedStage
  D := OmegaBound.ADVXXZT2.certDen
  modulus :=
    { floor := 11
      collisionPower := 3
      floor_ge := by decide +kernel
      collisionPower_ge := by decide +kernel }

noncomputable def releasedFirstChild : ChildShape releasedParent 0 := by
  change ChildShape OmegaBound.ADVXXZT9R16PositiveParents.releasedPositiveInput 0
  exact (OmegaBound.ADVXXZT6Round78.childRowEquiv 0).symm
    ⟨0, by decide +kernel⟩

end OmegaBound.ADVXXZGeneral
end

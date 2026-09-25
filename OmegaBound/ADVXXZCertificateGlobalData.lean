import OmegaBound.ADVXXZCertSemantic
import OmegaBound.ADVXXZPaperTheorems

/-!
# The ADVXXZ certificate as global-stage paper data

The semantic certificate stores the region simplex and the six shape simplexes as the first
seven `globalSpecs`.  This file reindexes those dependent `RatDist`s onto the paper's
`Fin 6` and `Shape 4` alphabets and packages them into `GlobalData 4`.

`certificateGlobalData` takes the `beta` field as an argument
(`ADVXXZCertificateSplitData.certificateGlobalData` supplies the certificate's own
complete-split family); `E` is defined to be the resulting exact `globalRegionRate`.
-/

open Finset

namespace OmegaBound.ADVXXZCertificateGlobalData

open ADVXXZ (RatDist SplitDist)
open ADVXXZPaper

namespace RatDist

/-- Transport an integral rational distribution along an equivalence of finite alphabets. -/
def reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (P : RatDist κ) : RatDist ι where
  num i := P.num (e i)
  den := P.den
  den_pos := P.den_pos
  sum_num := by
    rw [Equiv.sum_comp e]
    exact P.sum_num

@[simp] theorem reindex_probR {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (P : RatDist κ) (i : ι) :
    (reindex e P).probR i = P.probR (e i) := rfl

end RatDist

namespace Certificate

open ADVXXZCertSemantic

/-- The first semantic global distribution is the six-entry region distribution. -/
def regionId : GlobalDistId := ⟨0, by simp [globalSpecs, globalSpecs00]⟩

/-- Entries one through six are the 45-entry shape distributions for the six regions. -/
def shapeId (r : Fin 6) : GlobalDistId :=
  ⟨r.1 + 1, by simp [globalSpecs, globalSpecs00]; omega⟩

theorem region_length : (globalSpec regionId).nums.length = 6 := by
  decide

theorem shape_length (r : Fin 6) : (globalSpec (shapeId r)).nums.length = 45 := by
  fin_cases r <;> decide

def regionIndexEquiv : Fin 6 ≃ GlobalIndex regionId :=
  finCongr region_length.symm

def shapeIndexEquiv (r : Fin 6) : Fin 45 ≃ GlobalIndex (shapeId r) :=
  finCongr (shape_length r).symm

theorem shapeIndex_bijective : Function.Bijective
    (ADVXXZCertSemantic.shapeIndex : Shape 4 → Fin 45) := by
  decide

/-- The certificate ordering of the 45 level triples, as an equivalence. -/
noncomputable def paperShapeEquiv : Shape 4 ≃ Fin 45 :=
  Equiv.ofBijective ADVXXZCertSemantic.shapeIndex shapeIndex_bijective

/-- The certificate's six region weights, reindexed onto the paper alphabet. -/
def regionDist : RatDist (Fin 6) :=
  RatDist.reindex regionIndexEquiv (globalDist regionId)

/-- The certificate's shape simplex in region `r`, reindexed onto `Shape 4`. -/
noncomputable def shapeDist (r : Fin 6) : RatDist (Shape 4) :=
  RatDist.reindex (paperShapeEquiv.trans (shapeIndexEquiv r)) (globalDist (shapeId r))

end Certificate

open Certificate

/-- There are exactly six permutations of the three tensor sides. -/
theorem card_side_permutations : Fintype.card (Equiv.Perm Side) = 6 := by
  decide

/-- A canonical equivalence from the six regions to the six side permutations. -/
noncomputable def sidePermutationEquiv : Fin 6 ≃ Equiv.Perm Side :=
  (Fintype.equivFinOfCardEq card_side_permutations).symm

/-- A concrete enumeration of the six permutations of the three tensor sides. -/
noncomputable def certificatePerm (r : Fin 6) : Side → Side := sidePermutationEquiv r


/-- The common denominator of the six certificate shape distributions. -/
noncomputable def certificateShapeDen : ℕ := (shapeDist 0).den

theorem shapeDist_den (r : Fin 6) : (shapeDist r).den = certificateShapeDen := by
  fin_cases r <;> rfl

/-- The joint certificate distribution with exact integral weights `A r * alpha r u`. -/
noncomputable def certificateJoint : RatDist (Fin 6 × Shape 4) :=
  RatDist.pairWith regionDist shapeDist certificateShapeDen shapeDist_den

theorem certificateJoint_probR (r : Fin 6) (u : Shape 4) :
    certificateJoint.probR (r, u) = regionDist.probR r * (shapeDist r).probR u := by
  simp only [certificateJoint, RatDist.probR, RatDist.pairWith_num]
  change
    (↑(regionDist.num r * (shapeDist r).num u) : ℝ) /
        ↑(regionDist.den * certificateShapeDen) =
      (↑(regionDist.num r) : ℝ) / ↑regionDist.den *
        ((↑((shapeDist r).num u) : ℝ) / ↑(shapeDist r).den)
  rw [shapeDist_den r]
  push_cast
  ring

/-- Package the committed region and shape simplexes into global paper data.

`beta` is explicit; `ADVXXZCertificateSplitData.certificateGlobalData` supplies the
certificate's own complete-split family.  The remaining constrained fields are canonical:
the six role permutations are enumerated above, `joint` is the exact denominator product,
and `E` is the exact rate computed from the assembled data.
-/
private noncomputable def certificateGlobalCore
    (beta : Side → Fin 6 → Shape 4 → SplitDist 4) : GlobalData 4 :=
  { A := regionDist.probR
    alpha := fun r => (shapeDist r).probR
    beta := beta
    E := 0
    perm := certificatePerm
    joint := certificateJoint }

noncomputable def certificateGlobalData
    (beta : Side → Fin 6 → Shape 4 → SplitDist 4) : GlobalData 4 :=
  { A := regionDist.probR
    alpha := fun r => (shapeDist r).probR
    beta := beta
    E := fun r => globalRegionRate (certificateGlobalCore beta) r
    perm := certificatePerm
    joint := certificateJoint }

end OmegaBound.ADVXXZCertificateGlobalData

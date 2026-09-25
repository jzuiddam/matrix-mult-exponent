import OmegaBound.ADVXXZCertSemantic
import OmegaBound.ADVXXZConGrid
import OmegaBound.ADVXXZCertificateGlobalData
import OmegaBound.ADVXXZConEps
import OmegaBound.ADVXXZAbsGrid
import OmegaBound.ADVXXZBlkChunk

/-!
# The ADVXXZ certificate as constituent-stage paper data

The semantic certificate stores, for every positive level-three parent, a six-entry region
simplex and six child-split simplexes.  `ConstituentCertificateIndexing` is the typed index
bridge identifying selected semantic simplexes with a paper `ConstituentInput` and its dependent
`ChildShape` alphabets.

The certificate does not contain a retained paired disintegration.  `certificateConstituentData`
therefore uses the canonical exact disintegration, which sends every child shape to point masses
of the required levels (`certificateBetaChild`) and sends the regional law forward along the
resulting pair of chunks (`certificateBetaRegion`).  The released probability certificate has no
natural-valued table for the corrected symmetric output weight, so `outBase` is an argument.
-/

open Finset

namespace OmegaBound.ADVXXZCertificateConstituentData

open ADVXXZ (Chunk RatDist SplitDist)
open ADVXXZPaper
open ADVXXZCertSemantic
open ADVXXZCertificateGlobalData


section CertificateData

variable {w s : ℕ} (p : ConstituentInput w s)

/-- The data-only bridge from semantic certificate indices to the paper's dependent
constituent alphabets.  Supplying an equivalence cannot create probabilities: all weights
below are still coordinates of the committed `level3Dist` objects. -/
structure ConstituentCertificateIndexing where
  regionId : Fin s → Level3DistId
  regionEquiv : (t : Fin s) → Fin 6 ≃ Level3Index (regionId t)
  childId : Fin s → Fin 6 → Level3DistId
  childEquiv : (t : Fin s) → (r : Fin 6) →
    ChildShape p t ≃ Level3Index (childId t r)

variable (idx : ConstituentCertificateIndexing p)

/-- A constituent region simplex reindexed from the committed semantic certificate. -/
def certificateRegionDist (t : Fin s) : RatDist (Fin 6) :=
  ADVXXZCertificateGlobalData.RatDist.reindex (idx.regionEquiv t)
    (level3Dist (idx.regionId t))

/-- A constituent child-shape simplex reindexed from the committed semantic certificate. -/
def certificateChildDist (t : Fin s) (r : Fin 6) : RatDist (ChildShape p t) :=
  ADVXXZCertificateGlobalData.RatDist.reindex (idx.childEquiv t r)
    (level3Dist (idx.childId t r))

/-- A fixed grid realising the three coordinates of a child shape. -/
noncomputable def certificateGrid (t : Fin s) (u : ChildShape p t) :
    Fin w → ADVXXZHash.Pat (2 * 1) :=
  Classical.choose (ADVXXZAbs.exists_grid_of_sum w (coord .X u.1) (coord .Y u.1)
    (coord .Z u.1) u.1.property)

/-- The canonical point-mass chunk on side `W` for a child shape. -/
noncomputable def certificateChunk (W : Side) (t : Fin s) (u : ChildShape p t) : Chunk w :=
  match W with
  | .X => ADVXXZCon.patX (certificateGrid p t u)
  | .Y => ADVXXZCon.patY (certificateGrid p t u)
  | .Z => ADVXXZCon.patZ (certificateGrid p t u)


/-- The paired parent chunk attached to `u`; its right half is attached to the complement. -/
noncomputable def certificatePairChunk (W : Side) (t : Fin s) (u : ChildShape p t) :
    Chunk (w + w) :=
  ADVXXZ.legApp (certificateChunk p W t u)
    (certificateChunk p W t (complement p t u))

/-- Canonical child complete-split laws, supported at the required levels. -/
noncomputable def certificateBetaChild (W : Side) (t : Fin s) (_r : Fin 6)
    (u : ChildShape p t) : SplitDist w :=
  ADVXXZCon.deltaDist (certificateChunk p W t u)

/-- Canonical regional parent law: the child simplex pushed forward to paired chunks. -/
noncomputable def certificateBetaRegion (W : Side) (t : Fin s) (r : Fin 6) :
    SplitDist (w + w) :=
  (certificateChildDist p idx t r).map (certificatePairChunk p W t)

private noncomputable def certificateConstituentCore
    (outBase : ConstituentTerm p → ℕ) : ConstituentData p :=
  { A := fun t => (certificateRegionDist p idx t).probR
    betaRegion := certificateBetaRegion p idx
    alpha := fun t r => (certificateChildDist p idx t r).probR
    betaChild := certificateBetaChild p
    E := 0
    perm := certificatePerm
    outBase := outBase }

/-- Package certificate simplexes and the canonical paired disintegration as paper data.

`outBase` is explicit because the semantic probability certificate does not provide the
corrected symmetric natural multiplicities `outBase`.
-/
noncomputable def certificateConstituentData
    (outBase : ConstituentTerm p → ℕ) : ConstituentData p :=
  { A := fun t => (certificateRegionDist p idx t).probR
    betaRegion := certificateBetaRegion p idx
    alpha := fun t r => (certificateChildDist p idx t r).probR
    betaChild := certificateBetaChild p
    E := fun r => constituentRegionRate (certificateConstituentCore p idx outBase) r
    perm := certificatePerm
    outBase := outBase }

end CertificateData

end OmegaBound.ADVXXZCertificateConstituentData

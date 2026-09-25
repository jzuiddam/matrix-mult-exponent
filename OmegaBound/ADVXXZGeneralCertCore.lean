import OmegaBound.ADVXXZPaperTheorems

/-!
# The certificate interface: global and constituent specifications

A certificate (`Certificate`, `ADVXXZGeneralCertInventory`) carries a global specification
`GlobalSpec` (the region law `A`, the shape laws `alpha`, the split laws `beta`, the role
permutations and the joint law) and, for each stage `l` (a level `2 ≤ l ≤ top`), optionally a step:
a constituent input with a constituent specification `ConstituentSpec`.
`GlobalAdmissible` collects the conditions on the global part: the roles enumerate the permutations,
the joint law is the product law, the split laws are graded (`Supported`) and boundary-compatible
under `reflect`. `ConstituentAdmissible` is the unscaled constituent condition; the proof uses its
scaled form `ConstituentAdmissibleAt` (`ADVXXZGeneralCertScaleV22`) and not this one.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

def Supported {w : ℕ} (b : SplitDist w) (i : ℕ) : Prop :=
  ∀ σ, b.num σ ≠ 0 → chunkLvl σ = i

def reflect {w : ℕ} (σ : Chunk w) : Chunk w :=
  fun j => ⟨2 - (σ j).val, by omega⟩

def BoundaryCompatible {w : ℕ} (u : Shape w)
    (b : Side → SplitDist w) : Prop :=
  ∀ (Z X Y : Side), X ≠ Y → X ≠ Z → Y ≠ Z → coord Z u = 0 →
    ∀ σ, (b X).prob σ = (b Y).prob (reflect σ)

structure GlobalSpec (w : ℕ) where
  A : RatDist (Fin 6)
  alpha : Fin 6 → RatDist (Shape w)
  beta : Side → Fin 6 → Shape w → SplitDist w
  perm : Fin 6 → Side → Side
  joint : RatDist (Fin 6 × Shape w)

structure GlobalAdmissible {w : ℕ} (g : GlobalSpec w) : Prop where
  roles : EnumeratesPermutations g.perm
  joint_eq : ∀ r u, g.joint.prob (r,u) = g.A.prob r * (g.alpha r).prob u
  support : ∀ W r u, Supported (g.beta W r u) (coord W u)
  boundary : ∀ r u, BoundaryCompatible u (fun W => g.beta W r u)

structure ConstituentSpec {w s : ℕ} (p : ConstituentInput w s) where
  A : Fin s → RatDist (Fin 6)
  alpha : (t : Fin s) → Fin 6 → RatDist (ChildShape p t)
  betaRegion : Side → Fin s → Fin 6 → SplitDist (w + w)
  betaChild : (W : Side) → (t : Fin s) → Fin 6 → ChildShape p t → SplitDist w
  perm : Fin 6 → Side → Side
  outBase : ConstituentTerm p → ℕ

structure ConstituentAdmissible {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) : Prop where
  roles : EnumeratesPermutations d.perm
  mixture : ∀ W t σ, (p.beta W t).prob σ =
    ∑ r, (d.A t).prob r * (d.betaRegion W t r).prob σ
  pair_mixture : ∀ W t r σ, (d.betaRegion W t r).prob σ =
    ∑ u, (d.alpha t r).prob u *
      (d.betaChild W t r u).prob (leftHalf σ) *
      (d.betaChild W t r (complement p t u)).prob (rightHalf σ)
  regional_support : ∀ W t r, Supported (d.betaRegion W t r)
    (match W with | .X => p.i t | .Y => p.j t | .Z => p.k t)
  child_support : ∀ W t r u, Supported (d.betaChild W t r u) (coord W u.1)
  child_boundary : ∀ t r u, BoundaryCompatible u.1 (fun W => d.betaChild W t r u)
  out_eq : ∀ t r u, (d.outBase ⟨t,r,u⟩ : ℚ) =
    p.baseN t * (d.A t).prob r *
      ((d.alpha t r).prob u + (d.alpha t r).prob (complement p t u))

end OmegaBound.ADVXXZGeneral
end

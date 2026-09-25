import OmegaBound.ADVXXZGeneralScaleAuxV22

/-!
# Certificate admissibility

`AdmissibleAt C` is the admissibility of a `Certificate` that the general theorems assume
(`certificate_bound`, statement `V17_N_Closure.1`): positive parameters, the width identity, the
global conditions `GlobalAdmissible`, the constituent conditions `ConstituentAdmissibleAt` at scale
`D ^ 2` for every stage, atomic integrality, the hash floor, and the inventory links from the top
stage down. The released instance satisfies it by `released_ordinary_physical_admissible`.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

structure ConstituentAdmissibleAt {w s : ℕ} {p : ConstituentInput w s}
    (d : ConstituentSpec p) (b : ℕ) : Prop where
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
    (b : ℚ) * p.baseN t * (d.A t).prob r *
      ((d.alpha t r).prob u + (d.alpha t r).prob (complement p t u))

structure AdmissibleAt (C : Certificate) : Prop where
  q_pos : 0 < C.q
  top_pos : 0 < C.top
  width_eq : C.width = wid C.top
  kappa_pos : 0 < C.kappa
  D_pos : 0 < C.D
  global_ok : GlobalAdmissible C.global
  stage_ok : ∀ l d, C.stage l = some d → ConstituentAdmissibleAt d.data (C.D ^ 2)
  lattice : AtomicIntegralAt C
  hash_floor : 2 * C.width < C.modulus.floor
  top_link : ∀ l : Stage C.top, l.val = C.top →
    InventoryEq (interior (G C)) (P C l)
  next_link : ∀ l h : Stage C.top, l.val + 1 = h.val →
    InventoryEq (interior (QAt C h)) (P C l)

end OmegaBound.ADVXXZGeneral
end

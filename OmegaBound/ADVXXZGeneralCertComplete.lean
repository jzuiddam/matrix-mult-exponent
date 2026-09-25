import OmegaBound.ADVXXZGeneralCertInventory
import OmegaBound.ADVXXZBlkChunk

/-!
# Exact grids, and the unscaled admissibility predicate

`ExactGrid g n` is an integral grid of counts for the global specification `g` at size `n`, graded
by level; `outerN` is the outer scale `D ^ 4 * m`. `Admissible` is the unscaled variant of
`AdmissibleAt` (`ADVXXZGeneralCertScaleV22`); the final theorems do not use it.
-/

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral

structure ExactGrid {w : ℕ} (g : GlobalSpec w) (n : ℕ) where
  count : Side → Fin 6 → Shape w → Chunk w → ℕ
  total : ∀ W r u, ∑ σ, count W r u σ = (n*g.joint.prob (r,u)).floor.toNat
  graded : ∀ W r u σ, chunkLvl σ ≠ coord W u → count W r u σ = 0

structure Admissible (C : Certificate) : Prop where
  q_pos : 0 < C.q
  top_pos : 0 < C.top
  width_eq : C.width = wid C.top
  kappa_pos : 0 < C.kappa
  D_pos : 0 < C.D
  global_ok : GlobalAdmissible C.global
  stage_ok : ∀ l d, C.stage l = some d → ConstituentAdmissible d.data
  lattice : AtomicIntegral C
  hash_floor : 2 * C.width < C.modulus.floor
  top_link : ∀ l : Stage C.top, l.val = C.top →
    InventoryEq (interior (G C)) (P C l)
  next_link : ∀ l h : Stage C.top, l.val + 1 = h.val →
    InventoryEq (interior (Q C h)) (P C l)

def outerN (C : Certificate) (m : ℕ) : ℕ := C.D^4*m

end OmegaBound.ADVXXZGeneral
end

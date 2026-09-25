import OmegaBound.ADVXXZPaperTheorems
import OmegaBound.ADVXXZHoles

section
universe u
open OmegaBound Tensor3
open OmegaBound.ADVXXZ OmegaBound.ADVXXZPaper
open OmegaBound.CW90 OmegaBound.ADVXXZHoles
open scoped BigOperators
namespace OmegaBound.ADVXXZGeneral
variable {R : Type*} [CommSemiring R]
variable {X Y Z PX PY PZ ι ξ : Type*}
  [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [Fintype PX] [Fintype PY] [Fintype PZ] [DecidableEq PX] [DecidableEq PY] [DecidableEq PZ]
  [Fintype ι] [DecidableEq ι] [DecidableEq ξ] [Nonempty PX] [Nonempty PY] [Nonempty PZ]

theorem fix_holes_general (T : Tensor3 R X Y Z)
    (pX : X → PX) (pY : Y → PY) (pZ : Z → PZ)
    (S : Shuffles pX pY pZ T ξ) (D : ℕ) (hD : 2 ≤ D)
    (HX : ι → Finset PX) (HY : ι → Finset PY) (HZ : ι → Finset PZ)
    (hX : ∀ i, 4*D*(HX i).card ≤ Fintype.card PX)
    (hY : ∀ i, 4*D*(HY i).card ≤ Fintype.card PY)
    (hZ : ∀ i, 4*D*(HZ i).card ≤ Fintype.card PZ)
    (I : Finset ι)
    (hI : 4^(Nat.log D (Fintype.card PX) + Nat.log D (Fintype.card PY) +
      Nat.log D (Fintype.card PZ) + 1) ≤ I.card) :
  Restricts T (famDS I (fun i => boxZO pX pY pZ (HX i)ᶜ (HY i)ᶜ (HZ i)ᶜ T)) := by
  exact holes_restrict_univ S D hD HX HY HZ hX hY hZ I hI

end OmegaBound.ADVXXZGeneral
end
